import QuantCert.Semantics

namespace QuantCert.Examples

def int8 : QType := ⟨8, by decide, (1 : Rat) / 128, by decide +kernel, true⟩
def accumulator : QType := ⟨32, by decide, (1 : Rat) / 16384, by decide +kernel, true⟩
def output8 : QType := ⟨8, by decide, (1 : Rat) / 32, by decide +kernel, true⟩

abbrev Pair8 := WireType.word int8 ⊗ WireType.word int8

/-- A nonempty row of `n + 1` (activation, weight) pairs. -/
def rowType : Nat → WireType
  | 0 => Pair8
  | n + 1 => Pair8 ⊗ rowType n

def qMul : Circuit Pair8 (.word accumulator) :=
  .prim (.mul int8 int8 accumulator (by decide +kernel))

/-- A parameterized one-row quantized matrix multiply, accumulated at INT32.
The range certificate must be checked for the chosen row length. -/
def qMatMul : (n : Nat) → Circuit (rowType n) (.word accumulator)
  | 0 => qMul
  | n + 1 => (qMul *** qMatMul n) >>> Circuit.prim (.add accumulator)

def hwRequantize : Circuit (.word accumulator) (.word output8) :=
  .prim (.requant accumulator output8 ⟨1, 9, 0, by decide +kernel⟩)

def qReLU : Circuit (.word output8) (.word output8) := .prim (.relu output8)

/-- Two variable INT8 products, exact INT32 accumulation, scale by 1/512, then ReLU. -/
def quantizedLayer : Circuit (rowType 1) (.word output8) :=
  qMatMul 1 >>> hwRequantize >>> qReLU

theorem layer_accumulator_safe (xs : List (Int × Int)) (hlen : xs.length = 2)
    (h : Int8Pairs xs) :
    -2147483648 ≤ dotProduct xs ∧ dotProduct xs < 2147483648 := by
  exact dotProduct_no_overflow xs 2 32 hlen (by decide) h (by decide)

/-- This scale is exact: delta=0, so only rounding error remains. -/
theorem layer_requantization_error (acc : Int) :
    (hwRequantizeInt acc 1 9 * 512 - acc).natAbs ≤ 512 := by
  simpa using hwRequantize_approx_cleared acc 1 1 512 0 9 (by decide) (by simp)

theorem int8_range (x : BitVec 8) : -128 ≤ x.toInt ∧ x.toInt ≤ 127 := by
  have hlo := BitVec.le_toInt x
  have hhi := BitVec.toInt_lt (x := x)
  simp only [Nat.reduceSub, Int.reducePow] at hlo hhi
  omega

theorem mul_register_exact (x y : BitVec 8) :
    (BitVec.ofInt 32 (x.toInt * y.toInt)).toInt = x.toInt * y.toInt := by
  have h : Int8Pairs [(x.toInt, y.toInt)] := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact ⟨(int8_range x).1, (int8_range x).2, (int8_range y).1, (int8_range y).2⟩
  simpa [dotProduct] using
    dotProduct_register_exact [(x.toInt, y.toInt)] 1 32 (by rfl) (by decide) h (by decide)

theorem layer_pairs_bounded (x y z t : BitVec 8) :
    Int8Pairs [(x.toInt, y.toInt), (z.toInt, t.toInt)] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨(int8_range x).1, (int8_range x).2, (int8_range y).1, (int8_range y).2⟩
  · exact ⟨(int8_range z).1, (int8_range z).2, (int8_range t).1, (int8_range t).2⟩

/-- The example's actual bit-vector MAC, not just its mathematical model, cannot wrap. -/
theorem qMatMul_exact (x y z t : BitVec 8) :
    (evalCircuit (qMatMul 1) ((x, y), (z, t))).toInt =
      x.toInt * y.toInt + z.toInt * t.toInt := by
  change (BitVec.ofInt 32
    ((BitVec.ofInt 32 (x.toInt * y.toInt)).toInt +
      (BitVec.ofInt 32 (z.toInt * t.toInt)).toInt)).toInt = _
  rw [mul_register_exact, mul_register_exact]
  simpa [dotProduct] using dotProduct_register_exact
    [(x.toInt, y.toInt), (z.toInt, t.toInt)] 2 32 (by rfl) (by decide)
    (layer_pairs_bounded x y z t) (by decide)

/-- Requantization of every possible example input fits INT8 before ReLU. -/
theorem layer_narrowing_safe (x y z t : BitVec 8) :
    -128 ≤ hwRequantizeInt (x.toInt * y.toInt + z.toInt * t.toInt) 1 9 ∧
      hwRequantizeInt (x.toInt * y.toInt + z.toInt * t.toInt) 1 9 < 128 := by
  have hb := dotProduct_abs_bound
    [(x.toInt, y.toInt), (z.toInt, t.toInt)] (layer_pairs_bounded x y z t)
  simp [dotProduct] at hb
  simp only [hwRequantizeInt, Int.mul_one, Nat.reducePow]
  omega

/-- End-to-end signed integer formula, with both accumulation and narrowing verified. -/
theorem layer_exact (x y z t : BitVec 8) :
    (evalCircuit quantizedLayer ((x, y), (z, t))).toInt =
      max 0 (hwRequantizeInt (x.toInt * y.toInt + z.toInt * t.toInt) 1 9) := by
  have hr := layer_narrowing_safe x y z t
  change (BitVec.ofInt 8 (max 0
    (BitVec.ofInt 8 (hwRequantizeInt
      (evalCircuit (qMatMul 1) ((x, y), (z, t))).toInt 1 9)).toInt)).toInt = _
  have stored : (BitVec.ofInt 8
      (hwRequantizeInt (x.toInt * y.toInt + z.toInt * t.toInt) 1 9)).toInt =
      hwRequantizeInt (x.toInt * y.toInt + z.toInt * t.toInt) 1 9 :=
    BitVec.toInt_ofInt_eq_self (by decide) hr.1 hr.2
  rw [qMatMul_exact, stored]
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · omega
  · omega

/-- A gate-level fanout example; duplication is wiring, not a hidden gate. -/
def gateDemo : Circuit (.word bitQ ⊗ .word bitQ) (.word bitQ ⊗ .word bitQ) :=
  Circuit.prim Prim.nand &&& Circuit.fst

end QuantCert.Examples

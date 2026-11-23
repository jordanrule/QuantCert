import Std

namespace QuantCert

/-- Positive rational scale and nonempty storage; signed by default. -/
structure QuantParams where
  bitWidth : Nat
  width_pos : 0 < bitWidth
  scale : Rat
  scale_pos : 0 < scale
  signed : Bool := true

abbrev QType := QuantParams

/-- Round to nearest, with ties toward positive infinity; storage wraps, not saturates. -/
def quantize (q : QType) (x : Rat) : BitVec q.bitWidth :=
  BitVec.ofInt q.bitWidth ((x / q.scale + (1 : Rat) / 2).floor)

def dequantize (q : QType) (x : BitVec q.bitWidth) : Rat :=
  ((if q.signed then x.toInt else (x.toNat : Int)) : Rat) * q.scale

/-- Exact, unbounded dot product used by the range certificate. -/
def dotProduct : List (Int × Int) → Int
  | [] => 0
  | (x, y) :: xs => x * y + dotProduct xs

def Int8Pairs (xs : List (Int × Int)) : Prop :=
  ∀ p ∈ xs, -128 ≤ p.1 ∧ p.1 ≤ 127 ∧ -128 ≤ p.2 ∧ p.2 ≤ 127

theorem dotProduct_abs_bound (xs : List (Int × Int)) (h : Int8Pairs xs) :
    (dotProduct xs).natAbs ≤ xs.length * 16384 := by
  induction xs with
  | nil => simp [dotProduct]
  | cons p xs ih =>
    have hp := h p (by simp)
    have hx : p.1.natAbs ≤ 128 := by omega
    have hy : p.2.natAbs ≤ 128 := by omega
    have hm : (p.1 * p.2).natAbs ≤ 16384 := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul hx hy
    have ht := ih (fun a ha => h a (by simp [ha]))
    have hs := Int.natAbs_add_le (p.1 * p.2) (dotProduct xs)
    simp only [dotProduct, List.length_cons]
    omega

/-- Every exact partial sum also satisfies this certificate by applying it to a prefix. -/
theorem dotProduct_no_overflow (xs : List (Int × Int)) (K W : Nat)
    (hlen : xs.length = K) (_hW : 0 < W) (h : Int8Pairs xs)
    (capacity : K * 16384 < 2 ^ (W - 1)) :
    -((2 ^ (W - 1) : Nat) : Int) ≤ dotProduct xs ∧
      dotProduct xs < ((2 ^ (W - 1) : Nat) : Int) := by
  have hb := dotProduct_abs_bound xs h
  omega

/-- Arithmetic right shift of an unbounded signed product, with half-up rounding. -/
def hwRequantizeInt (acc M : Int) (shift : Nat) : Int :=
  (acc * M + (2 ^ shift : Nat) / 2) / (2 ^ shift : Nat)

/-- Denominator-cleared rational error:
`|result - acc * (num/den)| ≤ |acc| * (delta/den) + 1`.
The scale approximation hypothesis is exactly
`|M/2^shift - num/den| ≤ delta/den`. No floating-point arithmetic is involved. -/
theorem hwRequantize_approx_cleared (acc M num : Int) (den delta shift : Nat)
    (hden : 0 < den)
    (hscale : (M * (den : Int) - num * (2 ^ shift : Nat)).natAbs ≤
      delta * 2 ^ shift) :
    (hwRequantizeInt acc M shift * (den : Int) - acc * num).natAbs ≤
      acc.natAbs * delta + den := by
  let D := 2 ^ shift
  have hD : 0 < D := Nat.two_pow_pos shift
  have hd : 0 < (D : Int) := by omega
  have hr0 := Int.emod_nonneg (acc * M + (D / 2 : Nat)) (by omega : (D : Int) ≠ 0)
  have hr1 := Int.emod_lt_of_pos (acc * M + (D / 2 : Nat)) hd
  have he := Int.mul_ediv_add_emod (acc * M + (D / 2 : Nat)) (D : Int)
  rw [Int.mul_comm (D : Int)] at he
  have hh : D / 2 ≤ D := Nat.div_le_self D 2
  have hround : (hwRequantizeInt acc M shift * (D : Int) - acc * M).natAbs ≤ D := by
    unfold hwRequantizeInt
    change (((acc * M + (D / 2 : Nat)) / (D : Int)) * (D : Int) - acc * M).natAbs ≤ D
    omega
  have htriangle := Int.natAbs_add_le
    ((hwRequantizeInt acc M shift * (D : Int) - acc * M) * (den : Int))
    (acc * (M * (den : Int) - num * (D : Int)))
  have halgebra :
      (hwRequantizeInt acc M shift * (D : Int) - acc * M) * (den : Int) +
        acc * (M * (den : Int) - num * (D : Int)) =
      (hwRequantizeInt acc M shift * (den : Int) - acc * num) * (D : Int) := by
    grind
  rw [halgebra, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul] at htriangle
  have h1 := Nat.mul_le_mul_right den hround
  have h2 := Nat.mul_le_mul_left acc.natAbs hscale
  simp only [Int.natAbs_natCast] at htriangle
  have bound :
      (hwRequantizeInt acc M shift * (den : Int) - acc * num).natAbs * D ≤
        (acc.natAbs * delta + den) * D := by
    dsimp [D] at *
    grind
  exact Nat.le_of_mul_le_mul_right bound hD

/-- Absolute value on standard-library rationals, with no real-number dependency. -/
def ratAbs (x : Rat) : Rat := if x < 0 then -x else x

theorem ratAbs_int_div (x : Int) (d : Nat) (hd : 0 < d) :
    ratAbs ((x : Rat) / (d : Rat)) = (x.natAbs : Rat) / (d : Rat) := by
  have hp : 0 < (d : Rat) := Rat.natCast_lt_natCast.mpr hd
  have hc : (x : Rat) / (d : Rat) < 0 ↔ x < 0 := by
    rw [Rat.div_lt_iff hp]
    simpa using (Rat.intCast_lt_intCast (a := x) (b := 0))
  unfold ratAbs
  simp only [hc]
  split
  · rename_i hx
    have ha : (x.natAbs : Int) = -x := by omega
    have cast : (x.natAbs : Rat) = -(x : Rat) := by
      rw [← Rat.intCast_natCast, ha, Rat.intCast_neg]
    rw [cast]
    simp only [Rat.div_def, Rat.neg_mul]
  · rename_i hx
    have ha : (x.natAbs : Int) = x := by omega
    have cast : (x.natAbs : Rat) = (x : Rat) := by
      simpa only [Rat.intCast_natCast] using congrArg (fun z : Int => (z : Rat)) ha
    rw [cast]

/-- An overflow certificate is also a bit-vector register round-trip theorem. -/
theorem dotProduct_register_exact (xs : List (Int × Int)) (K W : Nat)
    (hlen : xs.length = K) (hW : 0 < W) (h : Int8Pairs xs)
    (capacity : K * 16384 < 2 ^ (W - 1)) :
    (BitVec.ofInt W (dotProduct xs)).toInt = dotProduct xs := by
  have hr := dotProduct_no_overflow xs K W hlen hW h capacity
  apply BitVec.toInt_ofInt_eq_self hW
  · simpa only [Int.natCast_pow] using hr.1
  · simpa only [Int.natCast_pow] using hr.2

/-- Rational form of the multiply-and-shift error certificate.
Here `realScale = num/den` and `δ = delta/den`; the hypothesis is the
denominator-cleared, exact comparison of `M/2^shift` with `realScale`. -/
theorem hwRequantize_approx (acc M num : Int) (den delta shift : Nat)
    (hden : 0 < den)
    (hscale : (M * (den : Int) - num * (2 ^ shift : Nat)).natAbs ≤
      delta * 2 ^ shift) :
    ratAbs ((hwRequantizeInt acc M shift : Rat) - (acc : Rat) * ((num : Rat) / den)) ≤
      (acc.natAbs : Rat) * ((delta : Rat) / den) + 1 := by
  have hp : 0 < (den : Rat) := Rat.natCast_lt_natCast.mpr hden
  have hn : (den : Rat) ≠ 0 := Rat.ne_of_gt hp
  have hc := Rat.div_mul_cancel (a := (num : Rat)) hn
  have he :
      (hwRequantizeInt acc M shift : Rat) - (acc : Rat) * ((num : Rat) / den) =
      ((hwRequantizeInt acc M shift * (den : Int) - acc * num : Int) : Rat) / den := by
    apply Rat.le_antisymm
    all_goals
      apply Rat.le_of_mul_le_mul_right (hc := hp)
      rw [Rat.div_mul_cancel hn]
      simp only [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_natCast]
      have eq : ((hwRequantizeInt acc M shift : Rat) -
          (acc : Rat) * ((num : Rat) / den)) * den =
          (hwRequantizeInt acc M shift : Rat) * den - (acc : Rat) * num := by grind
      rw [eq]
      exact Rat.le_refl
  rw [he, ratAbs_int_div _ den hden]
  apply Rat.le_of_mul_le_mul_right (hc := hp)
  rw [Rat.div_mul_cancel hn]
  have hr : ((acc.natAbs : Rat) * ((delta : Rat) / den) + 1) * den =
      ((acc.natAbs * delta + den : Nat) : Rat) := by
    have hd := Rat.div_mul_cancel (a := (delta : Rat)) hn
    simp only [Rat.natCast_add, Rat.natCast_mul]
    grind
  rw [hr]
  exact Rat.natCast_le_natCast.mpr
    (hwRequantize_approx_cleared acc M num den delta shift hden hscale)

/-- Multiplier/shift configuration carrying an exact metadata scale-error receipt.
The rational error tolerance is `delta / (a.scale / b.scale).den`. -/
structure RequantParams (a b : QType) where
  multiplier : Int
  shift : Nat
  delta : Nat
  scale_ok :
    (multiplier * ((a.scale / b.scale).den : Int) -
      (a.scale / b.scale).num * (2 ^ shift : Nat)).natAbs ≤ delta * 2 ^ shift

theorem requantParams_approx (a b : QType) (r : RequantParams a b) (acc : Int) :
    ratAbs ((hwRequantizeInt acc r.multiplier r.shift : Rat) -
      (acc : Rat) * (a.scale / b.scale)) ≤
      (acc.natAbs : Rat) * ((r.delta : Rat) / (a.scale / b.scale).den) + 1 := by
  have h := hwRequantize_approx acc r.multiplier (a.scale / b.scale).num
    (a.scale / b.scale).den r.delta r.shift (a.scale / b.scale).den_pos r.scale_ok
  have hs : ((a.scale / b.scale).num : Rat) / (a.scale / b.scale).den =
      a.scale / b.scale := by
    simpa only [Rat.divInt_eq_div, Rat.intCast_natCast] using
      Rat.num_divInt_den (a.scale / b.scale)
  rwa [hs] at h

/-- The same error bound applies to stored hardware outputs when narrowing cannot wrap. -/
theorem requantParams_stored_approx (a b : QType) (r : RequantParams a b)
    (x : BitVec a.bitWidth)
    (lo : -2 ^ (b.bitWidth - 1) ≤ hwRequantizeInt x.toInt r.multiplier r.shift)
    (hi : hwRequantizeInt x.toInt r.multiplier r.shift < 2 ^ (b.bitWidth - 1)) :
    ratAbs (((BitVec.ofInt b.bitWidth
      (hwRequantizeInt x.toInt r.multiplier r.shift)).toInt : Rat) -
      (x.toInt : Rat) * (a.scale / b.scale)) ≤
      (x.toInt.natAbs : Rat) * ((r.delta : Rat) / (a.scale / b.scale).den) + 1 := by
  rw [BitVec.toInt_ofInt_eq_self b.width_pos lo hi]
  exact requantParams_approx a b r x.toInt

end QuantCert

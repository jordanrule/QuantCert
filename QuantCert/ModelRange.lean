import QuantCert.Model

namespace QuantCert.Model

/-- Inclusive integer bounds. Membership is the assumption, not calibration data. -/
structure IntRange where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

def IntRange.Contains (r : IntRange) (x : Int) : Prop := r.lo ≤ x ∧ x ≤ r.hi
def IntRange.point (x : Int) : IntRange := ⟨x, x⟩
def IntRange.add (r s : IntRange) : IntRange := ⟨r.lo + s.lo, r.hi + s.hi⟩
def IntRange.scale (r : IntRange) (k : Int) : IntRange :=
  ⟨min (k * r.lo) (k * r.hi), max (k * r.lo) (k * r.hi)⟩
def IntRange.shift (r : IntRange) (s : Nat) : IntRange :=
  ⟨r.lo / (2 ^ s : Nat), r.hi / (2 ^ s : Nat)⟩
def IntRange.activate (r : IntRange) (a : Activation) : IntRange :=
  ⟨a.integer r.lo, a.integer r.hi⟩
def IntRange.saturate (r : IntRange) (f : Format) : IntRange :=
  ⟨clamp f.lo f.hi r.lo, clamp f.lo f.hi r.hi⟩
def IntRange.magnitude (r : IntRange) : Nat := max r.lo.natAbs r.hi.natAbs
def IntRange.fits (r : IntRange) (bits : Nat) : Prop :=
  storageLo true bits ≤ r.lo ∧ r.hi ≤ storageHi true bits

instance (r : IntRange) (x : Int) : Decidable (r.Contains x) := inferInstanceAs (Decidable (_ ∧ _))
instance (r : IntRange) (bits : Nat) : Decidable (r.fits bits) := inferInstanceAs (Decidable (_ ∧ _))

theorem IntRange.point_sound (x : Int) : (point x).Contains x := ⟨Int.le_refl _, Int.le_refl _⟩

theorem IntRange.add_sound (r s : IntRange) (hx : r.Contains x) (hy : s.Contains y) :
    (r.add s).Contains (x + y) := by
  simp only [Contains, add] at *
  omega

theorem IntRange.scale_sound (r : IntRange) (k : Int) (h : r.Contains x) :
    (r.scale k).Contains (k * x) := by
  rcases h with ⟨hl, hh⟩
  by_cases hk : 0 ≤ k
  · have := Int.mul_le_mul_of_nonneg_left hl hk
    have := Int.mul_le_mul_of_nonneg_left hh hk
    simp only [Contains, scale]
    omega
  · have hlo := Int.mul_le_mul_of_nonneg_left hl (by omega : 0 ≤ -k)
    have hhi := Int.mul_le_mul_of_nonneg_left hh (by omega : 0 ≤ -k)
    simp only [Int.neg_mul] at hlo hhi
    simp only [Contains, scale]
    omega

theorem IntRange.shift_sound (r : IntRange) (s : Nat) (h : r.Contains x) :
    (r.shift s).Contains (x / (2 ^ s : Nat)) := by
  have hp := Nat.two_pow_pos s
  have hd : (0 : Int) < (2 ^ s : Nat) := by omega
  exact ⟨Int.ediv_le_ediv hd h.1, Int.ediv_le_ediv hd h.2⟩

theorem IntRange.activate_sound (r : IntRange) (a : Activation) (h : r.Contains x) :
    (r.activate a).Contains (a.integer x) := by
  cases a <;> simp only [activate, Activation.integer, Contains] at * <;> omega

theorem IntRange.saturate_sound (r : IntRange) (f : Format) (h : r.Contains x) :
    (r.saturate f).Contains (clamp f.lo f.hi x) := by
  simp only [saturate, Contains, clamp] at *
  omega

theorem IntRange.magnitude_sound (r : IntRange) (h : r.Contains x) :
    x.natAbs ≤ r.magnitude := by
  simp only [Contains, magnitude] at *
  omega

theorem IntRange.storage_exact (r : IntRange) (h : r.Contains x)
    (bits : Nat) (hb : 0 < bits) (hs : r.fits bits) :
    (BitVec.ofInt bits x).toInt = x := by
  apply BitVec.toInt_ofInt_eq_self hb
  · have hlo : -((2 ^ (bits - 1) : Nat) : Int) ≤ x := Int.le_trans hs.1 h.1
    simpa only [Int.natCast_pow] using hlo
  · have hhi : x < ((2 ^ (bits - 1) : Nat) : Int) := by
      have hh := Int.le_trans h.2 hs.2
      simp only [storageHi, ↓reduceIte] at hh
      omega
    simpa only [Int.natCast_pow] using hhi

def rangeSum : (n : Nat) → (Fin n → IntRange) → IntRange
  | 0, _ => .point 0
  | n + 1, f => (f 0).add (rangeSum n (fun i => f i.succ))

theorem rangeSum_sound (n : Nat) (r : Fin n → IntRange) (x : Fin n → Int)
    (h : ∀ i, (r i).Contains (x i)) : (rangeSum n r).Contains (intSum n x) := by
  induction n with
  | zero => exact IntRange.point_sound 0
  | succ n ih =>
    exact IntRange.add_sound _ _ (h 0)
      (ih (fun i => r i.succ) (fun i => x i.succ) (fun i => h i.succ))

def signedStore (bits : Nat) (x : Int) : Int := (BitVec.ofInt bits x).toInt

def Format.store (f : Format) (x : Int) : Int :=
  if f.signed then (BitVec.ofInt f.bits x).toInt else (BitVec.ofInt f.bits x).toNat

theorem Format.storage_exact (f : Format) (x : Int) (h : f.valid x) : f.store x = x := by
  unfold store
  split
  · rename_i hs
    apply BitVec.toInt_ofInt_eq_self f.bits_pos
    · have hl : -((2 ^ (f.bits - 1) : Nat) : Int) ≤ x := by
        have := h.1
        simpa [lo, storageLo, hs] using this
      simpa only [Int.natCast_pow] using hl
    · have hh : x < ((2 ^ (f.bits - 1) : Nat) : Int) := by
        have := h.2
        simp only [hi, storageHi, hs, ↓reduceIte] at this
        omega
      simpa only [Int.natCast_pow] using hh
  · rename_i hs
    have hf : f.signed = false := by cases hf : f.signed <;> simp_all
    have hl : 0 ≤ x := by simpa [lo, storageLo, hf] using h.1
    have hh : x < (2 ^ f.bits : Nat) := by
      have hu : x < (2 : Int) ^ f.bits := by
        have := h.2
        simp [hi, storageHi, hf] at this
        omega
      simpa only [Int.natCast_pow] using hu
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hl hh]
    omega

/-- Every suffix of the explicitly right-associated dot product must fit. -/
def sumsFit : (n : Nat) → (Fin n → IntRange) → Nat → Prop
  | 0, _, bits => (IntRange.point 0).fits bits
  | n + 1, r, bits => (rangeSum (n + 1) r).fits bits ∧
      sumsFit n (fun i => r i.succ) bits

instance (n : Nat) (r : Fin n → IntRange) (bits : Nat) : Decidable (sumsFit n r bits) := by
  induction n with
  | zero => exact inferInstanceAs (Decidable ((IntRange.point 0).fits bits))
  | succ n ih =>
    exact @instDecidableAnd _ _ inferInstance (ih (fun i => r i.succ))

def storedSum (bits : Nat) : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => signedStore bits 0
  | n + 1, f => signedStore bits (f 0 + storedSum bits n (fun i => f i.succ))

theorem storedSum_exact (bits : Nat) (hb : 0 < bits) (n : Nat)
    (r : Fin n → IntRange) (x : Fin n → Int) (hx : ∀ i, (r i).Contains (x i))
    (hs : sumsFit n r bits) : storedSum bits n x = intSum n x := by
  induction n with
  | zero => exact IntRange.storage_exact _ (IntRange.point_sound _) bits hb hs
  | succ n ih =>
    simp only [storedSum, intSum]
    rw [ih (fun i => r i.succ) (fun i => x i.succ) (fun i => hx i.succ) hs.2]
    exact IntRange.storage_exact _ (rangeSum_sound (n + 1) r x hx) bits hb hs.1

def QuantLayer.inputRange (_l : QuantLayer n m a b) : IntRange := ⟨a.lo, a.hi⟩

def QuantLayer.centeredRange (_l : QuantLayer n m a b) (r : IntRange) : IntRange :=
  r.add (.point (-a.zeroPoint))

def QuantLayer.productRange (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) (i : Fin n) : IntRange :=
  (l.centeredRange (r i)).scale (l.weight j i - (l.weightFormat j).zeroPoint)

def QuantLayer.accRange (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) : IntRange :=
  (IntRange.point (l.bias j)).add (rangeSum n (l.productRange r j))

def QuantLayer.mulRange (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) : IntRange :=
  (l.accRange r j).scale (l.multiplier j)

def QuantLayer.tempRange (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) : IntRange :=
  (l.mulRange r j).add (.point ((2 ^ l.shift j : Nat) / 2))

def QuantLayer.roundRange (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) : IntRange := (l.tempRange r j).shift (l.shift j)

def QuantLayer.preClampRange (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) : IntRange :=
  ((l.roundRange r j).activate l.reference.activation).add (.point b.zeroPoint)

def QuantLayer.outputRange (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) : IntRange := (l.preClampRange r j).saturate b

theorem QuantLayer.productRange_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (x : Fin n → Int) (h : ∀ i, (r i).Contains (x i)) (j : Fin m) (i : Fin n) :
    (l.productRange r j i).Contains (l.product x j i) := by
  have hc := IntRange.add_sound _ _ (h i) (IntRange.point_sound (-a.zeroPoint))
  have hp := IntRange.scale_sound _ (l.weight j i - (l.weightFormat j).zeroPoint) hc
  simpa [productRange, centeredRange, product, Int.sub_eq_add_neg, Int.mul_comm] using hp

theorem QuantLayer.accRange_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (x : Fin n → Int) (h : ∀ i, (r i).Contains (x i)) (j : Fin m) :
    (l.accRange r j).Contains (l.acc x j) :=
  IntRange.add_sound _ _ (IntRange.point_sound _)
    (rangeSum_sound n _ _ (l.productRange_sound r x h j))

theorem QuantLayer.roundRange_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (x : Fin n → Int) (h : ∀ i, (r i).Contains (x i)) (j : Fin m) :
    (l.roundRange r j).Contains (l.rounded x j) := by
  have hm := IntRange.scale_sound _ (l.multiplier j) (l.accRange_sound r x h j)
  rw [Int.mul_comm] at hm
  exact IntRange.shift_sound _ _ (IntRange.add_sound _ _ hm (IntRange.point_sound _))

theorem QuantLayer.preClampRange_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (x : Fin n → Int) (h : ∀ i, (r i).Contains (x i)) (j : Fin m) :
    (l.preClampRange r j).Contains
      (l.reference.activation.integer (l.rounded x j) + b.zeroPoint) :=
  IntRange.add_sound _ _ (IntRange.activate_sound _ _ (l.roundRange_sound r x h j))
    (IntRange.point_sound _)

theorem QuantLayer.outputRange_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (x : Fin n → Int) (h : ∀ i, (r i).Contains (x i)) (j : Fin m) :
    (l.outputRange r j).Contains (l.eval x j) :=
  IntRange.saturate_sound _ _ (l.preClampRange_sound r x h j)

/-- An executable, conservative check; rejection means not certified, not a bug witness.
Centered subtractions are widened to accumulatorBits before multiplication. -/
def QuantLayer.Safe (l : QuantLayer n m a b) (r : Fin n → IntRange) : Prop :=
  (∀ i, a.lo ≤ (r i).lo ∧ (r i).lo ≤ (r i).hi ∧ (r i).hi ≤ a.hi) ∧
  ∀ j,
    (∀ i, (l.centeredRange (r i)).fits l.accumulatorBits ∧
      (IntRange.point (l.weight j i - (l.weightFormat j).zeroPoint)).fits l.accumulatorBits ∧
      (l.productRange r j i).fits l.accumulatorBits) ∧
    (IntRange.point (l.bias j)).fits l.accumulatorBits ∧
    sumsFit n (l.productRange r j) l.accumulatorBits ∧
    (l.accRange r j).fits l.accumulatorBits ∧
    (IntRange.point (l.multiplier j)).fits l.temporaryBits ∧
    (l.mulRange r j).fits l.temporaryBits ∧
    (IntRange.point ((2 ^ l.shift j : Nat) / 2)).fits l.temporaryBits ∧
    (l.tempRange r j).fits l.temporaryBits ∧
    (l.roundRange r j).fits l.temporaryBits ∧
    (l.preClampRange r j).fits l.temporaryBits

instance (l : QuantLayer n m a b) (r : Fin n → IntRange) : Decidable (l.Safe r) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem QuantLayer.accumulator_exact (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (hs : l.Safe r) (x : Fin n → Int) (hx : ∀ i, (r i).Contains (x i)) (j : Fin m) :
    (BitVec.ofInt l.accumulatorBits (l.acc x j)).toInt = l.acc x j :=
  IntRange.storage_exact _ (l.accRange_sound r x hx j) _ l.accumulatorBits_pos
    (hs.2 j).2.2.2.1

def QuantLayer.machineProduct (l : QuantLayer n m a b) (x : Fin n → Int)
    (j : Fin m) (i : Fin n) : Int :=
  signedStore l.accumulatorBits
    (signedStore l.accumulatorBits (x i - a.zeroPoint) *
      signedStore l.accumulatorBits (l.weight j i - (l.weightFormat j).zeroPoint))

def QuantLayer.machineAcc (l : QuantLayer n m a b) (x : Fin n → Int) (j : Fin m) : Int :=
  signedStore l.accumulatorBits
    (signedStore l.accumulatorBits (l.bias j) + storedSum l.accumulatorBits n (l.machineProduct x j))

def QuantLayer.machineRounded (l : QuantLayer n m a b) (x : Fin n → Int) (j : Fin m) : Int :=
  signedStore l.temporaryBits
    (signedStore l.temporaryBits
      (signedStore l.temporaryBits
        (l.machineAcc x j * signedStore l.temporaryBits (l.multiplier j)) +
          signedStore l.temporaryBits ((2 ^ l.shift j : Nat) / 2)) /
      (2 ^ l.shift j : Nat))

def QuantLayer.machineEval (l : QuantLayer n m a b) (x : Fin n → Int) : Fin m → Int :=
  fun j => b.store (clamp b.lo b.hi (signedStore l.temporaryBits
    (l.reference.activation.integer (l.machineRounded x j) + b.zeroPoint)))

theorem QuantLayer.machineProduct_exact (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (hs : l.Safe r) (x : Fin n → Int) (hx : ∀ i, (r i).Contains (x i))
    (j : Fin m) (i : Fin n) : l.machineProduct x j i = l.product x j i := by
  have hc : (l.centeredRange (r i)).Contains (x i - a.zeroPoint) := by
    simpa [centeredRange, Int.sub_eq_add_neg] using
      IntRange.add_sound _ _ (hx i) (IntRange.point_sound (-a.zeroPoint))
  have h₁ := IntRange.storage_exact _ hc _ l.accumulatorBits_pos ((hs.2 j).1 i).1
  have h₂ := IntRange.storage_exact _
    (IntRange.point_sound (l.weight j i - (l.weightFormat j).zeroPoint))
    _ l.accumulatorBits_pos ((hs.2 j).1 i).2.1
  unfold machineProduct signedStore
  rw [h₁, h₂]
  exact IntRange.storage_exact _ (l.productRange_sound r x hx j i)
    _ l.accumulatorBits_pos ((hs.2 j).1 i).2.2

theorem QuantLayer.machineAcc_exact (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (hs : l.Safe r) (x : Fin n → Int) (hx : ∀ i, (r i).Contains (x i)) (j : Fin m) :
    l.machineAcc x j = l.acc x j := by
  have hp : l.machineProduct x j = l.product x j :=
    funext (l.machineProduct_exact r hs x hx j)
  have hb := IntRange.storage_exact _ (IntRange.point_sound (l.bias j))
    _ l.accumulatorBits_pos (hs.2 j).2.1
  unfold machineAcc
  rw [hp, storedSum_exact _ l.accumulatorBits_pos n (l.productRange r j) _
    (l.productRange_sound r x hx j) (hs.2 j).2.2.1]
  unfold signedStore
  rw [hb]
  exact l.accumulator_exact r hs x hx j

theorem QuantLayer.machineEval_exact (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (hs : l.Safe r) (x : Fin n → Int) (hx : ∀ i, (r i).Contains (x i)) :
    l.machineEval x = l.eval x := by
  funext j
  have hj := (hs.2 j).2.2.2.2
  have hm := IntRange.storage_exact _ (IntRange.point_sound (l.multiplier j))
    _ l.temporaryBits_pos hj.1
  have hmul := IntRange.scale_sound _ (l.multiplier j) (l.accRange_sound r x hx j)
  rw [Int.mul_comm] at hmul
  have hp := IntRange.storage_exact _ hmul _ l.temporaryBits_pos hj.2.1
  have hr := IntRange.storage_exact _ (IntRange.point_sound ((2 ^ l.shift j : Nat) / 2))
    _ l.temporaryBits_pos hj.2.2.1
  have ht := IntRange.storage_exact _
    (IntRange.add_sound _ _ hmul (IntRange.point_sound ((2 ^ l.shift j : Nat) / 2)))
    _ l.temporaryBits_pos hj.2.2.2.1
  have hq := IntRange.storage_exact _ (l.roundRange_sound r x hx j)
    _ l.temporaryBits_pos hj.2.2.2.2.1
  have hz := IntRange.storage_exact _ (l.preClampRange_sound r x hx j)
    _ l.temporaryBits_pos hj.2.2.2.2.2
  unfold machineEval machineRounded signedStore
  rw [l.machineAcc_exact r hs x hx j, hm, hp, hr, ht]
  change b.store (clamp b.lo b.hi
    (signedStore l.temporaryBits
      (l.reference.activation.integer
        (signedStore l.temporaryBits (l.rounded x j)) + b.zeroPoint))) = _
  unfold signedStore
  rw [hq, hz]
  exact b.storage_exact _ (l.eval_valid x j)

def QuantNetwork.outputRange : (net : QuantNetwork n m a b) →
    (Fin n → IntRange) → (Fin m → IntRange)
  | .done, r => r
  | .cons l net, r => net.outputRange (l.outputRange r)

def QuantNetwork.Safe : (net : QuantNetwork n m a b) → (Fin n → IntRange) → Prop
  | .done, _ => True
  | .cons l net, r => l.Safe r ∧ net.Safe (l.outputRange r)

instance quantNetworkSafeDecidable (net : QuantNetwork n m a b)
    (r : Fin n → IntRange) : Decidable (net.Safe r) :=
  match net with
  | .done => isTrue trivial
  | .cons l net => @instDecidableAnd _ _ inferInstance (quantNetworkSafeDecidable net _)

theorem QuantNetwork.outputRange_sound (net : QuantNetwork n m a b)
    (r : Fin n → IntRange) (x : Fin n → Int) (h : ∀ i, (r i).Contains (x i)) :
    ∀ j, (net.outputRange r j).Contains (net.eval x j) := by
  induction net with
  | done => exact h
  | cons l net ih => exact ih _ _ (l.outputRange_sound r x h)

def QuantNetwork.machineEval : QuantNetwork n m a b → (Fin n → Int) → (Fin m → Int)
  | .done, x => x
  | .cons l net, x => net.machineEval (l.machineEval x)

theorem QuantNetwork.machineEval_exact (net : QuantNetwork n m a b)
    (r : Fin n → IntRange) (hs : net.Safe r) (x : Fin n → Int)
    (hx : ∀ i, (r i).Contains (x i)) : net.machineEval x = net.eval x := by
  induction net with
  | done => rfl
  | cons l net ih =>
    change net.machineEval (l.machineEval x) = net.eval (l.eval x)
    rw [l.machineEval_exact r hs.1 x hx]
    exact ih _ hs.2 _ (l.outputRange_sound r x hx)

end QuantCert.Model

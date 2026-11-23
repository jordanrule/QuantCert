import QuantCert.ModelRange

namespace QuantCert.Model

theorem abs_int_cast (x : Int) : ratAbs (x : Rat) = (x.natAbs : Rat) := by
  have hc : (x : Rat) < 0 ↔ x < 0 := Rat.intCast_lt_intCast
  unfold ratAbs
  simp only [hc]
  split
  · rename_i hx
    have ha : (x.natAbs : Int) = -x := by omega
    have h := congrArg (fun z : Int => (z : Rat)) ha
    simpa only [Rat.intCast_natCast, Rat.intCast_neg] using h.symm
  · rename_i hx
    have ha : (x.natAbs : Int) = x := by omega
    simpa only [Rat.intCast_natCast] using congrArg (fun z : Int => (z : Rat)) ha.symm

theorem abs_mul_le (c x e : Rat) (h : ratAbs x ≤ e) :
    ratAbs (c * x) ≤ ratAbs c * e := by
  rw [abs_mul]
  exact Rat.mul_le_mul_of_nonneg_left h (abs_nonneg c)

theorem Format.decode_mono (f : Format) (h : x ≤ y) : f.decode x ≤ f.decode y := by
  have hc : ((x - f.zeroPoint : Int) : Rat) ≤ ((y - f.zeroPoint : Int) : Rat) :=
    Rat.intCast_le_intCast.mpr (by omega)
  exact Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt f.scale_pos)

theorem Format.saturation_nonexpansive (f : Format) (code : Int) (x : Rat)
    (hx : f.decode f.lo ≤ x ∧ x ≤ f.decode f.hi) :
    ratAbs (f.decode (clamp f.lo f.hi code) - x) ≤ ratAbs (f.decode code - x) := by
  have hb := abs_bounds (f.decode code - x)
  by_cases hl : code < f.lo
  · have hc : clamp f.lo f.hi code = f.lo := by
      have := f.ordered
      unfold clamp
      omega
    rw [hc]
    have := f.decode_mono (x := code) (y := f.lo) (by omega)
    apply abs_le <;> grind
  · by_cases hh : f.hi < code
    · have hc : clamp f.lo f.hi code = f.hi := by
        have := f.ordered
        unfold clamp
        omega
      rw [hc]
      have := f.decode_mono (x := f.hi) (y := code) (by omega)
      apply abs_le <;> grind
    · have hc : clamp f.lo f.hi code = code := by unfold clamp; omega
      rw [hc]
      exact Rat.le_refl

theorem nearest_error (x : Rat) :
    ratAbs (((x + (1 : Rat) / 2).floor : Rat) - x) ≤ (1 : Rat) / 2 := by
  have hl := Rat.floor_le (x + (1 : Rat) / 2)
  have hh := Rat.lt_floor_add_one (x + (1 : Rat) / 2)
  simp only [Rat.intCast_add] at hh
  apply abs_le <;> grind

/-- Input quantization costs at most half an LSB on the representable real domain.
The domain hypothesis is explicit; out-of-domain input clipping is not ignored. -/
theorem Format.encode_error (f : Format) (x : Rat)
    (hx : f.decode f.lo ≤ x ∧ x ≤ f.decode f.hi) :
    ratAbs (f.decode (f.encode x) - x) ≤ f.scale * ((1 : Rat) / 2) := by
  have hn := nearest_error (x / f.scale)
  have hm := abs_mul_le f.scale _ _ hn
  have hs : ratAbs f.scale = f.scale := by
    unfold ratAbs
    have := f.scale_pos
    split <;> grind
  rw [hs] at hm
  have hd := Rat.div_mul_cancel (a := x) (Rat.ne_of_gt f.scale_pos)
  have heq : f.scale * (((x / f.scale + (1 : Rat) / 2).floor : Rat) - x / f.scale) =
      f.decode ((x / f.scale + (1 : Rat) / 2).floor + f.zeroPoint) - x := by
    simp only [Format.decode, Int.add_sub_cancel]
    grind
  rw [heq] at hm
  have hc := f.saturation_nonexpansive
    ((x / f.scale + (1 : Rat) / 2).floor + f.zeroPoint) x hx
  exact Rat.le_trans hc hm

theorem floor_mono (x y : Rat) (h : x ≤ y) : x.floor ≤ y.floor := by
  by_cases hf : x.floor ≤ y.floor
  · exact hf
  · have hc : ((y.floor + 1 : Int) : Rat) ≤ (x.floor : Rat) :=
      Rat.intCast_le_intCast.mpr (by omega)
    have := Rat.floor_le x
    have := Rat.lt_floor_add_one y
    grind

theorem Format.encode_mono (f : Format) (h : x ≤ y) : f.encode x ≤ f.encode y := by
  have hr : x / f.scale ≤ y / f.scale := by
    apply Rat.le_of_mul_le_mul_right (hc := f.scale_pos)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt f.scale_pos),
      Rat.div_mul_cancel (Rat.ne_of_gt f.scale_pos)]
    exact h
  have hf := floor_mono (x / f.scale + (1 : Rat) / 2)
    (y / f.scale + (1 : Rat) / 2) (by grind)
  unfold encode clamp
  omega

def Format.encodedRange (f : Format) (lo hi : Rat) : IntRange :=
  ⟨f.encode lo, f.encode hi⟩

theorem Format.encodedRange_sound (f : Format) (lo hi x : Rat) (h : lo ≤ x ∧ x ≤ hi) :
    (f.encodedRange lo hi).Contains (f.encode x) :=
  ⟨f.encode_mono h.1, f.encode_mono h.2⟩

theorem Activation.cast (a : Activation) (x : Int) :
    (a.integer x : Rat) = a.real (x : Rat) := by
  cases a with
  | identity => rfl
  | relu =>
    simp only [integer, real, Int.max_def]
    split <;> split <;>
      have h₁ := Rat.intCast_le_intCast (a := 0) (b := x) <;>
      have h₂ := Rat.intCast_lt_intCast (a := x) (b := 0) <;> grind

theorem Activation.scale (a : Activation) (x s : Rat) (hs : 0 < s) :
    a.real (x * s) = a.real x * s := by
  cases a with
  | identity => rfl
  | relu =>
    by_cases hx : x < 0
    · have hp := Rat.mul_pos (a := -x) (by grind) hs
      simp only [real]
      split <;> grind
    · have hp := Rat.mul_nonneg (a := x) (b := s) (by grind) (by grind)
      simp only [real]
      split <;> grind

/-- Worst possible clipping distance in code units, including deliberate saturation. -/
def IntRange.clipError (r : IntRange) (f : Format) : Nat :=
  max (f.lo - r.lo).toNat (r.hi - f.hi).toNat

theorem IntRange.clipError_sound (r : IntRange) (f : Format) (h : r.Contains x) :
    (clamp f.lo f.hi x - x).natAbs ≤ r.clipError f := by
  have := f.ordered
  simp only [Contains, clipError, clamp] at *
  omega

def QuantLayer.decodedWeight (l : QuantLayer n m a b) (j : Fin m) (i : Fin n) : Rat :=
  (l.weightFormat j).decode (l.weight j i)

def QuantLayer.decodedBias (l : QuantLayer n m a b) (j : Fin m) : Rat :=
  (l.bias j : Rat) * l.accScale j

def QuantLayer.decodedAffine (l : QuantLayer n m a b) (x : Fin n → Int) (j : Fin m) : Rat :=
  l.decodedBias j + sum n (fun i => l.decodedWeight j i * a.decode (x i))

theorem sum_scale (n : Nat) (f : Fin n → Rat) (c : Rat) :
    sum n f * c = sum n (fun i => f i * c) := by
  induction n with
  | zero => grind [sum]
  | succ n ih => simp only [sum, ← ih]; grind

theorem QuantLayer.affine_exact (l : QuantLayer n m a b) (x : Fin n → Int) (j : Fin m) :
    (l.acc x j : Rat) * l.accScale j = l.decodedAffine x j := by
  simp only [acc, Rat.intCast_add, intSum_cast, Rat.intCast_mul, product,
    decodedAffine, decodedBias, decodedWeight, Format.decode, accScale]
  rw [show ((l.bias j : Rat) +
      sum n (fun i => ((x i - a.zeroPoint : Int) : Rat) *
        ((l.weight j i - (l.weightFormat j).zeroPoint : Int) : Rat))) *
        (a.scale * (l.weightFormat j).scale) =
      (l.bias j : Rat) * (a.scale * (l.weightFormat j).scale) +
        sum n (fun i => ((x i - a.zeroPoint : Int) : Rat) *
          ((l.weight j i - (l.weightFormat j).zeroPoint : Int) : Rat)) *
          (a.scale * (l.weightFormat j).scale) by grind]
  rw [sum_scale]
  congr 1
  congr 1
  funext i
  grind

/-- Actual multiplier discrepancy, computed exactly rather than assumed zero. -/
def QuantLayer.scaleDrift (l : QuantLayer n m a b) (j : Fin m) : Rat :=
  ratAbs (b.scale * ((l.multiplier j : Rat) / (2 ^ l.shift j : Nat)) - l.accScale j)

def QuantLayer.roundError (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) : Rat :=
  b.scale + ((l.accRange r j).magnitude : Rat) * l.scaleDrift j

theorem QuantLayer.roundError_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (x : Fin n → Int) (h : ∀ i, (r i).Contains (x i)) (j : Fin m) :
    ratAbs ((l.rounded x j : Rat) * b.scale - l.decodedAffine x j) ≤ l.roundError r j := by
  have hr := hwRequantize_approx (l.acc x j) (l.multiplier j) (l.multiplier j)
    (2 ^ l.shift j) 0 (l.shift j) (Nat.two_pow_pos _) (by simp)
  have hz : ((0 : Nat) : Rat) / ((2 ^ l.shift j : Nat) : Rat) = 0 := by
    change (0 : Rat) / _ = 0
    rw [Rat.div_def, Rat.zero_mul]
  simp only [hz, Rat.mul_zero, Rat.zero_add] at hr
  have hround := abs_mul_le b.scale
    ((l.rounded x j : Rat) -
      (l.acc x j : Rat) * ((l.multiplier j : Rat) / (2 ^ l.shift j : Nat))) 1 hr
  have hs : ratAbs b.scale = b.scale := by
    unfold ratAbs
    have := b.scale_pos
    split <;> grind
  rw [hs] at hround
  have hm := (l.accRange r j).magnitude_sound (l.accRange_sound r x h j)
  have hm' : ((l.acc x j).natAbs : Rat) ≤ ((l.accRange r j).magnitude : Rat) :=
    Rat.natCast_le_natCast.mpr hm
  have hscale := Rat.mul_le_mul_of_nonneg_right hm' (abs_nonneg
    (b.scale * ((l.multiplier j : Rat) / (2 ^ l.shift j : Nat)) - l.accScale j))
  have htriangle := abs_add
    (b.scale * ((l.rounded x j : Rat) -
      (l.acc x j : Rat) * ((l.multiplier j : Rat) / (2 ^ l.shift j : Nat))))
    ((l.acc x j : Rat) *
      (b.scale * ((l.multiplier j : Rat) / (2 ^ l.shift j : Nat)) - l.accScale j))
  rw [abs_mul (l.acc x j : Rat), abs_int_cast] at htriangle
  have heq :
    b.scale * ((l.rounded x j : Rat) -
      (l.acc x j : Rat) * ((l.multiplier j : Rat) / (2 ^ l.shift j : Nat))) +
    (l.acc x j : Rat) *
      (b.scale * ((l.multiplier j : Rat) / (2 ^ l.shift j : Nat)) - l.accScale j) =
      (l.rounded x j : Rat) * b.scale - l.decodedAffine x j := by
    rw [← l.affine_exact x j]
    grind
  rw [heq] at htriangle
  unfold roundError scaleDrift
  grind

def QuantLayer.clipError (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (j : Fin m) : Rat := ((l.preClampRange r j).clipError b : Rat) * b.scale

theorem QuantLayer.localError_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (x : Fin n → Int) (h : ∀ i, (r i).Contains (x i)) (j : Fin m) :
    ratAbs (b.decode (l.eval x j) -
      l.reference.activation.real (l.decodedAffine x j)) ≤
      l.roundError r j + l.clipError r j := by
  let raw := l.reference.activation.integer (l.rounded x j) + b.zeroPoint
  have hc := (l.preClampRange r j).clipError_sound b (l.preClampRange_sound r x h j)
  have hc' : ((clamp b.lo b.hi raw - raw).natAbs : Rat) ≤
      ((l.preClampRange r j).clipError b : Rat) := Rat.natCast_le_natCast.mpr hc
  have hcs := Rat.mul_le_mul_of_nonneg_right hc' (Rat.le_of_lt b.scale_pos)
  have hr := l.roundError_sound r x h j
  have ha := l.reference.activation.nonexpansive
    ((l.rounded x j : Rat) * b.scale) (l.decodedAffine x j)
  have heq : b.decode raw =
      l.reference.activation.real ((l.rounded x j : Rat) * b.scale) := by
    simp only [Format.decode, raw, Int.add_sub_cancel, Activation.scale _ _ _ b.scale_pos,
      Activation.cast]
  have hclip :
      ratAbs (b.decode (l.eval x j) - b.decode raw) ≤ l.clipError r j := by
    have hd : b.decode (l.eval x j) - b.decode raw =
        ((clamp b.lo b.hi raw - raw : Int) : Rat) * b.scale := by
      simp only [Format.decode, eval, raw, Rat.intCast_sub, Rat.intCast_add]
      grind
    rw [hd, abs_mul, abs_int_cast]
    have hs : ratAbs b.scale = b.scale := by
      unfold ratAbs
      have := b.scale_pos
      split <;> grind
    rw [hs]
    exact hcs
  have ht := abs_add (b.decode (l.eval x j) - b.decode raw)
    (b.decode raw - l.reference.activation.real (l.decodedAffine x j))
  rw [← heq] at ha
  have he : b.decode (l.eval x j) - b.decode raw +
      (b.decode raw - l.reference.activation.real (l.decodedAffine x j)) =
      b.decode (l.eval x j) - l.reference.activation.real (l.decodedAffine x j) := by grind
  rw [he] at ht
  grind

/-- Bias/weight mismatch is measured against the supplied ideal model, including clipping. -/
def QuantLayer.affineError (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (error : Fin n → Rat) (j : Fin m) : Rat :=
  ratAbs (l.decodedBias j - l.reference.bias j) +
    sum n (fun i => ratAbs (l.reference.weight j i) * error i +
      ratAbs (l.decodedWeight j i - l.reference.weight j i) *
        (((l.centeredRange (r i)).magnitude : Rat) * a.scale))

def QuantLayer.outputError (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (error : Fin n → Rat) (j : Fin m) : Rat :=
  l.affineError r error j + l.roundError r j + l.clipError r j

theorem QuantLayer.affineError_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (error : Fin n → Rat) (real : Fin n → Rat) (x : Fin n → Int)
    (hx : ∀ i, (r i).Contains (x i))
    (he : ∀ i, ratAbs (a.decode (x i) - real i) ≤ error i) (j : Fin m) :
    ratAbs (l.decodedAffine x j -
      (l.reference.bias j + sum n (fun i => l.reference.weight j i * real i))) ≤
      l.affineError r error j := by
  have hterm (i : Fin n) :
      ratAbs (l.decodedWeight j i * a.decode (x i) - l.reference.weight j i * real i) ≤
        ratAbs (l.reference.weight j i) * error i +
        ratAbs (l.decodedWeight j i - l.reference.weight j i) *
          (((l.centeredRange (r i)).magnitude : Rat) * a.scale) := by
    have hc := IntRange.add_sound _ _ (hx i) (IntRange.point_sound (-a.zeroPoint))
    have hm := (l.centeredRange (r i)).magnitude_sound
      (show (l.centeredRange (r i)).Contains (x i - a.zeroPoint) from by
        simpa [centeredRange, Int.sub_eq_add_neg] using hc)
    have hm' := Rat.natCast_le_natCast.mpr hm
    have hd : ratAbs (a.decode (x i)) ≤
        ((l.centeredRange (r i)).magnitude : Rat) * a.scale := by
      simp only [Format.decode, abs_mul, abs_int_cast]
      have hs : ratAbs a.scale = a.scale := by
        unfold ratAbs
        have := a.scale_pos
        split <;> grind
      rw [hs]
      exact Rat.mul_le_mul_of_nonneg_right hm' (Rat.le_of_lt a.scale_pos)
    have h₁ := abs_mul_le (l.reference.weight j i) _ _ (he i)
    have h₂ := abs_mul_le (l.decodedWeight j i - l.reference.weight j i) _ _ hd
    have ht := abs_add
      (l.reference.weight j i * (a.decode (x i) - real i))
      ((l.decodedWeight j i - l.reference.weight j i) * a.decode (x i))
    have hid :
        l.reference.weight j i * (a.decode (x i) - real i) +
          (l.decodedWeight j i - l.reference.weight j i) * a.decode (x i) =
        l.decodedWeight j i * a.decode (x i) - l.reference.weight j i * real i := by grind
    rw [hid] at ht
    grind
  have hsum := sum_le n _ _ hterm
  have habs := sum_abs_le n
    (fun i => l.decodedWeight j i * a.decode (x i) - l.reference.weight j i * real i)
  have ht := abs_add (l.decodedBias j - l.reference.bias j)
    (sum n (fun i => l.decodedWeight j i * a.decode (x i) - l.reference.weight j i * real i))
  rw [sum_sub] at ht habs
  unfold affineError decodedAffine
  have hid : l.decodedBias j + sum n (fun i => l.decodedWeight j i * a.decode (x i)) -
      (l.reference.bias j + sum n (fun i => l.reference.weight j i * real i)) =
      l.decodedBias j - l.reference.bias j +
        (sum n (fun i => l.decodedWeight j i * a.decode (x i)) -
          sum n (fun i => l.reference.weight j i * real i)) := by grind
  rw [hid]
  grind

theorem QuantLayer.outputError_sound (l : QuantLayer n m a b) (r : Fin n → IntRange)
    (error : Fin n → Rat) (real : Fin n → Rat) (x : Fin n → Int)
    (hx : ∀ i, (r i).Contains (x i))
    (he : ∀ i, ratAbs (a.decode (x i) - real i) ≤ error i) (j : Fin m) :
    ratAbs (b.decode (l.eval x j) - l.reference.eval real j) ≤ l.outputError r error j := by
  have hl := l.localError_sound r x hx j
  have hf := l.affineError_sound r error real x hx he j
  have ha := l.reference.activation.nonexpansive (l.decodedAffine x j)
    (l.reference.bias j + sum n (fun i => l.reference.weight j i * real i))
  have ht := abs_add
    (b.decode (l.eval x j) - l.reference.activation.real (l.decodedAffine x j))
    (l.reference.activation.real (l.decodedAffine x j) - l.reference.eval real j)
  have hid : b.decode (l.eval x j) - l.reference.activation.real (l.decodedAffine x j) +
      (l.reference.activation.real (l.decodedAffine x j) - l.reference.eval real j) =
      b.decode (l.eval x j) - l.reference.eval real j := by grind
  rw [hid] at ht
  unfold outputError
  unfold Layer.eval at *
  grind

def QuantNetwork.outputError : (net : QuantNetwork n m a b) →
    (Fin n → IntRange) → (Fin n → Rat) → (Fin m → Rat)
  | .done, _, e => e
  | .cons l net, r, e => net.outputError (l.outputRange r) (l.outputError r e)

/-- Compositional error in real-value units for arbitrary fixed affine/ReLU networks. -/
theorem QuantNetwork.outputError_sound (net : QuantNetwork n m a b)
    (r : Fin n → IntRange) (error : Fin n → Rat) (real : Fin n → Rat) (x : Fin n → Int)
    (hx : ∀ i, (r i).Contains (x i))
    (he : ∀ i, ratAbs (a.decode (x i) - real i) ≤ error i) :
    ∀ j, ratAbs (b.decode (net.eval x j) - net.reference.eval real j) ≤
      net.outputError r error j := by
  induction net with
  | done => exact he
  | cons l net ih =>
    exact ih _ _ _ _ (l.outputRange_sound r x hx) (l.outputError_sound r error real x hx he)

theorem QuantNetwork.machineError_sound (net : QuantNetwork n m a b)
    (r : Fin n → IntRange) (hs : net.Safe r) (error : Fin n → Rat)
    (real : Fin n → Rat) (x : Fin n → Int) (hx : ∀ i, (r i).Contains (x i))
    (he : ∀ i, ratAbs (a.decode (x i) - real i) ≤ error i) (j : Fin m) :
    ratAbs (b.decode (net.machineEval x j) - net.reference.eval real j) ≤
      net.outputError r error j := by
  rw [net.machineEval_exact r hs x hx]
  exact net.outputError_sound r error real x hx he j

/-- From rational inputs through input encoding and every stored intermediate.
Both the input box and the representable-domain assumptions remain visible. -/
theorem QuantNetwork.encodedError_sound (net : QuantNetwork n m a b)
    (lo hi : Fin n → Rat)
    (hs : net.Safe (fun i => a.encodedRange (lo i) (hi i)))
    (x : Fin n → Rat) (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hd : ∀ i, a.decode a.lo ≤ x i ∧ x i ≤ a.decode a.hi) (j : Fin m) :
    ratAbs (b.decode (net.machineEval (fun i => a.encode (x i)) j) -
      net.reference.eval x j) ≤
      net.outputError (fun i => a.encodedRange (lo i) (hi i))
        (fun _ => a.scale * ((1 : Rat) / 2)) j :=
  net.machineError_sound _ hs _ x _ (fun i => a.encodedRange_sound _ _ _ (hx i))
    (fun i => a.encode_error _ (hd i)) j

end QuantCert.Model

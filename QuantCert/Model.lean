import QuantCert.Quant

namespace QuantCert.Model

theorem abs_bounds (a : Rat) : -ratAbs a ≤ a ∧ a ≤ ratAbs a := by
  unfold ratAbs
  split <;> grind

theorem abs_le {a b : Rat} (lo : -b ≤ a) (hi : a ≤ b) : ratAbs a ≤ b := by
  unfold ratAbs
  split <;> grind

theorem abs_nonneg (a : Rat) : 0 ≤ ratAbs a := by
  have := abs_bounds a
  grind

theorem abs_add (a b : Rat) : ratAbs (a + b) ≤ ratAbs a + ratAbs b := by
  have := abs_bounds a
  have := abs_bounds b
  apply abs_le <;> grind

theorem abs_mul (a b : Rat) : ratAbs (a * b) = ratAbs a * ratAbs b := by
  unfold ratAbs
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · have := Rat.mul_nonneg (a := -a) (b := -b) (by grind) (by grind)
    split <;> grind
  · have := Rat.mul_nonneg (a := -a) (b := b) (by grind) (by grind)
    split <;> grind
  · have := Rat.mul_nonneg (a := a) (b := -b) (by grind) (by grind)
    split <;> grind
  · have := Rat.mul_nonneg (a := a) (b := b) (by grind) (by grind)
    split <;> grind

theorem abs_sub (a b : Rat) : ratAbs (a - b) = ratAbs (b - a) := by
  unfold ratAbs
  split <;> split <;> grind

def sum : (n : Nat) → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => f 0 + sum n (fun i => f i.succ)

theorem sum_add (n : Nat) (f g : Fin n → Rat) :
    sum n (fun i => f i + g i) = sum n f + sum n g := by
  induction n with
  | zero => grind [sum]
  | succ n ih => simp only [sum, ih]; grind

theorem sum_sub (n : Nat) (f g : Fin n → Rat) :
    sum n (fun i => f i - g i) = sum n f - sum n g := by
  induction n with
  | zero => grind [sum]
  | succ n ih => simp only [sum, ih]; grind

theorem sum_abs_le (n : Nat) (f : Fin n → Rat) :
    ratAbs (sum n f) ≤ sum n (fun i => ratAbs (f i)) := by
  induction n with
  | zero => change ratAbs 0 ≤ 0; decide
  | succ n ih =>
    have := abs_add (f 0) (sum n (fun i => f i.succ))
    have := ih (fun i => f i.succ)
    change ratAbs (f 0 + _) ≤ ratAbs (f 0) + _
    grind

theorem sum_le (n : Nat) (f g : Fin n → Rat) (h : ∀ i, f i ≤ g i) :
    sum n f ≤ sum n g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    have := h 0
    have := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)
    change f 0 + _ ≤ g 0 + _
    grind

inductive Activation where
  | identity
  | relu
  deriving DecidableEq, Repr

def Activation.real : Activation → Rat → Rat
  | .identity, x => x
  | .relu, x => if x < 0 then 0 else x

def Activation.integer : Activation → Int → Int
  | .identity, x => x
  | .relu, x => max 0 x

theorem Activation.nonexpansive (a : Activation) (x y : Rat) :
    ratAbs (a.real x - a.real y) ≤ ratAbs (x - y) := by
  cases a with
  | identity => exact Rat.le_refl
  | relu =>
    have := abs_bounds (x - y)
    apply abs_le <;> simp only [real]
    all_goals
      change _ ≤ _
      split <;> split <;> grind

/-- Fixed parameters and dimension-indexed tensors; no truncating zip operations. -/
structure Layer (inputs outputs : Nat) where
  weight : Fin outputs → Fin inputs → Rat
  bias : Fin outputs → Rat
  activation : Activation

def Layer.eval (l : Layer n m) (x : Fin n → Rat) : Fin m → Rat :=
  fun j => l.activation.real (l.bias j + sum n (fun i => l.weight j i * x i))

inductive Network : Nat → Nat → Type where
  | done : Network n n
  | cons : Layer n m → Network m k → Network n k

def Network.eval : Network n m → (Fin n → Rat) → (Fin m → Rat)
  | .done, x => x
  | .cons l net, x => net.eval (l.eval x)

def storageLo (signed : Bool) (bits : Nat) : Int :=
  if signed then -(2 ^ (bits - 1) : Nat) else 0

def storageHi (signed : Bool) (bits : Nat) : Int :=
  if signed then (2 ^ (bits - 1) : Nat) - 1 else (2 ^ bits : Nat) - 1

/-- Affine quantization: value = (code - zeroPoint) * scale. -/
structure Format where
  bits : Nat
  bits_pos : 0 < bits
  signed : Bool
  scale : Rat
  scale_pos : 0 < scale
  zeroPoint : Int
  zeroPoint_lo : storageLo signed bits ≤ zeroPoint
  zeroPoint_hi : zeroPoint ≤ storageHi signed bits

def Format.lo (f : Format) : Int := storageLo f.signed f.bits
def Format.hi (f : Format) : Int := storageHi f.signed f.bits

def clamp (lo hi x : Int) : Int := max lo (min hi x)

theorem clamp_bounds (lo hi x : Int) (h : lo ≤ hi) :
    lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi := by
  unfold clamp
  omega

theorem Format.ordered (f : Format) : f.lo ≤ f.hi :=
  Int.le_trans f.zeroPoint_lo f.zeroPoint_hi

def Format.valid (f : Format) (code : Int) : Prop := f.lo ≤ code ∧ code ≤ f.hi
def Format.decode (f : Format) (code : Int) : Rat := ((code - f.zeroPoint : Int) : Rat) * f.scale

/-- Exact rational nearest rounding, ties toward positive infinity, then saturation. -/
def Format.encode (f : Format) (value : Rat) : Int :=
  clamp f.lo f.hi ((value / f.scale + (1 : Rat) / 2).floor + f.zeroPoint)

theorem Format.encode_valid (f : Format) (value : Rat) : f.valid (f.encode value) :=
  clamp_bounds _ _ _ f.ordered

def intSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => f 0 + intSum n (fun i => f i.succ)

theorem intSum_cast (n : Nat) (f : Fin n → Int) :
    ((intSum n f : Int) : Rat) = sum n (fun i => (f i : Rat)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intSum, sum, Rat.intCast_add, ih]

/-- Uniform activation format, per-output-channel weight formats and requantizers.
Bias codes have scale `input.scale * weightFormat.scale` and zero point zero. -/
structure QuantLayer (inputs outputs : Nat) (input output : Format) where
  reference : Layer inputs outputs
  weightFormat : Fin outputs → Format
  weight : Fin outputs → Fin inputs → Int
  weight_valid : ∀ j i, (weightFormat j).valid (weight j i)
  bias : Fin outputs → Int
  multiplier : Fin outputs → Int
  shift : Fin outputs → Nat
  accumulatorBits : Nat
  accumulatorBits_pos : 0 < accumulatorBits
  temporaryBits : Nat
  temporaryBits_pos : 0 < temporaryBits

/-- Quantize fixed parameters and choose the nearest multiplier for each requested shift.
Bias is not silently clipped: an undersized bias/accumulator fails the safety check. -/
def Layer.quantize (l : Layer n m) (input output : Format)
    (weightFormat : Fin m → Format) (shift : Fin m → Nat)
    (accumulatorBits temporaryBits : Nat)
    (ha : 0 < accumulatorBits) (ht : 0 < temporaryBits) :
    QuantLayer n m input output where
  reference := l
  weightFormat := weightFormat
  weight j i := (weightFormat j).encode (l.weight j i)
  weight_valid j _ := (weightFormat j).encode_valid _
  bias j := (l.bias j / (input.scale * (weightFormat j).scale) + (1 : Rat) / 2).floor
  multiplier j :=
    ((input.scale * (weightFormat j).scale / output.scale) *
      (2 ^ shift j : Nat) + (1 : Rat) / 2).floor
  shift := shift
  accumulatorBits := accumulatorBits
  accumulatorBits_pos := ha
  temporaryBits := temporaryBits
  temporaryBits_pos := ht

def QuantLayer.accScale (l : QuantLayer n m a b) (j : Fin m) : Rat :=
  a.scale * (l.weightFormat j).scale

theorem QuantLayer.accScale_pos (l : QuantLayer n m a b) (j : Fin m) :
    0 < l.accScale j := Rat.mul_pos a.scale_pos (l.weightFormat j).scale_pos

def QuantLayer.product (l : QuantLayer n m a b) (x : Fin n → Int)
    (j : Fin m) (i : Fin n) : Int :=
  (x i - a.zeroPoint) * (l.weight j i - (l.weightFormat j).zeroPoint)

def QuantLayer.acc (l : QuantLayer n m a b) (x : Fin n → Int) (j : Fin m) : Int :=
  l.bias j + intSum n (l.product x j)

def QuantLayer.rounded (l : QuantLayer n m a b) (x : Fin n → Int) (j : Fin m) : Int :=
  hwRequantizeInt (l.acc x j) (l.multiplier j) (l.shift j)

def QuantLayer.eval (l : QuantLayer n m a b) (x : Fin n → Int) : Fin m → Int :=
  fun j => clamp b.lo b.hi (l.reference.activation.integer (l.rounded x j) + b.zeroPoint)

theorem QuantLayer.eval_valid (l : QuantLayer n m a b) (x : Fin n → Int) (j : Fin m) :
    b.valid (l.eval x j) := clamp_bounds _ _ _ b.ordered

inductive QuantNetwork : Nat → Nat → Format → Format → Type where
  | done : QuantNetwork n n f f
  | cons : QuantLayer n m a b → QuantNetwork m k b c → QuantNetwork n k a c

def QuantNetwork.eval : QuantNetwork n m a b → (Fin n → Int) → (Fin m → Int)
  | .done, x => x
  | .cons l net, x => net.eval (l.eval x)

def QuantNetwork.reference : QuantNetwork n m a b → Network n m
  | .done => .done
  | .cons l net => .cons l.reference net.reference

end QuantCert.Model

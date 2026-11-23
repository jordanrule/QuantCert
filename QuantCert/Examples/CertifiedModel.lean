import QuantCert.ModelLowering

namespace QuantCert.Model.Examples

def input8 : Format :=
  ⟨8, by decide, false, (1 : Rat) / 16, by decide +kernel, 128, by decide, by decide⟩

def hidden8 : Format :=
  ⟨8, by decide, false, (1 : Rat) / 16, by decide +kernel, 3, by decide, by decide⟩

def output8 : Format :=
  ⟨8, by decide, true, (3 : Rat) / 32, by decide +kernel, -5, by decide, by decide⟩

def weight8 : Format :=
  ⟨8, by decide, true, (1 : Rat) / 8, by decide +kernel, 0, by decide, by decide⟩

def channelWeight8 : Format :=
  ⟨8, by decide, false, (1 : Rat) / 16, by decide +kernel, 128, by decide, by decide⟩

def firstReference : Layer 2 2 where
  weight j i :=
    if j.val = 0 then (if i.val = 0 then 1 / 2 else -1 / 3)
    else (if i.val = 0 then -3 / 8 else 5 / 16)
  bias j := if j.val = 0 then 1 / 10 else -1 / 16
  activation := .relu

def secondReference : Layer 2 1 where
  weight _ i := if i.val = 0 then 3 / 4 else -1 / 2
  bias _ := 1 / 7
  activation := .identity

def first : QuantLayer 2 2 input8 hidden8 :=
  firstReference.quantize input8 hidden8
    (fun j => if j.val = 0 then weight8 else channelWeight8) (fun _ => 6)
    16 32 (by decide) (by decide)

def second : QuantLayer 2 1 hidden8 output8 :=
  secondReference.quantize hidden8 output8 (fun _ => weight8) (fun _ => 6)
    16 32 (by decide) (by decide)

def classifier : QuantNetwork 2 1 input8 output8 := .cons first (.cons second .done)

/-- Real input domain [-1, 1] maps to these code intervals. -/
def inputBox : Fin 2 → IntRange := fun _ => input8.encodedRange (-1) 1

theorem inputBox_codes : inputBox 0 = ⟨112, 144⟩ := by decide +kernel

theorem classifier_safe : classifier.Safe inputBox := by decide +kernel

theorem classifier_full_codes_safe : classifier.Safe (fun _ => ⟨0, 255⟩) := by
  decide +kernel

theorem classifier_output_range : classifier.outputRange inputBox 0 = ⟨-7, 4⟩ := by
  decide +kernel

theorem classifier_error_budget :
    classifier.outputError inputBox (fun _ => input8.scale * ((1 : Rat) / 2)) 0 ≤
      (1 : Rat) / 3 := by decide +kernel

/-- Includes rational input encoding, inexact weights/biases, multiplier error,
two layers of rounding, and every finite-width intermediate. -/
theorem classifier_real_error (x : Fin 2 → Rat)
    (hx : ∀ i, (-1 : Rat) ≤ x i ∧ x i ≤ 1) :
    ratAbs (output8.decode (classifier.machineEval (fun i => input8.encode (x i)) 0) -
      classifier.reference.eval x 0) ≤ (1 : Rat) / 3 := by
  have hr (i : Fin 2) : (inputBox i).Contains (input8.encode (x i)) := by
    exact input8.encodedRange_sound (-1) 1 (x i) (hx i)
  have hd (i : Fin 2) : input8.decode input8.lo ≤ x i ∧ x i ≤ input8.decode input8.hi := by
    have := hx i
    rw [show input8.decode input8.lo = (-8 : Rat) from by decide +kernel,
      show input8.decode input8.hi = (127 : Rat) / 16 from by decide +kernel]
    grind
  exact Rat.le_trans
    (classifier.machineError_sound inputBox classifier_safe _ x _
      hr (fun i => input8.encode_error _ (hd i)) 0)
    classifier_error_budget

/-- The same error receipt now applies to the shared circuit frontend. -/
theorem classifier_circuit_error (x : Fin 2 → Rat)
    (hx : ∀ i, (-1 : Rat) ≤ x i ∧ x i ≤ 1) :
    ratAbs (output8.decode (codes output8
      (evalCircuit classifier.lower (encodeCodes input8 (fun i => input8.encode (x i)))) 0) -
        classifier.reference.eval x 0) ≤ (1 : Rat) / 3 := by
  rw [classifier.lower_correct, codes_encode]
  have he : (fun i => input8.store (input8.encode (x i))) =
      (fun i => input8.encode (x i)) := by
    funext i
    exact input8.storage_exact _ (input8.encode_valid _)
  rw [he]
  exact classifier_real_error x hx

theorem classifier_compiled_error (x : Fin 2 → Rat)
    (hx : ∀ i, (-1 : Rat) ≤ x i ∧ x i ≤ 1)
    (e : WireEnv (bundle input8.wire 2)) (next : Nat) (seed : Store)
    (hbound : Bounded e next)
    (hinput : readEnv e seed = encodeCodes input8 (fun i => input8.encode (x i))) :
    ratAbs (output8.decode (codes output8
      (readEnv (compile classifier.lower e ⟨next, []⟩).1
        (evalNetlist (compile classifier.lower e ⟨next, []⟩).2.cells seed)) 0) -
        classifier.reference.eval x 0) ≤ (1 : Rat) / 3 := by
  rw [QuantCert.compile_correct classifier.lower e ⟨next, []⟩ seed hbound]
  change ratAbs (output8.decode
    (codes output8 (evalCircuit classifier.lower (readEnv e seed)) 0) -
      classifier.reference.eval x 0) ≤ _
  rw [hinput]
  exact classifier_circuit_error x hx

/-- This is a conservative certificate rejection, not an overflow witness. -/
def undersizedAccumulator : QuantLayer 2 2 input8 hidden8 :=
  { first with accumulatorBits := 8, accumulatorBits_pos := by decide }

def undersizedTemporary : QuantLayer 2 2 input8 hidden8 :=
  { first with temporaryBits := 8, temporaryBits_pos := by decide }

theorem rejects_undersized_accumulator : ¬undersizedAccumulator.Safe inputBox := by decide +kernel
theorem rejects_undersized_temporary : ¬undersizedTemporary.Safe inputBox := by decide +kernel

def tighterFirst : QuantLayer 2 2 input8 hidden8 :=
  { first with
    accumulatorBits := 9
    accumulatorBits_pos := by decide
    temporaryBits := 12
    temporaryBits_pos := by decide }

def roundingAdditionTooNarrow : QuantLayer 2 2 input8 hidden8 :=
  { tighterFirst with temporaryBits := 11, temporaryBits_pos := by decide }

theorem tighter_first_safe : tighterFirst.Safe inputBox := by decide +kernel

theorem rejects_rounding_addition_width : ¬roundingAdditionTooNarrow.Safe inputBox := by
  decide +kernel

end QuantCert.Model.Examples

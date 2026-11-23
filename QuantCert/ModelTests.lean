import QuantCert.Examples.CertifiedModel

namespace QuantCert.Model.Tests
open Examples

#guard input8.encode 0 == 128
#guard input8.encode ((1 : Rat) / 32) == 129
#guard input8.encode ((-1 : Rat) / 32) == 128
#guard input8.encode 100 == 255
#guard input8.encode (-100) == 0
#guard output8.encode ((3 : Rat) / 64) == -4
#guard output8.encode ((-3 : Rat) / 64) == -5
#guard output8.encode 100 == 127
#guard output8.encode (-100) == -128
#guard input8.decode 128 == 0
#guard output8.decode (-5) == 0
#guard input8.store 255 == 255
#guard output8.store (-128) == -128
#guard (inputBox 0).scale (-3) == ⟨-432, -336⟩
#guard (IntRange.mk (-257) (-256)).shift 9 == ⟨-1, -1⟩
#guard ((IntRange.mk (-257) (-256)).add (.point 256)).shift 9 == ⟨-1, 0⟩
#guard (first.outputRange inputBox 0) == ⟨3, 19⟩
#guard (first.outputRange inputBox 1) == ⟨3, 13⟩
#guard first.multiplier 0 == 8
#guard first.multiplier 1 == 4
#guard second.multiplier 0 == 5
#guard first.scaleDrift 0 == 0
#guard second.scaleDrift 0 == (1 : Rat) / 2048
#guard first.decodedWeight 0 1 != first.reference.weight 0 1
#guard first.decodedBias 0 != first.reference.bias 0
#guard second.clipError (first.outputRange inputBox) 0 == 0
#guard (IntRange.mk (-200) 200).clipError output8 == 73
#guard (IntRange.mk 0 255).saturate output8 == ⟨0, 127⟩
#guard decide (classifier.Safe inputBox)
#guard !decide (undersizedAccumulator.Safe inputBox)
#guard !decide (undersizedTemporary.Safe inputBox)
#guard decide ((first.mulRange inputBox 0).fits 11)
#guard !decide ((first.tempRange inputBox 0).fits 11)
#guard first.tempRange inputBox 0 == ⟨-760, 1032⟩
#guard decide (tighterFirst.Safe inputBox)
#guard !decide (roundingAdditionTooNarrow.Safe inputBox)
#guard classifier.eval (fun _ => 128) 0 == -3
#guard classifier.machineEval (fun _ => 128) 0 == classifier.eval (fun _ => 128) 0

def tinyOutput : Format :=
  ⟨2, by decide, true, (3 : Rat) / 32, by decide +kernel, -1, by decide, by decide⟩

def clippedSecond : QuantLayer 2 1 hidden8 tinyOutput :=
  secondReference.quantize hidden8 tinyOutput (fun _ => weight8) (fun _ => 6)
    16 32 (by decide) (by decide)

def clippedNetwork : QuantNetwork 2 1 input8 tinyOutput :=
  .cons first (.cons clippedSecond .done)

#guard clippedSecond.clipError (first.outputRange inputBox) 0 == (21 : Rat) / 32
#guard clippedNetwork.outputRange inputBox 0 == ⟨-2, 1⟩
#guard clippedNetwork.machineEval (fun i => if i.val = 0 then 144 else 112) 0 == 1
#guard decide (clippedNetwork.Safe inputBox)

theorem clipped_network_safe : clippedNetwork.Safe inputBox := by decide +kernel

theorem clipped_network_error_budget :
    clippedNetwork.outputError inputBox (fun _ => input8.scale * ((1 : Rat) / 2)) 0 ≤ 1 := by
  decide +kernel

def negativeMultiplier : QuantLayer 2 1 hidden8 output8 :=
  { second with multiplier := fun _ => -5 }

def zeroShift : QuantLayer 2 1 hidden8 output8 :=
  secondReference.quantize hidden8 output8 (fun _ => weight8) (fun _ => 0)
    16 32 (by decide) (by decide)

#guard decide (negativeMultiplier.Safe (first.outputRange inputBox))
#guard negativeMultiplier.roundRange (first.outputRange inputBox) 0 == ⟨-9, 2⟩
#guard negativeMultiplier.machineEval (fun _ => 3) 0 == negativeMultiplier.eval (fun _ => 3) 0
#guard zeroShift.multiplier 0 == 0
#guard decide (zeroShift.Safe (first.outputRange inputBox))
#guard zeroShift.machineEval (fun _ => 3) 0 == -5

def biasOnlyReference : Layer 0 1 where
  weight _ i := Fin.elim0 i
  bias _ := (1 : Rat) / 2
  activation := .identity

def biasOnly : QuantLayer 0 1 input8 hidden8 :=
  biasOnlyReference.quantize input8 hidden8 (fun _ => weight8) (fun _ => 6)
    16 32 (by decide) (by decide)

#guard decide (biasOnly.Safe (fun i => Fin.elim0 i))
#guard biasOnly.machineEval (fun i => Fin.elim0 i) 0 == 11
#guard (QuantNetwork.done : QuantNetwork 2 2 input8 input8).outputError inputBox (fun _ => 0) 0 == 0

/-- The wrapper theorem includes the input encoder without a supplied input-error receipt. -/
example (x : Fin 2 → Rat) (hx : ∀ i, (-1 : Rat) ≤ x i ∧ x i ≤ 1)
    (hd : ∀ i, input8.decode input8.lo ≤ x i ∧ x i ≤ input8.decode input8.hi) :
    ratAbs (output8.decode (classifier.machineEval (fun i => input8.encode (x i)) 0) -
      classifier.reference.eval x 0) ≤
      classifier.outputError (fun _ => input8.encodedRange (-1) 1)
        (fun _ => input8.scale * ((1 : Rat) / 2)) 0 :=
  classifier.encodedError_sound (fun _ => -1) (fun _ => 1) classifier_safe x hx hd 0

end QuantCert.Model.Tests

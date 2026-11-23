import QuantCert.ModelTests

namespace QuantCert.RTLTests
open Model Model.Examples Model.Tests

def signed8 : QType := ⟨8, by decide, 1, by decide, true⟩
def unsigned8 : QType := ⟨8, by decide, 1, by decide, false⟩
def signed16 : QType := rawWire 16 (by decide)
def signed4 : QType := rawWire 4 (by decide)
def unsigned4 : QType := ⟨4, by decide, 1, by decide, false⟩

/-- Every leaf uses the same Circuit compiler and printer as the model and legacy demo. -/
def primitiveRegressions :=
  let mixed : Circuit (.word signed8 ⊗ .word unsigned8) (.word signed16) :=
    Circuit.prim (.mul signed8 unsigned8 signed16 (by decide +kernel))
  let requant : Circuit (.word signed8 ⊗ .word unsigned8) (.word signed16) :=
    Circuit.snd >>> Circuit.prim (.requant unsigned8 signed16 ⟨-3, 0, 4, by decide +kernel⟩)
  let center : Circuit (.word signed8 ⊗ .word unsigned8) (.word signed4) :=
    Circuit.snd >>> Circuit.prim (.offset unsigned8 signed4 128)
  let clip : Circuit (.word signed8 ⊗ .word unsigned8) (.word unsigned4) :=
    Circuit.fst >>> Circuit.prim (.clip signed8 unsigned4 0 15)
  let ushift : Circuit (.word signed8 ⊗ .word unsigned8) (.word unsigned8) :=
    Circuit.snd >>> Circuit.prim (.shift unsigned8 9)
  let sshift : Circuit (.word signed8 ⊗ .word unsigned8) (.word signed8) :=
    Circuit.fst >>> Circuit.prim (.shift signed8 9)
  let bias : Circuit (.word signed8 ⊗ .word unsigned8) (bundle hidden8.wire 1) :=
    Circuit.drop >>> biasOnly.lower
  mixed &&& (requant &&& (center &&& (clip &&& (ushift &&& (sshift &&& bias)))))

#guard wordInt unsigned8 (255#8) == 255
#guard (evalPrim (.relu unsigned8) (255#8)).toNat == 255
#guard (evalCircuit primitiveRegressions (BitVec.ofInt 8 (-128), 255#8)).1.toInt == -32640

def loweredCode (net : QuantNetwork n m a b) (x : Fin n → Int) : Fin m → Int :=
  codes b (evalCircuit net.lower (encodeCodes a x))

#guard loweredCode classifier (fun _ => 128) 0 == -3
#guard loweredCode clippedNetwork (fun i => if i.val = 0 then 144 else 112) 0 == 1
#guard loweredCode (.cons negativeMultiplier .done) (fun _ => 3) 0 == -6
#guard loweredCode (.cons zeroShift .done) (fun _ => 3) 0 == -5
#guard loweredCode (.cons biasOnly .done) (fun i => Fin.elim0 i) 0 == 11
#guard loweredCode (QuantNetwork.done : QuantNetwork 2 2 input8 input8) (fun _ => 255) 0 == 255

/-- Even intentionally unsafe widths preserve exactly the modeled wrap semantics. -/
def wrappingNetwork : QuantNetwork 2 2 input8 hidden8 := .cons undersizedAccumulator .done

#guard loweredCode wrappingNetwork (fun i => if i.val = 0 then 255 else 0) 0 ==
  wrappingNetwork.machineEval (fun i => if i.val = 0 then 255 else 0) 0

end QuantCert.RTLTests

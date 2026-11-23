import QuantCert.Examples.QuantizedLayer

namespace QuantCert.Tests
open Examples

def runLayer (x y z t : Int) : Int :=
  (evalCircuit quantizedLayer
    ((BitVec.ofInt 8 x, BitVec.ofInt 8 y), (BitVec.ofInt 8 z, BitVec.ofInt 8 t))).toInt

#guard runLayer (-128) (-128) (-128) (-128) == 64
#guard runLayer (-128) 127 (-128) 127 == 0
#guard runLayer 127 127 127 127 == 63
#guard runLayer 1 1 0 0 == 0
#guard runLayer 16 16 0 0 == 1
#guard hwRequantizeInt (-256) 1 9 == 0
#guard hwRequantizeInt (-257) 1 9 == -1
#guard hwRequantizeInt 7 (-3) 0 == -21
#guard (quantize int8 ((1 : Rat) / 2)).toInt == 64
#guard dequantize int8 (BitVec.ofInt 8 64) == (1 : Rat) / 2
#guard (evalCircuit gateDemo (1#1, 1#1)).1 == 0#1
#guard (evalCircuit gateDemo (0#1, 1#1)).1 == 1#1
#guard (compile gateDemo (0, 1) ⟨2, []⟩).2.cells.length == 1
#guard (compile (Circuit.dup : Circuit (.word int8) (.word int8 ⊗ .word int8))
  0 ⟨1, []⟩).2.cells.isEmpty
#guard match toVerilogChecked "bad;module" quantizedLayer with
  | .error _ => true
  | .ok _ => false

/-- A concrete input binding illustrates the general correctness theorem. -/
theorem layer_compiler_correct (seed : Store) :
    readEnv (compile quantizedLayer ((0, 1), (2, 3)) ⟨4, []⟩).1
      (evalNetlist (compile quantizedLayer ((0, 1), (2, 3)) ⟨4, []⟩).2.cells seed) =
      evalCircuit quantizedLayer
        ((BitVec.ofNat 8 (seed 0), BitVec.ofNat 8 (seed 1)),
         (BitVec.ofNat 8 (seed 2), BitVec.ofNat 8 (seed 3))) := by
  exact compile_correct quantizedLayer ((0, 1), (2, 3)) ⟨4, []⟩ seed
    (by change (0 < 4 ∧ 1 < 4) ∧ (2 < 4 ∧ 3 < 4); decide)

end QuantCert.Tests

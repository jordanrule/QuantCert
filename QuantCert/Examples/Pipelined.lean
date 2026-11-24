import QuantCert.SequentialRTL
import QuantCert.Examples.QuantizedLayer

namespace QuantCert.Examples

/-! ### Weight ROM

A 4-bit address selects an INT8 weight from a 12-entry table; addresses 12-15 read zero. -/

def addr4 : QType := ⟨4, by decide, 1, by decide, false⟩

def weights : List Int := [-128, -100, -64, -32, -1, 0, 1, 7, 42, 77, 120, 127]

def weightRom : Prim (.word addr4) int8 :=
  .rom addr4 int8 weights (by decide +kernel)

/-- `acc = weights[addr] * activation`, combinational. -/
def romMac : Circuit (.word addr4 ⊗ .word int8) (.word accumulator) :=
  (Circuit.prim weightRom *** Circuit.id) >>> qMul

theorem weights_fit : RomFits int8 weights := by
  unfold RomFits weights; decide +kernel

theorem weight_read_exact (k : Nat) (hk : k < 16) :
    wordInt int8 (BitVec.ofInt 8 (weights.getD k 0)) = weights.getD k 0 := by
  have h : ∀ k : Fin 16, wordInt int8 (BitVec.ofInt 8 (weights.getD k 0)) = weights.getD k 0 := by
    unfold weights wordInt; decide +kernel
  exact h ⟨k, hk⟩

/-- For every address and activation bit pattern: the product of the stored weight (zero
beyond the table) and the activation, exactly. -/
theorem romMac_exact (a : BitVec 4) (x : BitVec 8) :
    (evalCircuit romMac (a, x)).toInt = weights.getD a.toNat 0 * x.toInt := by
  have hw := weight_read_exact a.toNat (by have := a.isLt; simpa [addr4] using this)
  have hw' : (BitVec.ofInt 8 (weights.getD a.toNat 0)).toInt = weights.getD a.toNat 0 := hw
  have h := mul_register_exact (BitVec.ofInt 8 (weights.getD a.toNat 0)) x
  rw [hw'] at h
  show (BitVec.ofInt 32 (wordInt int8 (BitVec.ofInt 8 (weights.getD a.toNat 0)) *
      wordInt int8 x)).toInt = _
  rw [hw, show wordInt int8 x = x.toInt from rfl]
  exact h

/-! ### Pipelined designs -/

/-- Registers after the ROM and the multiplier; the activation path is delay-matched. -/
def pipelinedRomMac : Pipe (.word addr4 ⊗ .word int8) (.word accumulator) :=
  pipeline cutHeavy romMac

/-- Registers after multipliers and the requantizer. -/
def pipelinedLayer : Pipe (rowType 1) (.word output8) :=
  pipeline cutHeavy quantizedLayer

example : pipelinedRomMac.latency = 2 := by decide +kernel
example : pipelinedLayer.latency = 2 := by decide +kernel

/-- Reset-to-output refinement for the ROM MAC: from any power-up state, once reset has been
applied and released, outputs after two cycles are exactly the combinational result. -/
theorem pipelinedRomMac_correct (s0 : PState pipelinedRomMac) (rst : Nat → Bool)
    (x : Nat → Value (.word addr4 ⊗ .word int8))
    (h0 : rst 0 = true) (hr : ∀ t, 0 < t → rst t = false) (t : Nat) (ht : 3 ≤ t) :
    (pipelinedRomMac.output s0 rst x t).toInt =
      weights.getD (x (t - 2)).1.toNat 0 * (x (t - 2)).2.toInt := by
  have hl : pipelinedRomMac.latency = 2 := by decide +kernel
  have h : pipelinedRomMac.output s0 rst x t =
      evalCircuit romMac (x (t - pipelinedRomMac.latency)) :=
    pipeline_correct cutHeavy romMac s0 rst x h0 hr t (by change pipelinedRomMac.latency + 1 ≤ t; omega)
  rw [h, hl]
  exact romMac_exact _ _

theorem pipelinedLayer_correct (s0 : PState pipelinedLayer) (rst : Nat → Bool)
    (x : Nat → Value (rowType 1))
    (h0 : rst 0 = true) (hr : ∀ t, 0 < t → rst t = false) (t : Nat) (ht : 3 ≤ t) :
    pipelinedLayer.output s0 rst x t = evalCircuit quantizedLayer (x (t - 2)) := by
  have hl : pipelinedLayer.latency = 2 := by decide +kernel
  have h : pipelinedLayer.output s0 rst x t =
      evalCircuit quantizedLayer (x (t - pipelinedLayer.latency)) :=
    pipeline_correct cutHeavy quantizedLayer s0 rst x h0 hr t
        (by change pipelinedLayer.latency + 1 ≤ t; omega)
  rw [h, hl]

end QuantCert.Examples

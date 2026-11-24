import QuantCert.Examples.Pipelined

namespace QuantCert.SequentialTests
open Examples

/-- Cycle-accurate simulation of the clocked semantics: input stream, reset stream, start state. -/
def simulate (p : Pipe a b) (s0 : PState p) (rst : Nat → Bool) (x : Nat → Value a)
    (n : Nat) : List (Value b) :=
  (List.range n).map (p.output s0 rst x)

def rstFirst : Nat → Bool := fun t => t == 0

-- Memory reads: in range, at the last entry, and beyond the table depth.
#guard (evalPrim weightRom 0#4).toInt == -128
#guard (evalPrim weightRom 11#4).toInt == 127
#guard (evalPrim weightRom 12#4).toInt == 0
#guard (evalPrim weightRom 15#4).toInt == 0
#guard (evalCircuit romMac (2#4, BitVec.ofInt 8 (-3))).toInt == 192

-- Latency and delay matching: the activation path gets a register to match the ROM register.
#guard pipelinedRomMac.latency == 2
#guard pipelinedLayer.latency == 2
#guard (pipeline cutEvery quantizedLayer).latency == 4
#guard (pipeline cutHeavy (Circuit.id : Circuit (.word int8) _)).latency == 0

def fill : (t : WireType) → Nat → Value t
  | .unit, _ => ()
  | .word _, n => BitVec.ofNat _ n
  | .prod a b, n => (fill a n, fill b (n + 1))

/-- Arbitrary non-reset register contents, as at power-up. -/
def scramble : (p : Pipe a b) → Nat → PState p
  | .comb _, _ => ()
  | @Pipe.reg a _, n => fill a (n * 97 + 13)
  | .seq p q, n => (scramble p n, scramble q (n + 1))
  | .par p q, n => (scramble p n, scramble q (n + 1))

def layerInput (t : Nat) : Value (rowType 1) :=
  ((BitVec.ofInt 8 (t + 3), BitVec.ofInt 8 5), (BitVec.ofInt 8 (-7), BitVec.ofInt 8 t))

def romInput (t : Nat) : Value (.word addr4 ⊗ .word int8) :=
  (BitVec.ofNat 4 (t * 5), BitVec.ofInt 8 (t * 11 - 40))

/-- After one reset edge and `latency` cycles, outputs match the combinational circuit
regardless of the power-up contents. -/
def agrees (p : Pipe a b) (c : Circuit a b) (x : Nat → Value a) (seed : Nat)
    [BEq (Value b)] : Bool :=
  (List.range 12).all fun t =>
    t < p.latency + 1 ||
      p.output (scramble p seed) rstFirst x t == evalCircuit c (x (t - p.latency))

instance : BEq (BitVec n) := ⟨fun a b => a.toNat == b.toNat⟩

#guard (List.range 6).all (fun seed => agrees pipelinedRomMac romMac romInput seed)
#guard (List.range 6).all (fun seed => agrees pipelinedLayer quantizedLayer layerInput seed)

end QuantCert.SequentialTests

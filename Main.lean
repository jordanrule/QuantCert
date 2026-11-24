import QuantCert.Examples.QuantizedLayer
import QuantCert.RTLTests
import QuantCert.Examples.Pipelined

private def emit (name : String) (c : QuantCert.Circuit a b) : IO Unit := do
  let rtl ← match QuantCert.toVerilogChecked name c with
    | .ok text => pure text
    | .error message => throw (IO.userError message)
  IO.print rtl

private def emitSeq (name : String) (p : QuantCert.Pipe a b) : IO Unit := do
  let rtl ← match QuantCert.toVerilogSeqChecked name p with
    | .ok text => pure text
    | .error message => throw (IO.userError message)
  IO.print rtl

def main : IO Unit := do
  emit "quantized_layer" QuantCert.Examples.quantizedLayer
  emit "certified_model" QuantCert.Model.Examples.classifier.lower
  emit "primitive_regressions" QuantCert.RTLTests.primitiveRegressions
  emit "rom_mac" QuantCert.Examples.romMac
  emitSeq "pipelined_layer" QuantCert.Examples.pipelinedLayer
  emitSeq "pipelined_rom_mac" QuantCert.Examples.pipelinedRomMac

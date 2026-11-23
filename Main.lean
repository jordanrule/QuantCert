import QuantCert.Examples.QuantizedLayer
import QuantCert.RTLTests

private def emit (name : String) (c : QuantCert.Circuit a b) : IO Unit := do
  let rtl ← match QuantCert.toVerilogChecked name c with
    | .ok text => pure text
    | .error message => throw (IO.userError message)
  IO.print rtl

def main : IO Unit := do
  emit "quantized_layer" QuantCert.Examples.quantizedLayer
  emit "certified_model" QuantCert.Model.Examples.classifier.lower
  emit "primitive_regressions" QuantCert.RTLTests.primitiveRegressions

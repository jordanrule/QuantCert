import QuantCert.Examples.QuantizedLayer

def main : IO Unit := do
  let rtl ← match QuantCert.toVerilogChecked "quantized_layer"
      QuantCert.Examples.quantizedLayer with
    | .ok text => pure text
    | .error message => throw (IO.userError message)
  IO.print rtl

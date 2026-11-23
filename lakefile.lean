import Lake
open Lake DSL

package QuantCert where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib QuantCert

@[default_target]
lean_exe emit where
  root := `Main

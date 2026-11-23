#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null || { echo "lake is required (install Lean using elan)." >&2; exit 1; }
command -v yosys >/dev/null || { echo "yosys is required for RTL verification." >&2; exit 1; }
mkdir -p build
lake build
lake env lean -DwarningAsError=true --run Main.lean > build/example-output.txt
lake env lean -DwarningAsError=true scripts/Audit.lean > build/axioms.txt
if grep -E 'sorryAx|Lean.ofReduceBool' build/axioms.txt; then
  echo "Unexpected proof axiom in certificate audit." >&2
  exit 1
fi
.lake/build/bin/emit > build/designs.v
cmp build/example-output.txt build/designs.v
yosys -Q -T -l build/yosys.log scripts/verify.ys

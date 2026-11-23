# QuantCert

Licensed under the [MIT License](LICENSE). Copyright (c) 2026 Jordan Rule.

## Why this is useful before an AI inference chip tapes out

An inference chip can produce plausible but wrong answers when an accumulator
wraps, a negative number is shifted incorrectly, a quantization scale is
misconnected, or a compiler swaps two wires. Those mistakes can survive ordinary
simulation: testing a few images does not exercise every possible activation
and weight. Discovering them after tape-out can mean an expensive silicon respin.

QuantCert is a small example of attaching **mathematical receipts** to the
arithmetic and compilation steps before sending RTL into a chip implementation
flow. Engineers can justify register widths, track the real value represented
by each integer, bound rounding error, and establish that a structural compiler
preserves a circuit's behavior. An independent Yosys equivalence check also
checks the generated example's Verilog across **all input bit patterns**, rather
than a collection of test vectors.

This is a building block for tape-out assurance, **not tape-out sign-off**.
It does not verify model accuracy, timing closure, clocks, reset, CDC, memories,
power, physical design, DFT, or foundry rules. It is a combinational DSL, without
cycle-level scheduling or register insertion.

## Typed Pipes with Mathematical Receipts

```text
  Two (INT8 activation, INT8 weight) pairs
       scales: 1/128 for each operand
                     |
           qMatMul: signed products
             + INT32 accumulation
              scale: 1/16384
                     |
           hwRequantize: (acc + 256) >>> 9
                  INT8, scale: 1/32
                     |
                  qReLU
                     |
              one INT8 output

  typed Circuit AST --fresh-wire compiler--> flat structural Netlist
          |                                        |
      evalCircuit                              evalNetlist
          +------------- compile_correct ----------+
                                                   |
                                              toVerilog
                                                   |
                                      Yosys equivalence + synthesis
```

`Circuit a b` describes a typed hardware morphism. `>>>` connects compatible
bundles in sequence; `***` puts circuits in parallel; `&&&` duplicates an input
bundle and sends it to two circuits. Products, swaps, duplication, dropping,
projections, associators, and unitors are structural wiring, not hidden cells.
NAND supports gate-level circuits; signed multiply, add, requantization, and
ReLU support word-level circuits. `qMatMul n` constructs one row with `n + 1`
variable activation/weight pairs; the demo chooses two terms. Multiple rows can
be built with fanout and parallel composition.

`QType` is `QuantParams`: a strictly positive bit width and rational scale with
a positivity proof. Composition checks the whole wire type, including its
scale. Multiplication carries a product-scale equality. Requantization carries
`RequantParams`, including a checked approximation receipt for the actual ratio
of the input and output scales. No `mathlib`, external Lake packages, real-number
library, or floating-point calculation is required.

The AST is not quotiented: category laws are **extensional equalities of
denotations**, not equalities of syntax trees. The checked laws include category
identities/associativity, tensor interchange/identity, natural symmetry,
associator inverses/naturality, pentagon, hexagon, triangle, unit inverses, and
the Cartesian product and terminal-object equations.

## Machine-checked properties

All theorems are fully proved in Lean, with no `sorry`, custom axioms, or
`native_decide`. Constant receipts use `decide +kernel`; arithmetic proofs use
standard-library lemmas, `omega`, and `grind`.

| Receipt | What it establishes |
|---|---|
| `dotProduct_no_overflow` | For `K` pairs with both operands in `[-128,127]`, the exact dot product fits signed `W` bits if `W > 0` and `K * 16384 < 2^(W-1)`. |
| `dotProduct_register_exact` | Under the same hypotheses, storing the sum in `BitVec W` and reading it as signed `Int` returns the exact sum. |
| `hwRequantize_approx` | `abs(result - acc * realScale) <= abs(acc) * deltaScale + 1`, for every signed integer accumulator and multiplier and every natural shift. |
| `requantParams_stored_approx` | The error bound transfers to a narrowed bit-vector output when its signed range hypotheses hold. |
| `compile_correct` | Running the flat compiled assignments produces exactly `evalCircuit`, for every circuit, initial store, and typed input reference bundle below the fresh-wire counter. |
| `qMatMul_exact`, `layer_narrowing_safe`, `layer_exact` | The actual two-term demo never wraps in its products, accumulator, or INT8 narrowing, and implements the exact rounded-and-ReLU integer formula for every input. |

For the requantization theorem, `realScale = num / den`, `den > 0`,
`D = 2^shift`, and `deltaScale = delta / den`. The exact approximation hypothesis
is `abs(M * den - num * D) <= delta * D`, equivalent to
`abs(M/D - realScale) <= deltaScale`. The hardware integer result is
`(acc * M + floor(D/2)) / D`, using Euclidean division, which is signed
arithmetic right shift for a positive power-of-two divisor. Ties round toward
positive infinity, including negative ties; shift zero needs no rounding.
The bound is in output **integer units**; multiply by the output scale to
interpret it in real-value units.

The proof also exposes the denominator-cleared integer version as
`hwRequantize_approx_cleared`. The demo's multiplier is `1`, shift is `9`, and
scale ratio is exactly `1/512`, so its scale approximation error is zero.
Its sum lies in `[-32768,32768]`, the rounded result fits INT8, and the final
output is in `[0,64]`. The generic accumulator certificate applies to prefixes
as well, so a checked row length bounds its partial sums. Larger rows require
their own capacity receipt; their construction alone does not prove safety.

### Semantic and verification boundaries

Wire values are `BitVec`s. Arithmetic primitives wrap on storage; **they do
not saturate**. `quantize` rounds a rational value and wraps to the requested
width; `dequantize` reads a signed integer and multiplies by its scale. The
error theorem for unbounded integer requantization does not by itself justify
arbitrary narrowing: use the stored-output theorem and prove its range
hypotheses, as the example does.

The compiler is a `StateM Netlist` computation, exposed as
`compile : Circuit a b -> WireEnv a -> Netlist -> (WireEnv b × Netlist)`.
Typed input/output environments are trees of `WireId`s; the cell list is flat.
Cells are stored in reverse topological order and evaluated/printed in
topological order. The compiler invariant proves fresh output allocation,
counter monotonicity, preservation of existing wires, and semantic agreement.
Requantization RTL uses an explicitly widened signed product/rounding temporary
so the expression cannot overflow before its arithmetic shift.

`compile_correct` is a general Lean proof about the **structural netlist
semantics**, whose primitive meaning is shared with the DSL. It is not a
Lean proof of the Verilog parser, printer, or Yosys. The separate Yosys run checks
the emitted two-term example against `scripts/reference.sv`, an independently
written signed-arithmetic specification. Its eight output bits are proven
equivalent for all four INT8 inputs (32 input bits), and the design is
synthesized and checked for structural problems. This does not certify every
possible circuit's printed Verilog.

## Build and print Verilog

Install [Lean using elan](https://lean-lang.org/install/) and ensure `lake` is
on `PATH`. `lean-toolchain` pins stable Lean **4.24.0**. Lake downloads that
toolchain if necessary; there are **zero external Lean dependencies**.

```sh
lake build
lake env lean QuantCert/Examples/QuantizedLayer.lean
mkdir -p build
.lake/build/bin/emit > build/quantized_layer.v
```

Both the example's `#eval IO.print` and the `emit` executable print plain
synthesizable Verilog, without quoted string escapes. The example module has
four signed INT8 inputs `w0` through `w3` and one signed INT8 output `out0`.
Pass a legal, non-keyword Verilog module name to `toVerilog`;
`toVerilogChecked` additionally checks identifier spelling.
Warnings are treated as errors in the Lake configuration.

## Run the Yosys verification

Yosys is an **optional external RTL tool**, not a Lean dependency. Install it,
for example with `brew install yosys` on macOS, then run:

```sh
bash scripts/verify.sh
```

The script fails on any build, proof-audit, output-comparison, equivalence, or
structural-check failure. It builds every module and the edge-case regression
checks, executes the example, audits theorem axioms, emits the RTL, compares
both emission paths byte-for-byte, runs `equiv_simple` / `equiv_status -assert`,
and synthesizes the generated design with `check -assert`.

To rerun just the RTL check after emission:

```sh
yosys -Q -T -l build/yosys.log scripts/verify.ys
```

**Verified run:** Lean 4.24.0 and Yosys 0.69+post on macOS. `lake build`
and the example completed with zero errors and zero warnings. Yosys reported
`8 are proven and 0 are unproven`, `Equivalence successfully proven!`, and
`Found and reported 0 problems.` The check is combinational: no assumptions,
bounded cycle count, or stimulus file constrain the input space.

Generated artifacts are ignored by Git:
`build/quantized_layer.v`, `build/example-output.txt`, `build/axioms.txt`, and
`build/yosys.log`. The axiom audit permits Lean's standard logical axioms and
rejects `sorryAx` and native-evaluation proof axioms.

## Source map

| Module/file | Responsibility |
|---|---|
| `QuantCert/Core.lean` | Typed circuit syntax, primitives, denotation, categorical laws |
| `QuantCert/Quant.lean` | Rational quantization metadata, numerical receipts |
| `QuantCert/Compiler.lean` | Fresh-wire structural compilation, Verilog emission |
| `QuantCert/Semantics.lean` | Operational netlist evaluation and compiler proof |
| `QuantCert/Examples/QuantizedLayer.lean` | Quantized row demo and its end-to-end receipts |
| `QuantCert/Tests.lean` | Signed extremes, rounding ties, gate and wiring regression checks |
| `scripts/Audit.lean` | Certificate axiom audit |
| `scripts/reference.sv`, `scripts/verify.ys`, `scripts/verify.sh` | Independent RTL reference and reproducible Yosys verification |

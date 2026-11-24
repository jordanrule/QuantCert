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
preserves a circuit's behavior. The **fixed-weight model frontend** represents
shape-typed affine/ReLU networks, quantizes their parameters, checks intermediate
widths, and bounds end-to-end error against a rational reference model. It lowers
to the **same `Circuit` AST, compiler, netlist, and Verilog emitter** as directly
written circuits. One verification command builds the proofs and checks both
examples' generated RTL against independent specifications across **all input
bit patterns**, rather than a collection of test vectors:

```sh
bash scripts/verify.sh
```

The proofs cover the **most critical aspects of functional assurance**: bit-exact
arithmetic (widths, wrapping, rounding, signedness), quantization error bounds,
compiler correctness, **pipelining that provably preserves behavior across clock
cycles**, a defined synchronous reset, and ROM weight-table reads. These are the
failure modes that simulation cannot exhaust and that are most expensive to find
after silicon. This is **not tape-out sign-off**: see
[What tape-out sign-off still requires](#what-tape-out-sign-off-still-requires).

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

  Fixed-weight QuantNetwork --lower--> typed Circuit AST
                                          ^
  Directly written circuits --------------+

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
NAND supports gate-level circuits; multiply, add, requantization, ReLU,
constants, zero-point subtraction/resizing, shifts, and clamping support
word-level circuits. `qMatMul n` constructs one row with `n + 1`
variable activation/weight pairs; the demo chooses two terms. Multiple rows can
be built with fanout and parallel composition.

`QType` is `QuantParams`: a strictly positive bit width, a positive rational
scale, and signed/unsigned interpretation (signed by default). Composition checks
the whole wire type, including its scale and signedness. Multiplication carries
a product-scale equality. Requantization carries
`RequantParams`, including a checked approximation receipt for the actual ratio
of the input and output scales. No `mathlib`, external Lake packages, real-number
library, or floating-point calculation is required.

The AST is not quotiented: category laws are **extensional equalities of
denotations**, not equalities of syntax trees. The checked laws include category
identities/associativity, tensor interchange/identity, natural symmetry,
associator inverses/naturality, pentagon, hexagon, triangle, unit inverses, and
the Cartesian product and terminal-object equations.

## Pipelining, reset and ROM

`Pipe a b` (`QuantCert/Sequential.lean`) is a single-clock, single synchronous
active-high reset layer over `Circuit`: `comb`, `reg init`, `seq`, `par`.
`pipeline cut c` cuts any `Circuit` into stages, placing a register bank after each
primitive selected by a `CutPolicy` (`cutEvery`, `cutHeavy` = multipliers,
requantizers, ROMs), and pads shorter parallel branches with zero-reset delay
registers so all paths have equal latency. Registers reset to zero.

Two semantics are given and related: a stream denotation (`Pipe.sem`) and a clocked
operational one (`Pipe.step`/`Pipe.run`, a Mealy machine with explicit register
state and `rst`).

| Receipt | What it establishes |
|---|---|
| `pipeline_realizes` | `pipeline cut c` computes `evalCircuit c` with exactly `latency` cycles of delay, for every circuit and policy. |
| `Pipe.step_reset` | One reset edge puts every register at its reset value, whatever it held and whatever the inputs were. |
| `pipeline_correct` | From **any** power-up register contents, with reset asserted on cycle 0 and released, from cycle `latency + 1` onward the clocked output equals the combinational circuit's output on the input from `latency` cycles earlier. |
| `rom_read_in_range`, `rom_read_out_of_range`, `Examples.romMac_exact` | `Prim.rom` reads the table entry for in-range addresses and zero for addresses past the table; the weight-ROM MAC returns `weights[addr] * activation` exactly for all 4-bit addresses and INT8 activations. |
| `Examples.pipelinedRomMac_correct`, `pipelinedLayer_correct` | The two instances of the above for the shipped designs (latency 2 each). |

ROM addresses are the raw unsigned address bits; a `depth_ok` receipt bounds the table
by `2^addressWidth`. Entries wrap to the data width unless `RomFits` is shown.
Outputs during the first `latency` cycles after reset reflect reset values flowing
through later stages and are intentionally **not** claimed to be meaningful;
consumers must ignore them (or gate with a valid bit). Reset applied mid-stream is
covered only for `step_reset`; `pipeline_correct` states the single-reset-at-start case.

`toVerilogSeq` emits `clk`/`rst` ports, plain `always @(posedge clk)` registers with
synchronous reset and no initial blocks, and ROMs as equality-chain `assign`s. As with
`toVerilog`, the **printer is not proved**; Yosys checks stand in (below). Sequential
netlist compilation has no analogue of `compile_correct`.

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
| `Model.Format.encode_error` | Saturating input encoding has at most half an LSB error on the explicitly stated representable real domain. |
| `Model.QuantNetwork.outputRange_sound` | Automatically propagated integer intervals enclose every network output for every input in the supplied code box. |
| `Model.QuantNetwork.machineEval_exact` | A checked `Safe` certificate makes execution with bit-vector storage at every specified arithmetic intermediate equal to unbounded integer execution. |
| `Model.QuantNetwork.encodedError_sound` | Input encoding and finite-width network execution differ from the rational reference by at most the automatically composed per-output error budget. |
| `Model.QuantNetwork.lower_correct` | Lowering any quantized network to `Circuit` preserves its finite-width semantics for every input bit pattern, even when widths wrap. |
| `Model.QuantNetwork.compile_correct`, `compiledError_sound` | The shared netlist compiler preserves network behavior and carries the model error bound through to operational netlist outputs. |
| `Model.Examples.classifier_compiled_error` | The compiled two-layer scalar-output example has absolute real-value output error at most `1/3` throughout the real input box `[-1,1]^2`, given correctly encoded input wires. |

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

### Shared RTL semantics and verification boundaries

All frontend paths use `Circuit` wire values represented as `BitVec`s.
Arithmetic primitives wrap on storage; **saturation is an explicit `clip`
operation**, not an implicit property of multiplication or narrowing. The
low-level `quantize` rounds a rational value and wraps to the requested width;
`dequantize` reads according to the wire's signedness and multiplies by its scale.
The model frontend instead inserts explicit zero-point and clamping operations.
The error theorem for unbounded integer requantization does not by itself justify
arbitrary narrowing: use the stored-output theorem and prove its range
hypotheses, as the example does.

The compiler is a `StateM Netlist` computation, exposed as
`compile : Circuit a b -> WireEnv a -> Netlist -> (WireEnv b × Netlist)`.
Typed input/output environments are trees of `WireId`s; the cell list is flat.
Cells are stored in reverse topological order and evaluated/printed in
topological order. The compiler invariant proves fresh output allocation,
counter monotonicity, preservation of existing wires, and semantic agreement.
The shared printer explicitly sign-extends or zero-extends inputs before
multiplication and zero-point arithmetic. The low-level requantization primitive
uses a widened product/rounding temporary. Model lowering instead exposes its
specified accumulator and temporary widths as ordinary arithmetic cells, so the
same wrapping points used in its proofs appear in RTL.

`compile_correct` is a general Lean proof about the **structural netlist
semantics**, whose primitive meaning is shared with the DSL. It is not a
Lean proof of the Verilog parser, printer, or Yosys. The Yosys run checks the
two-product circuit, the lowered two-layer network, and a primitive regression
module against independently written specifications in `scripts/reference.sv`.
Every module is synthesized and checked for structural problems. These
instance-level checks do not certify every possible circuit's printed Verilog.

## Fixed-weight model and quantization proofs

The model is a frontend to the shared combinational RTL DSL, not a second
backend or a separate model-only execution path:

```text
Fixed rational weights + biases + affine/ReLU network + rational input box
             |                              |
        Layer.quantize                 Network.eval
             |                         ideal rational output
     QuantNetwork + integer ranges          |
             |                              |
       lower_correct                        |
             v                              |
     Circuit -> compile -> Netlist          |
             |                              |
     decode netlist outputs ----------------+-- per-output real error bound
             |
       shared toVerilog
             |
   Yosys equivalence + synthesis
```

`Model.Layer n m` stores fixed rational weights and biases and an identity or
ReLU activation. Tensors are functions on `Fin n`/`Fin m`, so incompatible
dimensions cannot be composed and dot products cannot silently truncate.
`Model.Network` composes layers of arbitrary dimensions. Its interpretation is
exact rational arithmetic, **not FP32 execution or an imported trained model**.

### Explicit deployment arithmetic

`Model.Format` specifies a positive width, signed or unsigned storage, a positive
rational scale, and an in-range zero point. Its real interpretation is
`(code - zeroPoint) * scale`. `Format.encode` rounds to nearest with ties toward
positive infinity and **saturates**, unlike the old DSL's wrapping `quantize`.
Both negative ties and signed/unsigned endpoints are covered by regressions.
There is no TensorFlow Lite, ONNX, or other framework-compatibility claim.

`Layer.quantize` constructs a quantized layer from the supplied reference:

- Activations have a uniform format at each layer boundary; weight formats,
  including scales and zero points, are per output channel.
- Weights are encoded with rounding and saturation. Bias is rounded at scale
  `input.scale * weightFormat[channel].scale`, with zero point zero. Bias is not
  silently clipped: insufficient accumulator capacity rejects the certificate.
- A caller chooses each channel's shift. The multiplier is rounded from the
  exact scale ratio times `2^shift`. Analysis measures its actual discrepancy;
  it does not assume the ratio is exactly representable.
- Integer execution accumulates centered products, adds bias, computes
  `(acc * multiplier + floor(2^shift / 2)) / 2^shift`, applies the activation,
  adds the output zero point, and saturates to the output storage range.

Different layers may have different activation formats, but a quantized network
boundary must match exactly. Per-channel **activation** scales, convolutions,
nonlinear activations other than ReLU, and framework import are not implemented.

### Automatically checked width certificates

`QuantLayer.productRange`, `accRange`, `mulRange`, `tempRange`, `roundRange`,
`preClampRange`, and `outputRange` compute inclusive integer intervals from an
input code box and the actual fixed weights. Negative coefficients and
zero-point subtraction are included. `QuantNetwork.outputRange` propagates these
intervals through every layer.

`QuantLayer.Safe` checks centered operand widths, each product, the bias, every
suffix sum in the specified right-associated dot product, the final bias
addition, the multiplier, the rounding constant, the widened multiplication
and rounding addition, the shifted value, and the zero-point addition.
`QuantNetwork.Safe` checks this recursively using each preceding layer's output
ranges. The input ranges must also be ordered and lie inside their format.
For a concrete model, `by decide +kernel` constructs the certificate without
hand-written arithmetic proofs. `decide (net.Safe ranges)` provides an
executable yes/no check; individual ranges and `IntRange.fits` locate rejected
widths.

`machineEval_exact` connects these checks to an explicit finite-width
interpreter: centered operands and products are stored at accumulator width,
every dot-product addition and bias are stored, requantization operations are
stored at temporary width, and saturated outputs are stored/read using their
signed or unsigned format. Centered subtractions must be widened before
multiplication. The proof covers this accumulation order, **not arbitrary
reassociation or a different implementation**. Certificate rejection means
“not certified”; interval overapproximation is not an overflow counterexample.
Safety is conditional on the declared input box, not merely observed
calibration minima/maxima.

### Compositional error budgets

`QuantLayer.outputError` and `QuantNetwork.outputError` compute bounds in
**real-value units**, per output channel. The layer budget is:

```text
|decodedBias - idealBias|
+ sum_i (|idealWeight_i| * inputError_i
         + |decodedWeight_i - idealWeight_i| * decodedInputMagnitude_i)
+ outputScale
+ accumulatorMagnitude * |outputScale * multiplier / 2^shift - accumulatorScale|
+ outputScale * worstClippingDistanceInCodes
```

Input encoding contributes half an input LSB when the real input is within its
format's representable interval. The requantization rounding allowance is a
conservative **one output LSB**; shift zero is supported too. Weight/bias
mismatch, multiplier approximation, rounding, and output clipping are all
accounted for. ReLU is proved nonexpansive, so these bounds compose without
adding an activation-error term. Output clipping is included even when it is
intentional; it is not confused with an unsafe intermediate wrap.

`encodedError_sound` connects rational input encoding, finite-width execution,
and the rational reference in one theorem, with explicit input-domain and
`Safe` hypotheses. `outputError_sound` also accepts an externally supplied
input-error bound, for integration with another input encoder. Bounds can be
loose: this is interval/magnitude analysis, not a correlation-aware neural
network verifier. It does not prove classification accuracy, robustness,
decision preservation, or equivalence to a floating-point runtime.

### One lowering and compilation pipeline

`QuantNetwork.lower` expands a network into ordinary `Circuit` composition,
fanout, projections, constants, multiplication, addition, shifts, ReLU, offsets,
and clips. It does **not** embed an opaque model cell or invoke a model-specific
Verilog printer. `QuantLayer.productCircuit`, `accCircuit`, `roundCircuit`, and
`neuronCircuit` expose the lowering for inspection.
Internal arithmetic wires use scale-one raw integer types; the model's scale
receipts establish their real interpretation. Boundary wires retain their
format's width, scale, and signedness, while zero points become explicit
arithmetic rather than implicit wire metadata.

`lower_correct` connects this expansion to the finite-width reference
interpreter for every input bit pattern; no `Safe` premise is needed just to
preserve wrapping behavior. `QuantNetwork.compile_correct` then applies the
existing generic `compile_correct` theorem. `compiledError_sound` combines this
with range and error receipts for the rational reference model.
`machineEval` remains an executable reference semantics used in these proofs,
not an alternative compilation or RTL path.

The public hardware interface is integer codes: **rational input encoding is a
host-side operation**, not generated hardware. Unsigned ports retain their
actual width and unsigned declarations; centering explicitly widens them before
subtracting zero points. The compiled error theorem assumes the input wires
contain the specified encoded inputs.

### Worked two-layer model

`QuantCert/Examples/CertifiedModel.lean` defines a fixed `2 -> 2 -> 1` network
with a hidden ReLU, unsigned activation storage, signed output storage, nonzero
zero points, and two different weight formats in the first layer. Its weights
and biases include values that quantization cannot represent exactly; the
second layer also has nonzero multiplier approximation error.

For **every rational input in `[-1,1]^2`**, the example proves that the stored
implementation has absolute output error at most **`1/3`** against its rational
reference. Its encoded input box is `[112,144]^2`, and its final output codes
are in `[-7,4]`. The certificate rejects separate variants with an 8-bit
accumulator or an 8-bit requantization temporary.
The first layer also has a certified 9-bit accumulator / 12-bit temporary
variant. An 11-bit temporary fits its multiplication but fails the subsequent
rounding addition: that temporary's interval reaches `1032`, above signed
11-bit maximum `1023`.

To inspect or adapt the example in a Lean file:

```lean
import QuantCert.ModelTests
open QuantCert.Model QuantCert.Model.Examples

#eval decide (classifier.Safe inputBox)
#eval first.accRange inputBox 1
#eval classifier.outputRange inputBox 0
#eval classifier.outputError inputBox (fun _ => input8.scale * ((1 : Rat) / 2)) 0
#check classifier_compiled_error
#eval QuantCert.toVerilog "my_model" classifier.lower
```

`classifier_compiled_error` carries the `1/3` error receipt through to the
shared compiled netlist. `classifier_full_codes_safe` additionally proves
intermediate safety over the complete unsigned input code domain `[0,255]^2`.
The emitted `certified_model` is independently checked by Yosys on **all 65,536
input combinations**, without constraining the check to the smaller input box.
The `1/3` model-error guarantee still applies only on `[-1,1]^2`.

## Build and print Verilog

Install [Lean using elan](https://lean-lang.org/install/) and ensure `lake` is
on `PATH`. `lean-toolchain` pins stable Lean **4.24.0**. Lake downloads that
toolchain if necessary; there are **zero external Lean dependencies**.

```sh
lake build
mkdir -p build
.lake/build/bin/emit > build/designs.v
```

`Main.lean` is the single emission entry point. The executable and
`lake env lean --run Main.lean` print the same plain synthesizable Verilog:

| Module in `build/designs.v` | Interface |
|---|---|
| `quantized_layer` | Four signed INT8 inputs `w0` through `w3`, one signed INT8 output `out0` |
| `certified_model` | Two unsigned INT8 inputs `w0`, `w1`, one signed INT8 output `out0` |
| `primitive_regressions` | Signed/unsigned arithmetic, narrow wrapping, saturation, large shifts, and a lowered bias-only layer |

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
checks (including model lowering, signed/unsigned formats, and width rejection),
audits arithmetic, compiler, lowering, and model theorem axioms, emits every
module through `Main.lean`, and compares interpreted and compiled execution of
that same emitter byte-for-byte. It runs `equiv_simple` /
`equiv_status -assert` for each module against its independent RTL reference,
then synthesizes each generated module with `check -assert`. Adding a different
model requires its own reference/equivalence check; the supplied RTL checks
cover the emitted examples, not arbitrary future models.

For sequential designs, `pipelined_rom_mac_check` (in `scripts/reference.sv`) wraps the
emitted pipeline, a delayed copy of the combinational `rom_mac`, and a post-reset age
counter; Yosys `sat -seq 4` proves they agree from an unconstrained power-up state once
reset has been applied (a bounded check of the emitted RTL, not an unbounded proof). The
`pipelined_layer` module is synthesized and structure-checked, but its two-multiplier
SAT miter did not finish in practical time, so its cycle behavior rests on the Lean
theorem `pipelinedLayer_correct` and the printer is unchecked for it.

To rerun just the RTL check after emission:

```sh
yosys -Q -T -l build/yosys.log scripts/verify.ys
```

The combinational checks use no assumptions, bounded cycle count, or stimulus file. The
sequential check is bounded to four cycles from an arbitrary power-up state.

Generated artifacts are ignored by Git:
`build/designs.v`, `build/example-output.txt`, `build/axioms.txt`, and
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
| `QuantCert/Sequential.lean` | `Pipe` (registers, reset), stream and clocked semantics, pipelining pass, refinement and reset theorems |
| `QuantCert/SequentialRTL.lean` | Sequential netlist items and Verilog emitter with `clk`/`rst` |
| `QuantCert/Examples/Pipelined.lean` | Weight-ROM MAC, pipelined ROM MAC and layer with correctness theorems |
| `QuantCert/SequentialTests.lean` | ROM reads, latencies, simulation from scrambled power-up state |
| `QuantCert/Tests.lean` | Signed extremes, rounding ties, gate and wiring regression checks |
| `QuantCert/Model.lean` | Shape-typed rational and quantized affine/ReLU networks, signed/unsigned affine formats, parameter quantization |
| `QuantCert/ModelRange.lean` | Executable interval propagation, width certificates, finite-width interpreter and exactness proof |
| `QuantCert/ModelError.lean` | Input-encoding error, parameter/multiplier/rounding/clipping error, compositional network theorem |
| `QuantCert/ModelLowering.lean` | Model-to-`Circuit` lowering, generic lowering/netlist correctness, compiled error preservation |
| `QuantCert/Examples/CertifiedModel.lean` | Fixed two-layer model, checked widths, real-input error guarantee, rejected narrow variants |
| `QuantCert/ModelTests.lean` | Affine-format endpoints/ties, per-channel parameters, nonzero error sources, network regression checks |
| `QuantCert/RTLTests.lean` | Lowering regressions and shared-backend RTL edge-case circuit |
| `Main.lean` | Single RTL emission entry point for all checked designs |
| `scripts/Audit.lean` | Certificate axiom audit |
| `scripts/reference.sv`, `scripts/verify.ys`, `scripts/verify.sh` | Independent RTL reference and reproducible Yosys verification |

## What tape-out sign-off still requires

QuantCert establishes *functional* intent at the arithmetic, RTL-semantics and
single-clock-pipeline level. Sign-off additionally needs the following. They are not
good targets for formalization here, because each depends on information outside the
RTL semantics (a foundry PDK, extracted physical data, analog/statistical behavior, a
vendor tool's proprietary model, or program-level process decisions) and verification
there is empirical, tool-driven, and re-run on every netlist or ECO, not a one-time
theorem.

| Sign-off item | Why it is not a formalization task |
|---|---|
| **Model accuracy on real data** | Depends on the dataset and task distribution, not on circuit arithmetic. We bound error against a given reference model only. Evaluation on held-out data is statistical. |
| **Timing closure** (STA, multi-corner/OCV) | Needs standard-cell libraries, parasitics and the placed/routed netlist; delays are numeric, process-dependent and change at every ECO. Latency in cycles is proved; nanoseconds are not. |
| **Multiple clocks, CDC, metastability** | Synchronizer MTBF is a probabilistic, physical property. This tool has one clock domain by construction. |
| **Reset in context** (async reset, release/removal timing, reset trees) | Recovery/removal is a timing property; the proof assumes the clean synchronous reset it defines. |
| **Real memories** (SRAM macros, BIST/repair, ECC) | Behavior comes from compiler-generated macros and silicon defects. Only the abstract, bounded-address ROM table is modeled. |
| **Power** (switching activity, IR drop, EM, thermal) | Analog/physical quantities driven by workloads and layout. |
| **Physical design** (floorplan, placement, routing, LVS) | Layout-level tool output checked against vendor decks; equivalence of the final netlist is checked by logic-equivalence tools. |
| **DFT** (scan, ATPG, test coverage) | Statistical fault-coverage metrics on the synthesized netlist; scan insertion changes the netlist. |
| **Foundry rules** (DRC, antenna, density, ESD, reliability) | Geometric rules in proprietary decks; only the foundry's qualified checkers carry sign-off authority. |
| **Verification of the toolchain** (Verilog printer, Yosys, synthesis) | A Lean proof covers the semantics here, not external tools; equivalence checking of the synthesized netlist against RTL is the pragmatic guard. |

Practically, use QuantCert's receipts as inputs to that flow: proven widths and
latencies feed the timing and floorplan constraints, and the generated RTL is the
reference for formal equivalence checking of the synthesized netlist.

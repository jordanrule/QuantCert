import QuantCert.Core

namespace QuantCert

abbrev WireId := Nat

/-- A typed tree of references into a flat wire store. -/
@[reducible] def WireEnv : WireType → Type
  | .unit => Unit
  | .word _ => WireId
  | .prod a b => WireEnv a × WireEnv b

structure Cell where
  inputType : WireType
  outputType : QType
  op : Prim inputType outputType
  inputs : WireEnv inputType
  output : WireId

/-- Cells are held in reverse topological order. `next` is the fresh-wire counter. -/
structure Netlist where
  next : WireId := 0
  cells : List Cell := []

/-- Wiring operations allocate nothing; only primitives emit cells. -/
def compileM : Circuit a b → WireEnv a → StateM Netlist (WireEnv b)
  | .id, e => pure e
  | .comp f g, e => do
      let m ← compileM f e
      compileM g m
  | .par f g, (e, d) => do
      let x ← compileM f e
      let y ← compileM g d
      pure (x, y)
  | .swap, (x, y) => pure (y, x)
  | .dup, e => pure (e, e)
  | .drop, _ => pure ()
  | .fst, (x, _) => pure x
  | .snd, (_, y) => pure y
  | .assoc, ((x, y), z) => pure (x, (y, z))
  | .unassoc, (x, (y, z)) => pure ((x, y), z)
  | .unitL, (_, x) => pure x
  | .unitLInv, x => pure ((), x)
  | .prim p, e => fun n =>
      (n.next, ⟨n.next + 1, ⟨_, _, p, e, n.next⟩ :: n.cells⟩)

def compile (c : Circuit a b) (e : WireEnv a) (n : Netlist) : WireEnv b × Netlist :=
  (compileM c e).run n

theorem compile_comp (f : Circuit a b) (g : Circuit b c) (e : WireEnv a) (n : Netlist) :
    compile (f >>> g) e n =
      let (mid, m) := compile f e n
      compile g mid m := rfl

theorem compile_par (f : Circuit a b) (g : Circuit c d) (e : WireEnv a × WireEnv c)
    (n : Netlist) :
    compile (f *** g) e n =
      let (left, m) := compile f e.1 n
      let (right, k) := compile g e.2 m
      ((left, right), k) := rfl

def Bounded : {a : WireType} → WireEnv a → Nat → Prop
  | .unit, _, _ => True
  | .word _, i, n => Nat.lt i n
  | .prod _ _, (x, y), n => Bounded x n ∧ Bounded y n

def wireName (i : WireId) : String := s!"w{i}"

def signedDecl (q : QType) : String := s!"signed [{q.bitWidth - 1}:0]"

/-- Allocate the module's leaf input ports before allocating internal cells. -/
def inputEnv : (a : WireType) → Nat → WireEnv a × Nat × List (WireId × QType)
  | .unit, n => ((), n, [])
  | .word q, n => (n, n + 1, [(n, q)])
  | .prod a b, n =>
      let (x, m, xs) := inputEnv a n
      let (y, k, ys) := inputEnv b m
      ((x, y), k, xs ++ ys)

def outputLeaves : (a : WireType) → WireEnv a → List (WireId × QType)
  | .unit, _ => []
  | .word q, i => [(i, q)]
  | .prod a b, (x, y) => outputLeaves a x ++ outputLeaves b y

def intLiteral (width : Nat) (x : Int) : String :=
  if x < 0 then s!"(-{width}'sd{x.natAbs})" else s!"{width}'sd{x.natAbs}"

/-- Explicit sign extension prevents Verilog expression sizing from truncating products. -/
def extend (q : QType) (width : Nat) (i : WireId) : String :=
  if width ≤ q.bitWidth then s!"$signed({wireName i})"
  else "$signed({{" ++ toString (width - q.bitWidth) ++ "{" ++
    wireName i ++ "[" ++ toString (q.bitWidth - 1) ++ "]}}, " ++ wireName i ++ "})"

def primRTL {a : WireType} {q : QType} (op : Prim a q) (inputs : WireEnv a)
    (output : WireId) : List String :=
  let dst := wireName output
  let decl := s!"  wire {signedDecl q} {dst};"
  match op, inputs with
  | .nand, (x, y) => [decl, s!"  assign {dst} = ~({wireName x} & {wireName y});"]
  | .mul a b out _, (x, y) =>
      let w := max out.bitWidth (a.bitWidth + b.bitWidth)
      [decl, s!"  assign {dst} = {extend a w x} * {extend b w y};"]
  | .add _, (x, y) =>
      [decl, s!"  assign {dst} = $signed({wireName x}) + $signed({wireName y});"]
  | .relu _, x =>
      [decl, s!"  assign {dst} = $signed({wireName x}) < 0 ? '0 : {wireName x};"]
  | .requant a _ receipt, x =>
      let M := receipt.multiplier
      let shift := receipt.shift
      let w := a.bitWidth + M.natAbs.log2 + shift + 3
      let tmp := s!"rq{output}"
      [decl, s!"  wire signed [{w - 1}:0] {tmp};",
       s!"  assign {tmp} = {extend a w x} * {intLiteral w M} + {intLiteral w ((2 ^ shift : Nat) / 2)};",
       s!"  assign {dst} = $signed({tmp}) >>> {shift};"]

def cellRTL (c : Cell) : List String := primRTL c.op c.inputs c.output

/-- Emit a combinational, flat, structural Verilog module (no clocks or behavioral blocks).
Names must be Verilog identifiers; `toVerilogChecked` validates untrusted names. -/
def toVerilog (name : String) (c : Circuit a b) : String :=
  let (ins, next, ports) := inputEnv a 0
  let (outs, net) := compile c ins ⟨next, []⟩
  let outputs := outputLeaves b outs
  let inDecls := ports.map fun (i, q) => s!"input wire {signedDecl q} {wireName i}"
  let outDecls := outputs.zipIdx |>.map fun ((_, q), k) =>
    s!"output wire {signedDecl q} out{k}"
  let header := s!"module {name}(\n  " ++ String.intercalate ",\n  " (inDecls ++ outDecls) ++ "\n);"
  let cells := net.cells.reverse.flatMap cellRTL
  let assigns := outputs.zipIdx |>.map fun ((i, _), k) =>
    s!"  assign out{k} = {wireName i};"
  String.intercalate "\n" ([header] ++ cells ++ assigns ++ ["endmodule", ""])

def toVerilogChecked (name : String) (c : Circuit a b) : Except String String :=
  if name.isEmpty || !(name.toList.head!.isAlpha || name.toList.head! == '_') ||
      !name.toList.all (fun ch => ch.isAlphanum || ch == '_') then
    .error "Module name must be a nonempty Verilog identifier."
  else .ok (toVerilog name c)

end QuantCert

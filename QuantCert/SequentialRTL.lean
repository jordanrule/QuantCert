import QuantCert.Sequential

namespace QuantCert

/-- A synchronous netlist item: a combinational cell or one reset-able register bit-vector. -/
inductive Item where
  | cell (c : Cell)
  | reg (q : QType) (dst src : WireId) (init : Nat)

/-- Items are held in reverse emission order. -/
structure SeqNet where
  next : WireId := 0
  items : List Item := []

def leafInits : (t : WireType) → Value t → List Nat
  | .unit, _ => []
  | .word _, v => [v.toNat]
  | .prod a b, (x, y) => leafInits a x ++ leafInits b y

/-- Combinational pieces reuse the verified fresh-wire compiler; each register leaf gets a fresh
output wire, its own source wire and reset value. -/
def compileP : Pipe a b → WireEnv a → SeqNet → WireEnv b × SeqNet
  | .comb c, e, n =>
      let (o, m) := compile c e ⟨n.next, []⟩
      (o, ⟨m.next, m.cells.map Item.cell ++ n.items⟩)
  | @Pipe.reg a init, e, n =>
      let (o, next, outs) := inputEnv a n.next
      let srcs := outputLeaves a e
      let regs := (outs.zip srcs).zip (leafInits a init) |>.map fun (((d, q), (s, _)), v) =>
        Item.reg q d s v
      (o, ⟨next, regs.reverse ++ n.items⟩)
  | .seq p q, e, n =>
      let (m, n₁) := compileP p e n
      compileP q m n₁
  | .par p q, e, n =>
      let (x, n₁) := compileP p e.1 n
      let (y, n₂) := compileP q e.2 n₁
      ((x, y), n₂)

def itemRTL : Item → List String
  | .cell c => cellRTL c
  | .reg q dst src init =>
      [s!"  reg {signedDecl q} {wireName dst};",
       s!"  always @(posedge clk) {wireName dst} <= rst ? {q.bitWidth}'d{init} : {wireName src};"]

/-- Emit one clock (`clk`) and one active-high synchronous reset (`rst`). Registers have no
initial block: reset is the only way they obtain a defined value. -/
def toVerilogSeq (name : String) (p : Pipe a b) : String :=
  let (ins, next, ports) := inputEnv a 0
  let (outs, net) := compileP p ins ⟨next, []⟩
  let outputs := outputLeaves b outs
  let inDecls := ports.map fun (i, q) => s!"input wire {signedDecl q} {wireName i}"
  let outDecls := outputs.zipIdx |>.map fun ((_, q), k) =>
    s!"output wire {signedDecl q} out{k}"
  let header := s!"module {name}(\n  " ++
    String.intercalate ",\n  " (["input wire clk", "input wire rst"] ++ inDecls ++ outDecls) ++ "\n);"
  let body := net.items.reverse.flatMap itemRTL
  let assigns := outputs.zipIdx |>.map fun ((i, _), k) =>
    s!"  assign out{k} = {wireName i};"
  String.intercalate "\n" ([header] ++ body ++ assigns ++ ["endmodule", ""])

def toVerilogSeqChecked (name : String) (p : Pipe a b) : Except String String :=
  if name.isEmpty || !(name.toList.head!.isAlpha || name.toList.head! == '_') ||
      !name.toList.all (fun ch => ch.isAlphanum || ch == '_') then
    .error "Module name must be a nonempty Verilog identifier."
  else .ok (toVerilogSeq name p)

end QuantCert

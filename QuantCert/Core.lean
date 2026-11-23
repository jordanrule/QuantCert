import QuantCert.Quant

namespace QuantCert

def bitQ : QType := ⟨1, by decide, 1, by decide⟩

/-- Products are wire bundles; unit is the empty bundle. Scales participate in typing. -/
inductive WireType where
  | unit
  | word (q : QType)
  | prod (a b : WireType)

infixr:35 " ⊗ " => WireType.prod

@[reducible] def Value : WireType → Type
  | .unit => Unit
  | .word q => BitVec q.bitWidth
  | .prod a b => Value a × Value b

/-- All primitives have a single output. Add requires identical quantization metadata. -/
inductive Prim : WireType → QType → Type where
  | nand : Prim (.word bitQ ⊗ .word bitQ) bitQ
  | mul (a b out : QType) (scale_ok : out.scale = a.scale * b.scale) :
      Prim (.word a ⊗ .word b) out
  | add (q : QType) : Prim (.word q ⊗ .word q) q
  | requant (a b : QType) (receipt : RequantParams a b) : Prim (.word a) b
  | relu (q : QType) : Prim (.word q) q

def evalPrim : Prim a q → Value a → BitVec q.bitWidth
  | .nand, (x, y) => BitVec.not (BitVec.and x y)
  | .mul _ _ out _, (x, y) => BitVec.ofInt out.bitWidth (x.toInt * y.toInt)
  | .add q, (x, y) => BitVec.ofInt q.bitWidth (x.toInt + y.toInt)
  | .requant _ b r, x =>
      BitVec.ofInt b.bitWidth (hwRequantizeInt x.toInt r.multiplier r.shift)
  | .relu q, x => BitVec.ofInt q.bitWidth (max 0 x.toInt)

/-- Syntax of a free symmetric Cartesian monoidal hardware category.
Categorical equations hold extensionally under `evalCircuit`, not as AST equality. -/
inductive Circuit : WireType → WireType → Type where
  | id : Circuit a a
  | comp : Circuit a b → Circuit b c → Circuit a c
  | par : Circuit a b → Circuit c d → Circuit (a ⊗ c) (b ⊗ d)
  | swap : Circuit (a ⊗ b) (b ⊗ a)
  | dup : Circuit a (a ⊗ a)
  | drop : Circuit a .unit
  | fst : Circuit (a ⊗ b) a
  | snd : Circuit (a ⊗ b) b
  | assoc : Circuit ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c))
  | unassoc : Circuit (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c)
  | unitL : Circuit (.unit ⊗ a) a
  | unitLInv : Circuit a (.unit ⊗ a)
  | prim : Prim a q → Circuit a (.word q)

infixr:60 " >>> " => Circuit.comp
infixr:65 " *** " => Circuit.par

def fanout (f : Circuit a b) (g : Circuit a c) : Circuit a (b ⊗ c) :=
  Circuit.dup >>> (f *** g)

infixr:55 " &&& " => fanout

/-- Bit-exact, combinational denotation; word outputs use modular two's-complement storage. -/
def evalCircuit : Circuit a b → Value a → Value b
  | .id, x => x
  | .comp f g, x => evalCircuit g (evalCircuit f x)
  | .par f g, (x, y) => (evalCircuit f x, evalCircuit g y)
  | .swap, (x, y) => (y, x)
  | .dup, x => (x, x)
  | .drop, _ => ()
  | .fst, (x, _) => x
  | .snd, (_, y) => y
  | .assoc, ((x, y), z) => (x, (y, z))
  | .unassoc, (x, (y, z)) => ((x, y), z)
  | .unitL, (_, x) => x
  | .unitLInv, x => ((), x)
  | .prim p, x => evalPrim p x

def Circuit.Equivalent (f g : Circuit a b) : Prop :=
  ∀ x, evalCircuit f x = evalCircuit g x

theorem comp_assoc (f : Circuit a b) (g : Circuit b c) (h : Circuit c d) :
    ((f >>> g) >>> h).Equivalent (f >>> (g >>> h)) := by intro x; rfl

theorem id_comp (f : Circuit a b) : (Circuit.id >>> f).Equivalent f := by intro x; rfl
theorem comp_id (f : Circuit a b) : (f >>> Circuit.id).Equivalent f := by intro x; rfl

theorem tensor_comp (f : Circuit a b) (g : Circuit b c)
    (h : Circuit d e) (k : Circuit e z) :
    ((f *** h) >>> (g *** k)).Equivalent ((f >>> g) *** (h >>> k)) := by
  intro x; rfl

theorem swap_involutive : (Circuit.swap >>> Circuit.swap : Circuit (a ⊗ b) (a ⊗ b)).Equivalent
    Circuit.id := by intro x; rfl

theorem fanout_fst (f : Circuit a b) (g : Circuit a c) :
    ((f &&& g) >>> Circuit.fst).Equivalent f := by intro x; rfl

theorem fanout_snd (f : Circuit a b) (g : Circuit a c) :
    ((f &&& g) >>> Circuit.snd).Equivalent g := by intro x; rfl

theorem fanout_unique (h : Circuit a (b ⊗ c)) :
    ((h >>> Circuit.fst) &&& (h >>> Circuit.snd)).Equivalent h := by intro x; rfl

theorem tensor_id :
    (Circuit.id *** Circuit.id : Circuit (a ⊗ b) (a ⊗ b)).Equivalent Circuit.id := by
  intro x; rfl

theorem swap_natural (f : Circuit a b) (g : Circuit c d) :
    ((f *** g) >>> Circuit.swap).Equivalent (Circuit.swap >>> (g *** f)) := by
  intro x; rfl

theorem assoc_inverse :
    (Circuit.assoc >>> Circuit.unassoc : Circuit ((a ⊗ b) ⊗ c) ((a ⊗ b) ⊗ c)).Equivalent
      Circuit.id := by intro x; rfl

theorem unassoc_inverse :
    (Circuit.unassoc >>> Circuit.assoc : Circuit (a ⊗ (b ⊗ c)) (a ⊗ (b ⊗ c))).Equivalent
      Circuit.id := by intro x; rfl

theorem assoc_natural (f : Circuit a b) (g : Circuit c d) (h : Circuit e z) :
    (((f *** g) *** h) >>> Circuit.assoc).Equivalent
      (Circuit.assoc >>> (f *** (g *** h))) := by intro x; rfl

theorem pentagon :
    (((Circuit.assoc *** Circuit.id) >>> Circuit.assoc >>> (Circuit.id *** Circuit.assoc) :
        Circuit (((a ⊗ b) ⊗ c) ⊗ d) (a ⊗ (b ⊗ (c ⊗ d)))).Equivalent
      (Circuit.assoc >>> Circuit.assoc)) := by intro x; rfl

theorem hexagon :
    ((Circuit.assoc >>> Circuit.swap >>> Circuit.assoc :
        Circuit ((a ⊗ b) ⊗ c) (b ⊗ (c ⊗ a))).Equivalent
      ((Circuit.swap *** Circuit.id) >>> Circuit.assoc >>> (Circuit.id *** Circuit.swap))) := by
  intro x; rfl

def unitR : Circuit (a ⊗ .unit) a := Circuit.swap >>> Circuit.unitL

theorem triangle :
    ((Circuit.assoc >>> (Circuit.id *** Circuit.unitL) :
        Circuit ((a ⊗ .unit) ⊗ b) (a ⊗ b)).Equivalent (unitR *** Circuit.id)) := by
  intro x; rfl

theorem unit_inverse :
    (Circuit.unitLInv >>> Circuit.unitL : Circuit a a).Equivalent Circuit.id := by
  intro x; rfl

theorem unit_inverse' :
    (Circuit.unitL >>> Circuit.unitLInv : Circuit (.unit ⊗ a) (.unit ⊗ a)).Equivalent
      Circuit.id := by
  intro x
  cases x with | mk u v => cases u; rfl

theorem terminal_unique (f : Circuit a .unit) : f.Equivalent Circuit.drop := by
  intro x
  cases evalCircuit f x
  rfl

end QuantCert

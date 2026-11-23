import QuantCert.ModelError
import QuantCert.Semantics

namespace QuantCert.Model

def Format.wire (f : Format) : QType :=
  ⟨f.bits, f.bits_pos, f.scale, f.scale_pos, f.signed⟩

def rawWire (bits : Nat) (h : 0 < bits) : QType := ⟨bits, h, 1, by decide, true⟩

def bundle (q : QType) : Nat → WireType
  | 0 => .unit
  | n + 1 => .word q ⊗ bundle q n

def values (q : QType) : (n : Nat) → Value (bundle q n) → Fin n → BitVec q.bitWidth
  | 0, _, i => Fin.elim0 i
  | _ + 1, (x, xs), i => Fin.cases x (fun j => values q _ xs j) i

def pack (q : QType) : (n : Nat) → (Fin n → BitVec q.bitWidth) → Value (bundle q n)
  | 0, _ => ()
  | n + 1, x => (x 0, pack q n (fun i => x i.succ))

theorem values_pack (q : QType) (n : Nat) (x : Fin n → BitVec q.bitWidth) :
    values q n (pack q n x) = x := by
  funext i
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (funext (ih (fun k => x k.succ))) j

def codes (f : Format) (v : Value (bundle f.wire n)) : Fin n → Int :=
  fun i => if f.signed then (values f.wire n v i).toInt else (values f.wire n v i).toNat

def encodeCodes (f : Format) (x : Fin n → Int) : Value (bundle f.wire n) :=
  pack f.wire n (fun i => BitVec.ofInt f.bits (x i))

theorem codes_encode (f : Format) (x : Fin n → Int) :
    codes f (encodeCodes f x) = fun i => f.store (x i) := by
  unfold codes encodeCodes
  rw [values_pack]
  rfl

def project (q : QType) : (n : Nat) → Fin n → Circuit (bundle q n) (.word q)
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases Circuit.fst (fun j => Circuit.snd >>> project q n j) i

theorem project_correct (q : QType) (n : Nat) (i : Fin n) (v : Value (bundle q n)) :
    evalCircuit (project q n i) v = values q n v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j v.2

def constant (q : QType) (x : Int) : Circuit a (.word q) :=
  Circuit.drop >>> Circuit.prim (.const q x)

def collect (q : QType) : (n : Nat) →
    (Fin n → Circuit a (.word q)) → Circuit a (bundle q n)
  | 0, _ => Circuit.drop
  | n + 1, f => f 0 &&& collect q n (fun i => f i.succ)

theorem collect_correct (q : QType) (n : Nat) (f : Fin n → Circuit a (.word q))
    (x : Value a) :
    evalCircuit (collect q n f) x = pack q n (fun i => evalCircuit (f i) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (evalCircuit (f 0) x, evalCircuit (collect q n (fun i => f i.succ)) x) = _
    rw [ih]
    rfl

def sumCircuit (q : QType) : (n : Nat) →
    (Fin n → Circuit a (.word q)) → Circuit a (.word q)
  | 0, _ => constant q 0
  | n + 1, f => (f 0 &&& sumCircuit q n (fun i => f i.succ)) >>> Circuit.prim (.add q)

theorem sumCircuit_correct (bits : Nat) (h : 0 < bits) (n : Nat)
    (f : Fin n → Circuit a (.word (rawWire bits h))) (x : Value a) :
    (evalCircuit (sumCircuit (rawWire bits h) n f) x).toInt =
      storedSum bits n (fun i => (evalCircuit (f i) x).toInt) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change signedStore bits
      ((evalCircuit (f 0) x).toInt +
        (evalCircuit (sumCircuit (rawWire bits h) n (fun i => f i.succ)) x).toInt) = _
    rw [ih]
    rfl

def QuantLayer.productCircuit (l : QuantLayer n m a b) (j : Fin m) (i : Fin n) :
    Circuit (bundle a.wire n) (.word (rawWire l.accumulatorBits l.accumulatorBits_pos)) :=
  let q := rawWire l.accumulatorBits l.accumulatorBits_pos
  ((project a.wire n i >>> Circuit.prim (.offset a.wire q a.zeroPoint)) &&&
    constant q (l.weight j i - (l.weightFormat j).zeroPoint)) >>>
      Circuit.prim (.mul q q q (by change (1 : Rat) = 1 * 1; decide +kernel))

def QuantLayer.accCircuit (l : QuantLayer n m a b) (j : Fin m) :
    Circuit (bundle a.wire n) (.word (rawWire l.accumulatorBits l.accumulatorBits_pos)) :=
  let q := rawWire l.accumulatorBits l.accumulatorBits_pos
  (constant q (l.bias j) &&& sumCircuit q n (l.productCircuit j)) >>> Circuit.prim (.add q)

def QuantLayer.roundCircuit (l : QuantLayer n m a b) (j : Fin m) :
    Circuit (bundle a.wire n) (.word (rawWire l.temporaryBits l.temporaryBits_pos)) :=
  let acc := rawWire l.accumulatorBits l.accumulatorBits_pos
  let tmp := rawWire l.temporaryBits l.temporaryBits_pos
  -- The product receives the accumulator at its original width: widening it first
  -- could truncate a wide accumulator even when the resulting product fits.
  let product := Circuit.comp (l.accCircuit j &&& constant tmp (l.multiplier j))
    (Circuit.prim (.mul acc tmp tmp (by change (1 : Rat) = 1 * 1; decide +kernel)))
  (product &&& constant tmp ((2 ^ l.shift j : Nat) / 2)) >>>
      Circuit.prim (.add tmp) >>> Circuit.prim (.shift tmp (l.shift j))

def QuantLayer.neuronCircuit (l : QuantLayer n m a b) (j : Fin m) :
    Circuit (bundle a.wire n) (.word b.wire) :=
  let tmp := rawWire l.temporaryBits l.temporaryBits_pos
  let activation : Circuit (.word tmp) (.word tmp) :=
    match l.reference.activation with
    | .identity => .id
    | .relu => .prim (.relu tmp)
  l.roundCircuit j >>> activation >>> Circuit.prim (.offset tmp tmp (-b.zeroPoint)) >>>
    Circuit.prim (.clip tmp b.wire b.lo b.hi)

def QuantLayer.lower (l : QuantLayer n m a b) : Circuit (bundle a.wire n) (bundle b.wire m) :=
  collect b.wire m l.neuronCircuit

theorem QuantLayer.productCircuit_correct (l : QuantLayer n m a b) (j : Fin m) (i : Fin n)
    (v : Value (bundle a.wire n)) :
    (evalCircuit (l.productCircuit j i) v).toInt = l.machineProduct (codes a v) j i := by
  simp only [productCircuit, evalCircuit, fanout, evalPrim, constant, project_correct]
  rfl

theorem QuantLayer.accCircuit_correct (l : QuantLayer n m a b) (j : Fin m)
    (v : Value (bundle a.wire n)) :
    (evalCircuit (l.accCircuit j) v).toInt = l.machineAcc (codes a v) j := by
  change signedStore l.accumulatorBits
    (signedStore l.accumulatorBits (l.bias j) +
      (evalCircuit (sumCircuit _ n (l.productCircuit j)) v).toInt) = _
  rw [sumCircuit_correct]
  simp only [l.productCircuit_correct]
  rfl

theorem QuantLayer.roundCircuit_correct (l : QuantLayer n m a b) (j : Fin m)
    (v : Value (bundle a.wire n)) :
    (evalCircuit (l.roundCircuit j) v).toInt = l.machineRounded (codes a v) j := by
  simp only [roundCircuit, evalCircuit, fanout, evalPrim, constant, wordInt, rawWire, ↓reduceIte]
  rw [l.accCircuit_correct]
  rfl

theorem relu_store (bits : Nat) (hb : 0 < bits) (x : BitVec bits) :
    (BitVec.ofInt bits (max 0 x.toInt)).toInt = max 0 x.toInt := by
  have hl := BitVec.le_toInt x
  have hh := BitVec.toInt_lt (x := x)
  have hp := Nat.two_pow_pos (bits - 1)
  have hp' : (0 : Int) < (2 : Int) ^ (bits - 1) := by
    have hc : (0 : Int) < ((2 ^ (bits - 1) : Nat) : Int) := by omega
    simpa only [Int.natCast_pow] using hc
  apply BitVec.toInt_ofInt_eq_self hb <;> omega

theorem QuantLayer.neuronCircuit_correct (l : QuantLayer n m a b) (j : Fin m)
    (v : Value (bundle a.wire n)) :
    evalCircuit (l.neuronCircuit j) v =
      BitVec.ofInt b.bits (clamp b.lo b.hi (signedStore l.temporaryBits
        (l.reference.activation.integer (l.machineRounded (codes a v) j) + b.zeroPoint))) := by
  cases ha : l.reference.activation with
  | identity =>
    simp only [neuronCircuit, ha, evalCircuit, evalPrim, rawWire, wordInt,
      ↓reduceIte, Int.sub_neg, Activation.integer]
    rw [l.roundCircuit_correct]
    rfl
  | relu =>
    simp only [neuronCircuit, ha, evalCircuit, evalPrim, rawWire, wordInt,
      ↓reduceIte, Int.sub_neg, Activation.integer]
    rw [relu_store _ l.temporaryBits_pos, l.roundCircuit_correct]
    rfl

theorem QuantLayer.lower_correct (l : QuantLayer n m a b) (v : Value (bundle a.wire n)) :
    codes b (evalCircuit l.lower v) = l.machineEval (codes a v) := by
  unfold lower
  rw [collect_correct]
  unfold codes
  rw [values_pack]
  funext j
  rw [l.neuronCircuit_correct]
  rfl

def QuantNetwork.lower : QuantNetwork n m a b → Circuit (bundle a.wire n) (bundle b.wire m)
  | .done => .id
  | .cons l net => l.lower >>> net.lower

/-- No range assumptions: lowering preserves finite-width wrapping and saturation too. -/
theorem QuantNetwork.lower_correct (net : QuantNetwork n m a b) (v : Value (bundle a.wire n)) :
    codes b (evalCircuit net.lower v) = net.machineEval (codes a v) := by
  induction net with
  | done => rfl
  | cons l net ih =>
    change codes _ (evalCircuit net.lower (evalCircuit l.lower v)) = _
    rw [ih, l.lower_correct]
    rfl

/-- Both frontend paths use the same fresh-wire compiler and operational netlist. -/
theorem QuantNetwork.compile_correct (net : QuantNetwork n m a b)
    (e : WireEnv (bundle a.wire n)) (initial : Netlist) (seed : Store)
    (h : Bounded e initial.next) :
    codes b (readEnv (compile net.lower e initial).1
      (evalNetlist (compile net.lower e initial).2.cells seed)) =
    net.machineEval (codes a (readEnv e (evalNetlist initial.cells seed))) := by
  rw [QuantCert.compile_correct net.lower e initial seed h]
  exact net.lower_correct _

theorem QuantNetwork.compiledError_sound (net : QuantNetwork n m a b)
    (r : Fin n → IntRange) (hs : net.Safe r) (error : Fin n → Rat)
    (real : Fin n → Rat) (e : WireEnv (bundle a.wire n))
    (initial : Netlist) (seed : Store) (h : Bounded e initial.next)
    (hx : ∀ i, (r i).Contains (codes a (readEnv e (evalNetlist initial.cells seed)) i))
    (he : ∀ i, ratAbs (a.decode (codes a (readEnv e (evalNetlist initial.cells seed)) i) -
      real i) ≤ error i) (j : Fin m) :
    ratAbs (b.decode (codes b (readEnv (compile net.lower e initial).1
      (evalNetlist (compile net.lower e initial).2.cells seed)) j) -
        net.reference.eval real j) ≤ net.outputError r error j := by
  rw [net.compile_correct e initial seed h]
  exact net.machineError_sound r hs error real _ hx he j

end QuantCert.Model

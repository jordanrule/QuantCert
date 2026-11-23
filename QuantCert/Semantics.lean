import QuantCert.Compiler

namespace QuantCert

abbrev Store := WireId → Nat

def readEnv : {a : WireType} → WireEnv a → Store → Value a
  | .unit, _, _ => ()
  | .word q, i, s => BitVec.ofNat q.bitWidth (s i)
  | .prod _ _, (x, y), s => (readEnv x s, readEnv y s)

def write (s : Store) (i : WireId) (v : Nat) : Store :=
  fun j => if j = i then v else s j

/-- Operational semantics executes explicit assignments, in topological order. -/
def evalNetlist : List Cell → Store → Store
  | [], s => s
  | c :: cs, s =>
      let t := evalNetlist cs s
      write t c.output (evalPrim c.op (readEnv c.inputs t)).toNat

theorem bounded_mono {a : WireType} (e : WireEnv a) {m n : Nat}
    (h : Bounded e m) (hmn : m ≤ n) : Bounded e n := by
  induction a with
  | unit => trivial
  | word q => exact Nat.lt_of_lt_of_le h hmn
  | prod a b ih₁ ih₂ => exact ⟨ih₁ e.1 h.1, ih₂ e.2 h.2⟩

theorem readEnv_congr {a : WireType} (e : WireEnv a) (s t : Store) (n : Nat)
    (h : Bounded e n) (heq : ∀ i, i < n → s i = t i) :
    readEnv e s = readEnv e t := by
  induction a with
  | unit => rfl
  | word q => simp only [readEnv, heq e h]
  | prod a b ih₁ ih₂ =>
      change (readEnv e.1 s, readEnv e.2 s) = (readEnv e.1 t, readEnv e.2 t)
      rw [ih₁ e.1 h.1, ih₂ e.2 h.2]

/-- Strong compiler invariant: outputs are allocated, the counter is monotone,
the output denotation agrees, and every previously allocated wire is preserved.
It holds for every initial cell list and seed store; only input references must
be below the fresh counter. -/
theorem compile_invariant (c : Circuit a b) :
    ∀ (e : WireEnv a) (n : Netlist) (seed : Store), Bounded e n.next →
    let (o, m) := compile c e n
    Bounded o m.next ∧ n.next ≤ m.next ∧
      readEnv o (evalNetlist m.cells seed) =
        evalCircuit c (readEnv e (evalNetlist n.cells seed)) ∧
      (∀ i, i < n.next → evalNetlist m.cells seed i = evalNetlist n.cells seed i) := by
  induction c with
  | id =>
      intro e n seed h
      exact ⟨h, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | comp f g ihf ihg =>
      intro e n seed h
      rcases hf : compile f e n with ⟨mid, m⟩
      rcases hg : compile g mid m with ⟨out, k⟩
      have hF := ihf e n seed h
      rw [hf] at hF
      have hG := ihg mid m seed hF.1
      rw [hg] at hG
      rw [compile_comp, hf]
      dsimp only
      rw [hg]
      change Bounded out k.next ∧ n.next ≤ k.next ∧
        readEnv out (evalNetlist k.cells seed) =
          evalCircuit g (evalCircuit f (readEnv e (evalNetlist n.cells seed))) ∧ _
      · exact ⟨hG.1, Nat.le_trans hF.2.1 hG.2.1,
          hG.2.2.1.trans (congrArg (evalCircuit g) hF.2.2.1),
          fun i hi => (hG.2.2.2 i (Nat.lt_of_lt_of_le hi hF.2.1)).trans (hF.2.2.2 i hi)⟩
  | par f g ihf ihg =>
      intro e n seed h
      rcases hf : compile f e.1 n with ⟨left, m⟩
      rcases hg : compile g e.2 m with ⟨right, k⟩
      have hF := ihf e.1 n seed h.1
      rw [hf] at hF
      have hG := ihg e.2 m seed (bounded_mono e.2 h.2 hF.2.1)
      rw [hg] at hG
      have hl := readEnv_congr left (evalNetlist k.cells seed)
        (evalNetlist m.cells seed) m.next hF.1 hG.2.2.2
      have hr := readEnv_congr e.2 (evalNetlist m.cells seed)
        (evalNetlist n.cells seed) n.next h.2 hF.2.2.2
      rw [compile_par, hf]
      dsimp only
      rw [hg]
      change (Bounded left k.next ∧ Bounded right k.next) ∧ n.next ≤ k.next ∧
        (readEnv left (evalNetlist k.cells seed), readEnv right (evalNetlist k.cells seed)) =
        (evalCircuit f (readEnv e.1 (evalNetlist n.cells seed)),
         evalCircuit g (readEnv e.2 (evalNetlist n.cells seed))) ∧ _
      refine ⟨⟨bounded_mono left hF.1 hG.2.1, hG.1⟩, Nat.le_trans hF.2.1 hG.2.1,
        ?_, fun i hi => (hG.2.2.2 i (Nat.lt_of_lt_of_le hi hF.2.1)).trans (hF.2.2.2 i hi)⟩
      rw [hl, hF.2.2.1, hG.2.2.1, hr]
  | prim p =>
      intro e n seed h
      change n.next < n.next + 1 ∧ n.next ≤ n.next + 1 ∧
        BitVec.ofNat _ (write (evalNetlist n.cells seed) n.next
          (evalPrim p (readEnv e (evalNetlist n.cells seed))).toNat n.next) =
          evalPrim p (readEnv e (evalNetlist n.cells seed)) ∧ _
      refine ⟨Nat.lt_succ_self _, Nat.le_succ _, ?_, ?_⟩
      · simp [write]
      · intro i hi
        simp [evalNetlist, write, Nat.ne_of_lt hi]
  | swap =>
      intro e n seed h
      exact ⟨⟨h.2, h.1⟩, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | dup =>
      intro e n seed h
      exact ⟨⟨h, h⟩, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | drop =>
      intro e n seed _
      exact ⟨True.intro, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | fst =>
      intro e n seed h
      exact ⟨h.1, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | snd =>
      intro e n seed h
      exact ⟨h.2, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | assoc =>
      intro e n seed h
      exact ⟨⟨h.1.1, h.1.2, h.2⟩, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | unassoc =>
      intro e n seed h
      exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2⟩, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | unitL =>
      intro e n seed h
      exact ⟨h.2, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  | unitLInv =>
      intro e n seed h
      exact ⟨⟨True.intro, h⟩, Nat.le_refl _, rfl, fun _ _ => rfl⟩

/-- Evaluating the compiled structural assignments agrees exactly with the DSL. -/
theorem compile_correct (c : Circuit a b) (e : WireEnv a) (n : Netlist)
    (seed : Store) (h : Bounded e n.next) :
    readEnv (compile c e n).1 (evalNetlist (compile c e n).2.cells seed) =
      evalCircuit c (readEnv e (evalNetlist n.cells seed)) :=
  (compile_invariant c e n seed h).2.2.1

end QuantCert

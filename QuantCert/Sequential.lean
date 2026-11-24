import QuantCert.Semantics

namespace QuantCert

/-- The reset value of every register introduced by the pipelining pass. -/
def zeroValue : (t : WireType) → Value t
  | .unit => ()
  | .word _ => 0
  | .prod a b => (zeroValue a, zeroValue b)

/-- Synchronous circuits in one clock domain with one active-high synchronous reset.
`reg init` is a register bundle that loads `init` when reset is asserted. -/
inductive Pipe : WireType → WireType → Type where
  | comb : Circuit a b → Pipe a b
  | reg (init : Value a) : Pipe a a
  | seq : Pipe a b → Pipe b c → Pipe a c
  | par : Pipe a b → Pipe c d → Pipe (a ⊗ c) (b ⊗ d)

/-- Clock cycles between an input and the output computed from it. -/
def Pipe.latency : Pipe a b → Nat
  | .comb _ => 0
  | .reg _ => 1
  | .seq p q => p.latency + q.latency
  | .par p q => max p.latency q.latency

/-- `k` registers in series, all resetting to zero. -/
def delay (a : WireType) : Nat → Pipe a a
  | 0 => .comb .id
  | k + 1 => .seq (delay a k) (.reg (zeroValue a))

theorem delay_latency (a : WireType) (k : Nat) : (delay a k).latency = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [delay, Pipe.latency, ih]

/-! ### Stream semantics

The denotation of a `Pipe` assuming reset was applied on the cycle before time zero:
a register outputs its reset value at time zero and its previous input afterwards. -/

def Pipe.sem : Pipe a b → (Nat → Value a) → Nat → Value b
  | .comb c, x, t => evalCircuit c (x t)
  | .reg init, x, t => match t with
      | 0 => init
      | t + 1 => x t
  | .seq p q, x, t => q.sem (p.sem x) t
  | .par p q, x, t => (p.sem (fun s => (x s).1) t, q.sem (fun s => (x s).2) t)

/-- `p` computes `f` with `n` cycles of latency. Earlier outputs are unconstrained. -/
def Realizes (p : Pipe a b) (f : Value a → Value b) (n : Nat) : Prop :=
  ∀ x t, n ≤ t → p.sem x t = f (x (t - n))

theorem realizes_comb (c : Circuit a b) : Realizes (.comb c) (evalCircuit c) 0 := by
  intro x t _; rfl

theorem realizes_reg (init : Value a) : Realizes (.reg init) id 1 := by
  intro x t ht
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rfl

theorem realizes_seq {p : Pipe a b} {q : Pipe b c} {f g n m}
    (hp : Realizes p f n) (hq : Realizes q g m) :
    Realizes (.seq p q) (fun v => g (f v)) (n + m) := by
  intro x t ht
  show q.sem (p.sem x) t = _
  rw [hq _ t (by omega), hp x (t - m) (by omega)]
  have : t - m - n = t - (n + m) := by omega
  rw [this]

theorem realizes_par {p : Pipe a b} {q : Pipe c d} {f g n}
    (hp : Realizes p f n) (hq : Realizes q g n) :
    Realizes (.par p q) (fun v => (f v.1, g v.2)) n := by
  intro x t ht
  show (_, _) = _
  rw [hp _ t ht, hq _ t ht]

theorem realizes_delay (a : WireType) (k : Nat) : Realizes (delay a k) id k := by
  induction k with
  | zero => exact realizes_comb _
  | succ k ih => exact realizes_seq ih (realizes_reg _)

theorem realizes_congr {p : Pipe a b} {f g : Value a → Value b} {n m : Nat}
    (h : Realizes p f n) (hfg : ∀ v, f v = g v) (hnm : n = m) : Realizes p g m := by
  subst hnm
  intro x t ht
  rw [h x t ht, hfg]

/-! ### The pipelining pass -/

/-- Chooses which primitives end a pipeline stage: a register bank follows each cut primitive. -/
abbrev CutPolicy := {a : WireType} → {q : QType} → Prim a q → Bool

def cutEvery : CutPolicy := fun _ => true

/-- Registers follow multipliers, requantizers and memories, the usual timing-critical blocks. -/
def cutHeavy : CutPolicy := fun p =>
  match p with
  | .mul .. => true
  | .requant .. => true
  | .rom .. => true
  | _ => false

/-- Cut the combinational graph into stages. Parallel branches are padded with zero-reset
delay registers to the slower branch, so every path through the circuit has equal latency. -/
def pipeline (cut : CutPolicy) : Circuit a b → Pipe a b
  | .id => .comb .id
  | .comp f g => .seq (pipeline cut f) (pipeline cut g)
  | .par f g =>
      let pf := pipeline cut f
      let pg := pipeline cut g
      let l := max pf.latency pg.latency
      .par (.seq pf (delay _ (l - pf.latency))) (.seq pg (delay _ (l - pg.latency)))
  | .prim p =>
      if cut p then .seq (.comb (.prim p)) (.reg (zeroValue _)) else .comb (.prim p)
  | .swap => .comb .swap
  | .dup => .comb .dup
  | .drop => .comb .drop
  | .fst => .comb .fst
  | .snd => .comb .snd
  | .assoc => .comb .assoc
  | .unassoc => .comb .unassoc
  | .unitL => .comb .unitL
  | .unitLInv => .comb .unitLInv

/-- The pass preserves behavior, shifted by exactly the reported latency. -/
theorem pipeline_realizes (cut : CutPolicy) (c : Circuit a b) :
    Realizes (pipeline cut c) (evalCircuit c) (pipeline cut c).latency := by
  induction c with
  | id => exact realizes_comb .id
  | comp f g ihf ihg => exact realizes_seq ihf ihg
  | par f g ihf ihg =>
      simp only [pipeline, Pipe.latency]
      generalize pipeline cut f = pf at ihf ⊢
      generalize pipeline cut g = pg at ihg ⊢
      have hf := realizes_seq ihf (realizes_delay _ (max pf.latency pg.latency - pf.latency))
      have hg := realizes_seq ihg (realizes_delay _ (max pf.latency pg.latency - pg.latency))
      have hf' := realizes_congr hf (fun _ => rfl) (by omega : _ = max pf.latency pg.latency)
      have hg' := realizes_congr hg (fun _ => rfl) (by omega : _ = max pf.latency pg.latency)
      refine realizes_congr (realizes_par hf' hg') (fun _ => rfl) ?_
      simp only [delay_latency]
      omega
  | prim p =>
      simp only [pipeline]
      split
      · exact realizes_seq (realizes_comb _) (realizes_reg _)
      · exact realizes_comb _
  | swap => exact realizes_comb _
  | dup => exact realizes_comb _
  | drop => exact realizes_comb _
  | fst => exact realizes_comb _
  | snd => exact realizes_comb _
  | assoc => exact realizes_comb _
  | unassoc => exact realizes_comb _
  | unitL => exact realizes_comb _
  | unitLInv => exact realizes_comb _

/-! ### Clocked operational semantics -/

/-- Register contents; combinational pieces have no state. -/
def PState : Pipe a b → Type
  | .comb _ => Unit
  | @Pipe.reg a _ => Value a
  | .seq p q => PState p × PState q
  | .par p q => PState p × PState q

def Pipe.reset : (p : Pipe a b) → PState p
  | .comb _ => ()
  | .reg init => init
  | .seq p q => (p.reset, q.reset)
  | .par p q => (p.reset, q.reset)

/-- One rising clock edge: the output is Mealy-style (current state and input), and the next
state loads reset values when `rst` is high. -/
def Pipe.step : (p : Pipe a b) → PState p → Bool → Value a → Value b × PState p
  | .comb c, _, _, x => (evalCircuit c x, ())
  | .reg init, s, rst, x => (s, if rst then init else x)
  | .seq p q, s, rst, x =>
      let (y, sp') := p.step s.1 rst x
      let (z, sq') := q.step s.2 rst y
      (z, (sp', sq'))
  | .par p q, s, rst, (x, y) =>
      let (u, sp') := p.step s.1 rst x
      let (v, sq') := q.step s.2 rst y
      ((u, v), (sp', sq'))

/-- Reset is complete: whatever the register contents and inputs were, one reset edge
leaves every register at its defined reset value. -/
theorem Pipe.step_reset (p : Pipe a b) (s : PState p) (x : Value a) :
    (p.step s true x).2 = p.reset := by
  induction p with
  | comb c => rfl
  | reg init => simp [Pipe.step, Pipe.reset]
  | seq p q ihp ihq =>
      obtain ⟨sp, sq⟩ : PState p × PState q := s
      simp only [Pipe.step, Pipe.reset, ihp, ihq]
  | par p q ihp ihq =>
      obtain ⟨sp, sq⟩ : PState p × PState q := s
      obtain ⟨x, y⟩ := x
      simp only [Pipe.step, Pipe.reset, ihp, ihq]

/-- `Inv p s x t`: `s` is the state of `p` after `t` reset-free edges on input stream `x`. -/
def Inv : (p : Pipe a b) → PState p → (Nat → Value a) → Nat → Prop
  | .comb _, _, _, _ => True
  | .reg init, s, x, t => s = (match t with | 0 => init | t + 1 => x t)
  | .seq p q, s, x, t => Inv p s.1 x t ∧ Inv q s.2 (p.sem x) t
  | .par p q, s, x, t => Inv p s.1 (fun i => (x i).1) t ∧ Inv q s.2 (fun i => (x i).2) t

theorem Pipe.inv_reset (p : Pipe a b) (x : Nat → Value a) : Inv p p.reset x 0 := by
  induction p with
  | comb c => trivial
  | reg init => rfl
  | seq p q ihp ihq => exact ⟨ihp x, ihq _⟩
  | par p q ihp ihq => exact ⟨ihp _, ihq _⟩

theorem Pipe.step_inv (p : Pipe a b) (s : PState p) (x : Nat → Value a) (t : Nat)
    (h : Inv p s x t) :
    (p.step s false (x t)).1 = p.sem x t ∧ Inv p (p.step s false (x t)).2 x (t + 1) := by
  induction p generalizing t with
  | comb c => exact ⟨rfl, trivial⟩
  | reg init =>
      subst h
      cases t <;> exact ⟨rfl, rfl⟩
  | seq p q ihp ihq =>
      obtain ⟨sp, sq⟩ : PState p × PState q := s
      obtain ⟨hp, hq⟩ := h
      obtain ⟨hp1, hp2⟩ := ihp sp x t hp
      obtain ⟨hq1, hq2⟩ := ihq sq (p.sem x) t hq
      simp only [Pipe.step]
      rw [hp1]
      exact ⟨hq1, hp2, hq2⟩
  | par p q ihp ihq =>
      obtain ⟨sp, sq⟩ : PState p × PState q := s
      obtain ⟨hp, hq⟩ := h
      obtain ⟨hp1, hp2⟩ := ihp sp _ t hp
      obtain ⟨hq1, hq2⟩ := ihq sq _ t hq
      simp only [Pipe.step]
      exact ⟨by rw [hp1, hq1]; rfl, hp2, hq2⟩

/-- State after `t` clock edges, with per-cycle reset `rst` and input stream `x`. -/
def Pipe.run (p : Pipe a b) (s : PState p) (rst : Nat → Bool) (x : Nat → Value a) :
    Nat → PState p
  | 0 => s
  | t + 1 => (p.step (p.run s rst x t) (rst t) (x t)).2

def Pipe.output (p : Pipe a b) (s : PState p) (rst : Nat → Bool) (x : Nat → Value a)
    (t : Nat) : Value b :=
  (p.step (p.run s rst x t) (rst t) (x t)).1

theorem Pipe.run_shift (p : Pipe a b) (s : PState p) (rst : Nat → Bool) (x : Nat → Value a)
    (k t : Nat) :
    p.run s rst x (k + t) = p.run (p.run s rst x k) (fun i => rst (k + i)) (fun i => x (k + i)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      show (p.step (p.run s rst x (k + t)) (rst (k + t)) (x (k + t))).2 = _
      rw [ih]
      rfl

/-- Without reset, a state satisfying the invariant produces the stream semantics forever. -/
theorem Pipe.run_sem (p : Pipe a b) (s : PState p) (x : Nat → Value a)
    (h : Inv p s x 0) (t : Nat) :
    Inv p (p.run s (fun _ => false) x t) x t ∧
      p.output s (fun _ => false) x t = p.sem x t := by
  induction t with
  | zero => exact ⟨h, (p.step_inv s x 0 h).1⟩
  | succ t ih =>
      exact ⟨(p.step_inv _ x t ih.1).2, (p.step_inv _ x (t + 1) (p.step_inv _ x t ih.1).2).1⟩

/-- **Pipeline refinement from arbitrary power-up state.** Assert reset on cycle 0 and release
it afterwards. Whatever the registers held at power-up, from cycle `latency + 1` on the
clocked pipeline outputs the combinational circuit's result for the input presented
`latency` cycles earlier. -/
theorem pipeline_correct (cut : CutPolicy) (c : Circuit a b)
    (s0 : PState (pipeline cut c)) (rst : Nat → Bool) (x : Nat → Value a)
    (h0 : rst 0 = true) (hr : ∀ t, 0 < t → rst t = false)
    (t : Nat) (ht : (pipeline cut c).latency + 1 ≤ t) :
    (pipeline cut c).output s0 rst x t =
      evalCircuit c (x (t - (pipeline cut c).latency)) := by
  have hreal := pipeline_realizes cut c
  revert s0 hreal ht
  generalize pipeline cut c = p
  intro s0 ht hreal
  obtain ⟨u, rfl⟩ : ∃ u, t = 1 + u := ⟨t - 1, by omega⟩
  have hs : p.run s0 rst x 1 = p.reset := by
    simp only [Pipe.run]
    rw [h0]
    exact p.step_reset s0 (x 0)
  have hrst : (fun i => rst (1 + i)) = fun _ => false :=
    funext fun i => hr _ (by omega)
  have hout : p.output s0 rst x (1 + u) =
      p.output (p.run s0 rst x 1) (fun i => rst (1 + i)) (fun i => x (1 + i)) u := by
    simp only [Pipe.output, Pipe.run_shift, hr (1 + u) (by omega)]
  rw [hout, hs, hrst]
  rw [(p.run_sem p.reset _ (p.inv_reset _) u).2]
  rw [hreal _ u (by omega)]
  have : 1 + (u - p.latency) = 1 + u - p.latency := by omega
  simp only [this]

end QuantCert

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/DeferLate.lean: challengers that name the point of a marked evaluation only when they release
  it.

  In the language Step of Rom/Defer.lean a marked evaluation carries the closure pt that makes its
  point out of tokens. In mode I this closure is applied for one purpose only: to write the answer
  into the table at the release. So a program that does not yet know the point (a simulator that
  learns the symbol under a leaf only when the leaf is opened) can do the same work. LStep is Step
  without pt at the marked evaluation; instead each reveal supplies, as a partial map from (charged
  token, oracle), the closures of the evaluations that it releases. Late relates a Step program to
  an LStep program with the same constructors; a ghost context Γ remembers which closure the Step
  program gave for (charged token, oracle), and at a reveal of ts the LStep program must supply
  these closures for the tokens of ts. Related challengers, whose private states may be of different
  types, give the adversary the same view in mode I, if no run in mode I has a violation
  (Spec.lateView: a statement; proved in Rom/DeferLateProof.lean).
  `Spec.lateView` is used in `hopLateBP` (Compile/Batch/PubLate.lean), between mode I and the
  wrapped lifetime game (`WrBP`, Compile/Batch/PubWr.lean).
-/
import Rom.DeferPublic
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob
namespace Rom

/-- how the point of a marked evaluation of o is made of the value of the charged token and the
values of the others -/
abbrev Clo (S : OSpec) (o : S.ι) : Type := Bits → List Bits → S.Dom o

/-- One step of a challenger that supplies points at the release. As Step, but for marked and
reveal. A marked evaluation has no closure, and it draws its answer uniformly from a set A; a
program that stands for a Step program has A = univ (a simulator that is given part of the answer
draws the rest from the fibre). Limits: `Late`, and with it `Spec.lateView`, relates a Step program
only to a program with A = univ; a program with another A is covered by no statement of this
file. -/
inductive LStep (S : OSpec) (sp : Split S) (α : Type) : Type
  | pure (a : α) : LStep S sp α
  | sample (n : ℕ) (k : Fin (n + 1) → LStep S sp α) : LStep S sp α
  | plain (o : S.ι) (q : S.Dom o) (k : S.Rng o → LStep S sp α) : LStep S sp α
  | fresh (ℓ : ℕ) (k : Tok → LStep S sp α) : LStep S sp α
  | marked (o : S.ι) (t : Tok) (us : List Tok) (A : Finset (S.Rng o)) (hA : A.Nonempty)
      (k : sp.Vis o → Tok → LStep S sp α) : LStep S sp α
  | reveal (ts : List Tok) (pts : Tok → ∀ o : S.ι, Option (Clo S o))
      (k : List Bits → LStep S sp α) : LStep S sp α

variable {S : OSpec}

namespace LStep
variable {sp : Split S} {α β : Type}
def bind : LStep S sp α → (α → LStep S sp β) → LStep S sp β
  | pure a, g => g a
  | sample n k, g => sample n fun r => (k r).bind g
  | plain o q k, g => plain o q fun r => (k r).bind g
  | fresh ℓ k, g => fresh ℓ fun t => (k t).bind g
  | marked o t us A hA k, g => marked o t us A hA fun v t' => (k v t').bind g
  | reveal ts pts k, g => reveal ts pts fun vs => (k vs).bind g
instance : Monad (LStep S sp) where
  pure := LStep.pure
  bind := LStep.bind
end LStep

/-- the record of one marked evaluation, without its point -/
structure LEv (S : OSpec) where
  o : S.ι
  ans : S.Rng o
  charged : Tok
  others : List Tok
  tail : Tok
  released : Bool

/-- the state of the experiment beside the challenger's own; no counters and no flag: the rules are
checked on the Step side -/
structure LSt (S : OSpec) where
  table : Table S
  vals : List Bits
  shown : List Tok
  evs : List (LEv S)

def LSt.init (S : OSpec) : LSt S := ⟨Table.empty S, [], [], []⟩
def LSt.val (d : LSt S) (t : Tok) : Bits := d.vals.getD t []

/-- forget the point; `DSt.forget` below: the points, the counters (`nPlain`) and the flag
(`viol`) -/
def Ev.forget (e : Ev S) : LEv S := ⟨e.o, e.ans, e.charged, e.others, e.tail, e.released⟩
def DSt.forget (d : DSt S) : LSt S := ⟨d.table, d.vals, d.shown, d.evs.map Ev.forget⟩

/-- the release of one evaluation: the point is computed now, from the closure supplied now (nothing
is written if none is supplied), and the answer is written if the entry is empty -/
def lwrite (pts : Tok → ∀ o : S.ι, Option (Clo S o)) (val : Tok → Bits)
    (T : Table S) (e : LEv S) : Table S :=
  match pts e.charged e.o with
  | none => T
  | some pt =>
      match T e.o (pt (val e.charged) (e.others.map val)) with
      | none => T.set e.o (pt (val e.charged) (e.others.map val)) e.ans
      | some _ => T

/-- release of all evaluations charged to a shown token -/
def lrelease (pts : Tok → ∀ o : S.ι, Option (Clo S o))
    (val : Tok → Bits) (shown : List Tok) :
    List (LEv S) → Table S → List (LEv S) × Table S
  | [], T => ([], T)
  | e :: es, T =>
      if !e.released && shown.contains e.charged then
        let r := lrelease pts val shown es (lwrite pts val T e)
        ({ e with released := true } :: r.1, r.2)
      else
        let r := lrelease pts val shown es T
        (e :: r.1, r.2)

/-- the run of a step (there is only mode I) -/
def LStep.run {sp : Split S} {α : Type} : LStep S sp α → LSt S → PMF (α × LSt S)
  | .pure a, d => PMF.pure (a, d)
  | .sample n k, d => (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).run d
  | .plain o q k, d => (lazyAnswer d.table o q).bind fun p => (k p.1).run { d with table := p.2 }
  | .fresh ℓ k, d => (PMF.uniformOfFintype (Fin ℓ → Bool)).bind fun u =>
      (k d.vals.length).run { d with vals := d.vals ++ [List.ofFn u] }
  | .marked o t us A hA k, d => (PMF.uniformOfFinset A hA).bind fun r =>
      (k (sp.split o r).1 d.vals.length).run
        { d with vals := d.vals ++ [List.ofFn (sp.split o r).2],
                 evs := d.evs ++ [⟨o, r, t, us, d.vals.length, false⟩] }
  | .reveal ts pts k, d =>
      (k (ts.map d.val)).run
        { d with
          table := (lrelease pts d.val (d.shown ++ ts) d.evs d.table).2, shown := d.shown ++ ts,
          evs := (lrelease pts d.val (d.shown ++ ts) d.evs d.table).1 }

/-- A challenger of this kind. -/
structure LChall (S : OSpec) (sp : Split S) (Out In : Type) where
  τ : Type
  step : τ → Out → LStep S sp (In × τ)

/-- the `World` that it makes; the adversary's queries read the table -/
def LChall.world {sp : Split S} {Out In : Type} (C : LChall S sp Out In) :
    World S Out In where
  σ := C.τ × LSt S
  answer := fun s o q =>
    (lazyAnswer s.2.table o q).map fun p => (p.1, (s.1, { s.2 with table := p.2 }))
  reply := fun s m => ((C.step s.1 m).run s.2).map fun p => (p.1.1, (p.1.2, p.2))

/-- the ghost context: which closure the Step program gave when it charged token t at oracle o -/
abbrev Ctx (S : OSpec) : Type := Tok → ∀ o : S.ι, Option (Clo S o)

def Ctx.empty (S : OSpec) : Ctx S := fun _ _ => none

def Ctx.set (Γ : Ctx S) (t : Tok) (o : S.ι) (pt : Clo S o) : Ctx S :=
  Function.update Γ t (Function.update (Γ t) o (some pt))

/-- P and Q have the same constructors; Q has no closures at its marked evaluations (and draws their
answers from all of the range), and at each reveal of ts it supplies, for every token of ts and
every oracle at which P has charged it, the closure that P gave. n is a lower bound on the number of
tokens that exist: a new token has a number t >= n, and after it the bound is t + 1; so what is
known about older tokens survives. post relates the results, with the bound and the context at the
end. -/
inductive Late {sp : Split S} {α β : Type} (post : ℕ → Ctx S → α → β → Prop) :
    ℕ → Ctx S → Step S sp α → LStep S sp β → Prop
  | pure {n : ℕ} {Γ : Ctx S} {a : α} {b : β} (h : post n Γ a b) : Late post n Γ (.pure a) (.pure b)
  | sample {n : ℕ} {Γ : Ctx S} {m : ℕ} {k : Fin (m + 1) → Step S sp α}
      {k' : Fin (m + 1) → LStep S sp β} (h : ∀ r, Late post n Γ (k r) (k' r)) :
      Late post n Γ (.sample m k) (.sample m k')
  | plain {n : ℕ} {Γ : Ctx S} {o : S.ι} {q : S.Dom o} {k : S.Rng o → Step S sp α}
      {k' : S.Rng o → LStep S sp β} (h : ∀ r, Late post n Γ (k r) (k' r)) :
      Late post n Γ (.plain o q k) (.plain o q k')
  | fresh {n : ℕ} {Γ : Ctx S} {ℓ : ℕ} {k : Tok → Step S sp α} {k' : Tok → LStep S sp β}
      (h : ∀ t, n ≤ t → Late post (t + 1) Γ (k t) (k' t)) : Late post n Γ (.fresh ℓ k) (.fresh ℓ k')
  | marked {n : ℕ} {Γ : Ctx S} {o : S.ι} {t : Tok} {us : List Tok} {pt : Clo S o}
      {inj : ∀ vs, Function.Injective fun v => pt v vs} {k : sp.Vis o → Tok → Step S sp α}
      {k' : sp.Vis o → Tok → LStep S sp β}
      (h : ∀ v t', n ≤ t' → Late post (t' + 1) (Γ.set t o pt) (k v t') (k' v t')) :
      Late post n Γ (.marked o t us pt inj k) (.marked o t us Finset.univ Finset.univ_nonempty k')
  | reveal {n : ℕ} {Γ : Ctx S} {ts : List Tok} {pts : Ctx S} {k : List Bits → Step S sp α}
      {k' : List Bits → LStep S sp β}
      (hp : ∀ t ∈ ts, ∀ o pt, Γ t o = some pt → pts t o = some pt)
      (h : ∀ vs, Late post n Γ (k vs) (k' vs)) : Late post n Γ (.reveal ts k) (.reveal ts pts k')

theorem Ctx.set_same (Γ : Ctx S) (t : Tok) (o : S.ι) (pt : Clo S o) :
    (Γ.set t o pt) t o = some pt := by
  simp [Ctx.set]

theorem Ctx.set_ne_tok (Γ : Ctx S) {t t' : Tok} (h : t' ≠ t) (o : S.ι) (pt : Clo S o) (o' : S.ι) :
    (Γ.set t o pt) t' o' = Γ t' o' := by
  simp [Ctx.set, Function.update_of_ne h]

theorem Ctx.set_ne_oracle (Γ : Ctx S) (t : Tok) {o o' : S.ι} (h : o' ≠ o) (pt : Clo S o) :
    (Γ.set t o pt) t o' = Γ t o' := by
  simp [Ctx.set, Function.update_of_ne h]

/-- sequencing: related programs followed by related continuations are related -/
theorem Late.bind {sp : Split S} {α β α' β' : Type} {post : ℕ → Ctx S → α → β → Prop}
    {post' : ℕ → Ctx S → α' → β' → Prop} {n : ℕ} {Γ : Ctx S} {P : Step S sp α} {Q : LStep S sp β}
    (h : Late post n Γ P Q) {f : α → Step S sp α'} {g : β → LStep S sp β'}
    (hfg : ∀ n' Γ' a b, post n' Γ' a b → Late post' n' Γ' (f a) (g b)) :
    Late post' n Γ (P.bind f) (Q.bind g) := by
  induction h with
  | pure h => exact hfg _ _ _ _ h
  | sample _ ih => exact Late.sample ih
  | plain _ ih => exact Late.plain ih
  | fresh _ ih => exact Late.fresh ih
  | marked _ ih => exact Late.marked ih
  | reveal hp _ ih => exact Late.reveal hp ih

/-- a weaker relation between the results -/
theorem Late.mono {sp : Split S} {α β : Type} {post post' : ℕ → Ctx S → α → β → Prop} {n : ℕ}
    {Γ : Ctx S} {P : Step S sp α} {Q : LStep S sp β} (h : Late post n Γ P Q)
    (hpp : ∀ n' Γ' a b, post n' Γ' a b → post' n' Γ' a b) : Late post' n Γ P Q := by
  induction h with
  | pure h => exact Late.pure (hpp _ _ _ _ h)
  | sample _ ih => exact Late.sample ih
  | plain _ ih => exact Late.plain ih
  | fresh _ ih => exact Late.fresh ih
  | marked _ ih => exact Late.marked ih
  | reveal hp _ ih => exact Late.reveal hp ih

/-- a larger bound on the tokens that exist, if the relation between the results allows it -/
theorem Late.weaken {sp : Split S} {α β : Type} {post : ℕ → Ctx S → α → β → Prop}
    (hpost : ∀ n n' Γ a b, n ≤ n' → post n Γ a b → post n' Γ a b) {n : ℕ} {Γ : Ctx S}
    {P : Step S sp α} {Q : LStep S sp β} (h : Late post n Γ P Q) :
    ∀ n', n ≤ n' → Late post n' Γ P Q := by
  induction h with
  | pure h => exact fun n' hn => Late.pure (hpost _ _ _ _ _ hn h)
  | sample _ ih => exact fun n' hn => Late.sample fun r => ih r n' hn
  | plain _ ih => exact fun n' hn => Late.plain fun r => ih r n' hn
  | fresh h _ => exact fun n' hn => Late.fresh fun t ht => h t (hn.trans ht)
  | marked h _ => exact fun n' hn => Late.marked fun v t' ht => h v t' (hn.trans ht)
  | reveal hp _ ih => exact fun n' hn => Late.reveal hp fun vs => ih vs n' hn

/-- the context knows the closure of every unreleased evaluation of the state, the tokens of these
evaluations (`charged`, `others`) exist, and their charged tokens are not shown -/
def Ctx.Knows (Γ : Ctx S) (d : DSt S) : Prop :=
  ∀ e ∈ d.evs, e.released = false →
    (∃ pt, Γ e.charged e.o = some pt ∧ e.pt = pt (d.val e.charged) (e.others.map d.val)) ∧
    e.charged < d.vals.length ∧ (∀ x ∈ e.others, x < d.vals.length) ∧ e.charged ∉ d.shown

/-- A whole run, private states of different types, related by R with the current bound and context:
under the hypotheses below, if related states give steps related by `Late`, and no run in mode I has
a violation, the adversary's outputs against the two challengers have the same distribution. -/
def Spec.lateView : Prop :=
  ∀ (S : OSpec) (sp : Split S) (Out In α : Type) (C : Chall S sp Out In)
      (C' : LChall S sp Out In) (R : ℕ → Ctx S → C.τ → C'.τ → Prop),
    (∀ n Γ s s' m, R n Γ s s' →
      Late (fun n' Γ' a b => a.1 = b.1 ∧ R n' Γ' a.2 b.2) n Γ (C.step s m) (C'.step s' m)) →
    ∀ (A : Adv S Out In α) (s₀ : C.τ) (s₀' : C'.τ), R 0 (Ctx.empty S) s₀ s₀' →
      (∀ x ∈ (interact (C.world true) A (s₀, DSt.init S)).support, x.2.2.viol = false) →
      (interact (C.world true) A (s₀, DSt.init S)).map Prod.fst =
        (interact C'.world A (s₀', LSt.init S)).map Prod.fst

end Rom

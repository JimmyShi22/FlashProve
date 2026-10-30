-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsRuns.lean: a success of a routine of the verifier program, taken apart
into the successes of its calls, in order, with "the context is no dry run" carried along by the
class KeepsM (OnBytes/Tie/Pv/Keeps/KeepsLift.lean).

HasRuns m: for a monad m over blocks, the whole state St (for Blk the context; for StateT σ m the
pair of σ and m's), the context in it, and Runs x s a s': x, run from s, succeeds with the value a
and leaves s'. By definition Runs unfolds to the routine applied to its states and the context:
  Runs (x : Blk α) c a c' is x c = .ok (a, c')
  Runs (x : SubM α) (F, c) a (F', c') is x F c = .ok ((a, F'), c')
  Runs (x : LinkM α) (L, F, c) a (L', F', c') is x L F c = .ok (((a, L'), F'), c')
Two laws are asked of Runs (pure, bind: what a success says); all else is drawn from them.

Main names:
  step: a success of "x, then f" on a view: x has succeeded, it has left a view, and f has succeeded
    from there.
  runs_view; runs_lift, runs_up, runs_sub: a lifted routine has run below, and the layer's own state
    is as it was. runs_get.
  Fails: the class of the routines that never succeed.
  The tactics that this file declares:
  is_sequence h: succeeds if h is a success of a sequence of calls (a bind), and fails else.
  apart_from h d n: takes the success h of a sequence of calls apart, on the view d, call by call:
    for call number i, counted from n, the context gets the value a_i, the state s_i, the success
    r_i and the view d_i; a match or an if goes by cases, and a case whose routine never succeeds is
    closed.
  apart h d: apart_from h d 1.
  lower r with e: the success r of a routine that was lifted through one layer of state becomes the
    success below, and e says that the layer's own state is as it was.

Limits: one direction: from a success. Nothing is said on what a call does.
-/
import OnBytes.Tie.Pv.Keeps.KeepsLift
import OnBytes.Model.Trees
import Lean

namespace OnBytes.L5

open OnBytes

/-- What a success of a routine of m is. -/
class HasRuns (m : Type → Type) [Monad m] where
  /-- the whole state: every layer's own, and the context -/
  St : Type
  /-- the context in it -/
  ctx : St → Ctx
  /-- x, run from s, succeeds with a and leaves s' -/
  Runs : {α : Type} → m α → St → α → St → Prop
  runs_pure : ∀ {α : Type} {a b : α} {s s' : St}, Runs (pure a) s b s' → b = a ∧ s' = s
  runs_bind : ∀ {α β : Type} {x : m α} {f : α → m β} {s : St} {b : β} {s' : St},
    Runs (x >>= f) s b s' → ∃ a s1, Runs x s a s1 ∧ Runs (f a) s1 b s'

export HasRuns (Runs)

instance hasRuns_blk : HasRuns Blk where
  St := Ctx
  ctx := id
  Runs := fun x c a c' => x c = .ok (a, c')
  runs_pure := fun h => by cases h; exact ⟨rfl, rfl⟩
  runs_bind := fun {_ _ x f c b c'} h => by
    obtain ⟨a, c1, h1, h2⟩ := (Blk.yields_bind x f c c' b).1 ((Blk.yields_iff _ _ _ _).2 h)
    exact ⟨a, c1, (Blk.yields_iff _ _ _ _).1 h1, (Blk.yields_iff _ _ _ _).1 h2⟩

instance hasRuns_stateT {σ : Type} {m : Type → Type} [Monad m] [HasRuns m] :
    HasRuns (StateT σ m) where
  St := σ × HasRuns.St m
  ctx := fun s => HasRuns.ctx s.2
  Runs := fun x s a s' => HasRuns.Runs (x s.1) s.2 (a, s'.1) s'.2
  runs_pure := fun {_ a b s s'} h => by
    obtain ⟨e1, e2⟩ := HasRuns.runs_pure (m := m) (a := (a, s.1)) h
    exact ⟨congrArg Prod.fst e1, Prod.ext (congrArg Prod.snd e1) e2⟩
  runs_bind := fun {_ _ x f s b s'} h => by
    obtain ⟨⟨a, s1⟩, t1, h1, h2⟩ := HasRuns.runs_bind (m := m) (x := x s.1)
      (f := fun p => f p.1 p.2) h
    exact ⟨a, (s1, t1), h1, h2⟩

/-- The context in the state is no dry run. -/
def View {m : Type → Type} [Monad m] [HasRuns m] (s : HasRuns.St m) : Prop :=
  (HasRuns.ctx s).ch.dry = false

/-- The two classes agree: a routine with the property K, where it succeeds, leaves a context that
is Kept. -/
class RunsKeep (m : Type → Type) [Monad m] [HasKeeps m] [HasRuns m] : Prop where
  kept : ∀ {α : Type} {x : m α} {s : HasRuns.St m} {a : α} {s' : HasRuns.St m},
    HasKeeps.K x → Runs x s a s' → Kept (HasRuns.ctx s) (HasRuns.ctx s')

instance runsKeep_blk : RunsKeep Blk where
  kept := fun {_ _ c a c'} k h => Keeps.out (self := k) c a c' h

instance runsKeep_stateT {σ : Type} {m : Type → Type} [Monad m] [HasKeeps m] [HasRuns m]
    [RunsKeep m] : RunsKeep (StateT σ m) where
  kept := fun {_ _ s _ _} k h => RunsKeep.kept (m := m) (k s.1) h

section Laws

variable {m : Type → Type} [Monad m] [HasKeeps m] [HasRuns m] [RunsKeep m] {α β σ : Type}

/-- A routine that keeps, run on a view, leaves a view. -/
theorem runs_view {x : m α} [k : KeepsM x] {s : HasRuns.St m} {a : α} {s' : HasRuns.St m}
    (h : Runs x s a s') (d : View s) : View s' :=
  (RunsKeep.kept k.out h).dry.trans d

/-- One step. -/
theorem step {x : m α} [KeepsM x] {f : α → m β} {s : HasRuns.St m} {b : β} {s' : HasRuns.St m}
    (h : Runs (x >>= f) s b s') (d : View s) :
    ∃ a s1, Runs x s a s1 ∧ View s1 ∧ Runs (f a) s1 b s' := by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  exact ⟨a, s1, h1, runs_view h1 d, h2⟩

omit [HasKeeps m] [RunsKeep m] in
/-- A routine of the layer below, lifted: it has run below, and this layer's state is as it was. -/
theorem runs_lift {x : m α} {s : HasRuns.St (StateT σ m)} {a : α} {s' : HasRuns.St (StateT σ m)}
    (h : Runs (StateT.lift x : StateT σ m α) s a s') : Runs x s.2 a s'.2 ∧ s'.1 = s.1 := by
  obtain ⟨a', t1, h1, h2⟩ := HasRuns.runs_bind (m := m) (x := x)
    (f := fun a => pure (a, s.1)) h
  obtain ⟨e1, e2⟩ := HasRuns.runs_pure h2
  have ea : a = a' := congrArg Prod.fst e1
  rw [ea, e2]
  exact ⟨h1, congrArg Prod.snd e1⟩

omit [HasKeeps m] [RunsKeep m] in
/-- The same for the lift that Lean puts in by itself. n: any monad that lifts into m. -/
theorem runs_up {n : Type → Type} [MonadLiftT n m] {x : n α} {s : HasRuns.St (StateT σ m)} {a : α}
    {s' : HasRuns.St (StateT σ m)} (h : Runs (monadLift x : StateT σ m α) s a s') :
    Runs (monadLift x : m α) s.2 a s'.2 ∧ s'.1 = s.1 :=
  runs_lift (x := (monadLift x : m α)) h

omit [HasKeeps m] [RunsKeep m] in
/-- Reading this layer's state. -/
theorem runs_get {s : HasRuns.St (StateT σ m)} {a : σ} {s' : HasRuns.St (StateT σ m)}
    (h : Runs (get : StateT σ m σ) s a s') : a = s.1 ∧ s' = s := by
  obtain ⟨e1, e2⟩ := HasRuns.runs_pure (m := m) (a := (s.1, s.1)) h
  exact ⟨congrArg Prod.fst e1, Prod.ext (congrArg Prod.snd e1) e2⟩

end Laws

/-- LinkM.sub is the lift. -/
theorem runs_sub {α : Type} {x : Model.SubM α} {s : HasRuns.St Model.LinkM} {a : α}
    {s' : HasRuns.St Model.LinkM} (h : Runs (Model.LinkM.sub x) s a s') :
    Runs x s.2 a s'.2 ∧ s'.1 = s.1 :=
  runs_lift (σ := Model.LinkCtx) (x := x) h

/-! ## Routines that never succeed -/

/-- The routine succeeds from no state. -/
class Fails {m : Type → Type} [Monad m] [HasRuns m] {α : Type} (x : m α) : Prop where
  no : ∀ s a s', ¬ Runs x s a s'

instance fails_fail {α : Type} (n : String) : Fails (Blk.fail n : Blk α) :=
  ⟨fun _ _ _ h => by cases h⟩

instance fails_refuse {α : Type} (n : String) : Fails (Model.refuse n : Blk α) :=
  ⟨fun _ _ _ h => by cases h⟩

instance fails_lift {m : Type → Type} [Monad m] [HasRuns m] {α σ : Type}
    (x : m α) [f : Fails x] : Fails (StateT.lift x : StateT σ m α) :=
  ⟨fun _ _ _ h => f.no _ _ _ (runs_lift h).1⟩

instance fails_up {m n : Type → Type} [Monad m] [HasRuns m] [MonadLiftT n m] {α σ : Type}
    (x : n α) [f : Fails (monadLift x : m α)] :
    Fails (monadLift x : StateT σ m α) :=
  ⟨fun _ _ _ h => f.no _ _ _ (runs_up h).1⟩

instance fails_self {m : Type → Type} [Monad m] [HasRuns m] {α : Type} (x : m α) [f : Fails x] :
    Fails (monadLift x : m α) := f

/-- From a success of a routine that never succeeds, anything. -/
theorem Fails.elim {m : Type → Type} [Monad m] [HasRuns m] {α : Type} {x : m α} [f : Fails x]
    {s : HasRuns.St m} {a : α} {s' : HasRuns.St m} {P : Prop} (h : Runs x s a s') : P :=
  (f.no s a s' h).elim

/-! ## Two calls that leave all as it was -/

/-- A public condition under a name: it was true, and the context is as it was. -/
theorem runs_mustAs {n : String} {b : Bool} {c : Ctx} {u : Unit} {c' : Ctx}
    (h : Runs (Model.mustAs n b) c u c') : b = true ∧ c' = c := by
  cases b with
  | true => cases h; exact ⟨rfl, rfl⟩
  | false => cases h

/-- A value that must be there, under a name. -/
theorem runs_pure' {m : Type → Type} [Monad m] [HasRuns m] {α : Type} {a b : α}
    {s s' : HasRuns.St m} (h : Runs (pure a : m α) s b s') : b = a ∧ s' = s :=
  HasRuns.runs_pure h

/-! ## The tactics

apart h d: h is a success of a routine written as a sequence of calls, d says that it began on a
view. The success is taken apart, call by call: for call number i the context gets the value a_i
that
the call returned, the state s_i that it left, r_i (the call has succeeded from s_(i-1) with a_i and
left s_i) and d_i (s_i is on a view). A match or an if is taken by cases; a case whose routine never
succeeds is closed. What is left under the name h is the success of the last call. Each call must be
KeepsM, which Lean finds by instances. No definition is unfolded: a call that is itself a sequence
stays whole until its name is unfolded and apart_from is called on it (with the number from which
its names count).

lower r with e: r is a success of a routine that was lifted through one layer of state. r becomes
the
success of the routine below, and e says that the layer's own state is as it was. -/

/-- Fails unless the hypothesis is a success of a routine that is, as it stands, "x, then f". -/
elab "is_sequence " h:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let t ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getFVarId h).getType)
  let args := t.getAppArgs
  unless t.isAppOf ``HasRuns.Runs && args.size == 8 do
    throwError "not a success of a routine"
  let x ← Lean.Meta.whnfCore args[4]!
  unless x.isAppOf ``Bind.bind do throwError "not a sequence"

open Lean in
syntax "apart_from " ident ident num : tactic

open Lean in
macro_rules
  | `(tactic| apart_from $h $d $n) => do
    let i := n.getNat
    let nm (p : String) : Ident := mkIdent (Name.mkSimple (p ++ toString i))
    let next : TSyntax `num := Syntax.mkNumLit (toString (i + 1))
    `(tactic| first
      | (is_sequence $h
         have hh := step $h $d
         clear $h
         obtain ⟨$(nm "a"):ident, $(nm "s"):ident, $(nm "r"):ident, $(nm "d"):ident, $h:ident⟩ := hh
         apart_from $h $(nm "d") $next)
      | (split at $h:ident <;> first | exact Fails.elim $h | apart_from $h $d $n)
      | skip)

macro "apart " h:ident d:ident : tactic => `(tactic| apart_from $h $d 1)

macro "lower " r:ident " with " e:ident : tactic =>
  `(tactic| (have hh := runs_up $r; clear $r; obtain ⟨$r:ident, $e:ident⟩ := hh))

#print axioms hasRuns_blk
#print axioms hasRuns_stateT
#print axioms runsKeep_blk
#print axioms runsKeep_stateT
#print axioms runs_view
#print axioms step
#print axioms runs_lift
#print axioms runs_up
#print axioms runs_get
#print axioms runs_sub
#print axioms Fails.elim
#print axioms runs_mustAs

end OnBytes.L5

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysPlace.lean.
Routines of OnBytes/Model/AttentionTables.lean stay on the view: those that are named below.

These routines carry a state of their own, the tables placed so far (`PlaceM`). `DryP x`: from every
such state, a run of x on a view that returns is still on the view. The rules are those of
OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean at this level, and the tactic `stays` is taught them here,
with two further steps: a routine that is written as a function of its state, and `modify` on a
sub-proof's state.

 * `stays_placeAll`, `dry_tables`: the routine that places all tables, and the block that runs it
   from the empty state.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStayBlk
import OnBytes.Model.AttentionTables

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

section
variable {α β : Type}

/-- From every state of the tables placed so far, a run on a view stays on the view. -/
def DryP (x : PlaceM α) : Prop := ∀ t, Dry (x t)

theorem DryP.pure (a : α) : DryP (Pure.pure a : PlaceM α) := fun t => Dry.pure (a, t)
theorem DryP.bind {x : PlaceM α} {f : α → PlaceM β} (hx : DryP x) (hf : ∀ a, DryP (f a)) :
    DryP (x >>= f) := fun t =>
  Dry.bind (x := x t) (f := fun p => f p.1 p.2) (hx t) fun p => hf p.1 p.2
theorem DryP.lift {b : Blk α} (h : Dry b) : DryP (StateT.lift b : PlaceM α) := fun t =>
  Dry.bind (f := fun a => Pure.pure (a, t)) h fun _ => Dry.pure _
theorem DryP.monadLift {b : Blk α} (h : Dry b) : DryP (MonadLiftT.monadLift b : PlaceM α) :=
  DryP.lift h
theorem DryP.liftM {b : Blk α} (h : Dry b) : DryP (_root_.liftM b : PlaceM α) := DryP.lift h

theorem DryP.map {x : PlaceM α} (f : α → β) (hx : DryP x) : DryP (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => DryP.pure _

theorem DryP.foldlM {σ : Type} {f : σ → α → PlaceM σ} (hf : ∀ s a, DryP (f s a)) :
    ∀ (l : List α) (s : σ), DryP (l.foldlM f s)
  | [], s => DryP.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => DryP.foldlM hf l s'

theorem DryP.arrayFoldlM {σ : Type} {f : σ → α → PlaceM σ} (hf : ∀ s a, DryP (f s a))
    (l : Array α) (s : σ) : DryP (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact DryP.foldlM hf _ s

theorem DryP.forIn {σ : Type} {f : α → σ → PlaceM (ForInStep σ)} (hf : ∀ a s, DryP (f a s)) :
    ∀ (l : List α) (s : σ), DryP (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact DryP.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact DryP.pure b
    | yield b => exact DryP.forIn hf l b

theorem DryP.arrayForIn {σ : Type} {f : α → σ → PlaceM (ForInStep σ)}
    (hf : ∀ a s, DryP (f a s)) (l : Array α) (s : σ) : DryP (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact DryP.forIn hf _ s

theorem DryP.forM {f : α → PlaceM PUnit} (hf : ∀ a, DryP (f a)) : ∀ l : List α, DryP (l.forM f)
  | [] => DryP.pure _
  | a :: l => by
    show DryP (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => DryP.forM hf l

theorem DryP.arrayForM {f : α → PlaceM PUnit} (hf : ∀ a, DryP (f a)) (l : Array α) :
    DryP (l.forM f) := by
  unfold Array.forM
  exact DryP.arrayFoldlM (fun _ a => hf a) l _

theorem DryP.mapM {f : α → PlaceM β} (hf : ∀ a, DryP (f a)) : ∀ l : List α, DryP (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact DryP.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (DryP.mapM hf l).bind fun _ => DryP.pure _

theorem DryP.arrayMapM {f : α → PlaceM β} (hf : ∀ a, DryP (f a)) (l : Array α) :
    DryP (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (DryP.mapM hf _).map _

theorem DryP.discard {x : PlaceM α} (hx : DryP x) : DryP (Functor.discard x) := by
  have e : Functor.discard x = (fun _ => PUnit.unit) <$> x := by
    unfold Functor.discard
    rw [LawfulFunctor.map_const]
    rfl
  rw [e]
  exact hx.map _

theorem DryS.modify (f : Fork → Fork) : DryS (_root_.modify f : SubM PUnit) := fun F =>
  Dry.pure (α := PUnit × Fork) (PUnit.unit, f F)

end

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `DryP x`. -/
elab "staysP_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.DryP 2 do throwError "not a goal DryP x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

open Lean Meta Elab Tactic in
/-- A routine that is written as a function of its state: takes the state in. -/
elab "stays_fun" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isAppOfArity ``Fo.DryP 2 || t.isAppOfArity ``Fo.DryS 2 || t.isAppOfArity ``Fo.DryL 2 do
    throwError "not a routine with a state"
  unless t.appArg!.isLambda do throwError "not written as a function"
  evalTactic (← `(tactic| intro _))

macro_rules | `(tactic| stays_rule) => `(tactic| first
  | (with_reducible first
      | exact DryP.pure _ | exact DryS.modify _
      | apply DryP.lift | apply DryP.monadLift | apply DryP.liftM
      | apply DryP.bind | apply DryP.map | apply DryP.discard
      | apply DryP.foldlM | apply DryP.arrayFoldlM
      | apply DryP.forIn | apply DryP.arrayForIn | apply DryP.forM | apply DryP.arrayForM
      | apply DryP.mapM | apply DryP.arrayMapM)
  | stays_fun
  | staysP_open)

theorem stays_placeAll (S : Shape) (mats : Array TMat) (nW : Nat) (g : Forest.Heard)
    (planes : Array PlaneClaim) (scores : Array Score) (d : Divide) (x : Attain) :
    DryP (placeAll S mats nW g planes scores d x) := by stays

theorem dry_tables (S : Shape) (mats : Array TMat) (nW : Nat) (g : Forest.Heard)
    (planes : Array PlaneClaim) (scores : Array Score) (d : Divide) (x : Attain) :
    Dry (tables S mats nW g planes scores d x) := by
  unfold tables
  exact Dry.bind (stays_placeAll S mats nW g planes scores d x {}) fun _ => Dry.pure _

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact dry_tables _ _ _ _ _ _ _ _)

end Fo

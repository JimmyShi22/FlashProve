-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoHushLink.lean.
Routines of a link that change neither the sub-proof's state nor the context.

`HushL x`: from every state of the link, x has `Hush` (OnBytes/Tie/Pv/Lookup/Ends/FoHush.lean); the
link's own state may change. The file has the rules for the ways in which such routines are put
together, and teaches them to the tactic `hush`. It follows
OnBytes/Tie/Pv/Lookup/Ends/FoTallyLink.lean.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoHush
import OnBytes.Model.Trees

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- From every state of the link the routine leaves the sub-proof's state and the context as they
were. -/
def HushL {α : Type} (x : LinkM α) : Prop := ∀ Lc : LinkCtx, Hush (x Lc)

section
variable {α β : Type}

theorem HushL.pure (a : α) : HushL (Pure.pure a : LinkM α) := fun Lc => Hush.pure (a, Lc)

theorem HushL.bind {x : LinkM α} {f : α → LinkM β} (hx : HushL x) (hf : ∀ a, HushL (f a)) :
    HushL (x >>= f) := fun Lc =>
  Hush.bind (x := x Lc) (f := fun p => f p.1 p.2) (hx Lc) fun p => hf p.1 p.2

theorem HushL.map {x : LinkM α} (f : α → β) (hx : HushL x) : HushL (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => HushL.pure _

theorem HushL.lift {x : SubM α} (hx : Hush x) : HushL (StateT.lift x : LinkM α) := fun Lc =>
  Hush.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Hush.pure _

theorem HushL.sub {x : SubM α} (hx : Hush x) : HushL (LinkM.sub x) := fun Lc =>
  Hush.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Hush.pure _

theorem HushL.monadLift {x : SubM α} (hx : Hush x) :
    HushL (MonadLiftT.monadLift x : LinkM α) := HushL.lift hx

theorem HushL.liftM {x : SubM α} (hx : Hush x) : HushL (_root_.liftM x : LinkM α) :=
  HushL.lift hx

theorem HushL.monadLiftB {b : Blk α} (hb : HushB b) : HushL (MonadLiftT.monadLift b : LinkM α) :=
  HushL.lift (Hush.lift hb)

theorem HushL.liftMB {b : Blk α} (hb : HushB b) : HushL (_root_.liftM b : LinkM α) :=
  HushL.lift (Hush.lift hb)

theorem HushL.get : HushL (MonadState.get : LinkM LinkCtx) := fun Lc => Hush.pure (Lc, Lc)

theorem HushL.set (s : LinkCtx) : HushL (MonadStateOf.set s : LinkM PUnit) := by
  intro _
  exact Hush.pure (α := PUnit × LinkCtx) (PUnit.unit, s)

theorem HushL.modify (f : LinkCtx → LinkCtx) : HushL (_root_.modify f : LinkM PUnit) := by
  intro Lc
  exact Hush.pure (α := PUnit × LinkCtx) (PUnit.unit, f Lc)

theorem HushL.fn {x : LinkCtx → SubM (α × LinkCtx)} (h : ∀ Lc, Hush (x Lc)) :
    HushL (x : LinkM α) := h

theorem HushL.forIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)} (hf : ∀ a s, HushL (f a s)) :
    ∀ (l : List α) (s : σ), HushL (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact HushL.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact HushL.pure b
    | yield b => exact HushL.forIn hf l b

theorem HushL.arrayForIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)}
    (hf : ∀ a s, HushL (f a s)) (l : Array α) (s : σ) : HushL (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact HushL.forIn hf _ s

theorem HushL.foldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, HushL (f s a)) :
    ∀ (l : List α) (s : σ), HushL (l.foldlM f s)
  | [], s => HushL.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => HushL.foldlM hf l s'

theorem HushL.arrayFoldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, HushL (f s a))
    (l : Array α) (s : σ) : HushL (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact HushL.foldlM hf _ s

theorem HushL.forM {f : α → LinkM PUnit} (hf : ∀ a, HushL (f a)) :
    ∀ l : List α, HushL (l.forM f)
  | [] => HushL.pure _
  | a :: l => by
    show HushL (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => HushL.forM hf l

theorem HushL.arrayForM {f : α → LinkM PUnit} (hf : ∀ a, HushL (f a)) (l : Array α) :
    HushL (l.forM f) := by
  unfold Array.forM
  exact HushL.arrayFoldlM (fun _ a => hf a) l _

end

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `HushL x`. -/
elab "hushL_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.HushL 2 do throwError "not a goal HushL x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if n == ``LinkM.sub then throwError "a lifted routine"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

macro_rules | `(tactic| hush_rule) => `(tactic| with_reducible first
  | exact HushL.pure _ | exact HushL.get | exact HushL.set _ | exact HushL.modify _
  | apply HushL.monadLiftB | apply HushL.liftMB
  | apply HushL.sub | apply HushL.lift | apply HushL.monadLift | apply HushL.liftM
  | apply HushL.bind | apply HushL.map
  | apply HushL.forIn | apply HushL.arrayForIn | apply HushL.foldlM | apply HushL.arrayFoldlM
  | apply HushL.forM | apply HushL.arrayForM)

macro_rules | `(tactic| hush_open) => `(tactic| hushL_open)

end Fo

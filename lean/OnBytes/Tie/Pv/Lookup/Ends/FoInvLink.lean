-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean.
Routines of a link that keep every property of the state that has `Prim`.

A routine of a link (LinkM) is a routine of the sub-proof with one more state, the link's.
`InvL I x`: from every state of the link, x has `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean). The
file has the rules
for the ways in which such routines are put together, and teaches them to the tactic `inv`.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvLook
import OnBytes.Model.Trees

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun


/-- From every state of the link the routine keeps the property I of the sub-proof's state. -/
def InvL {α : Type} (I : Fork → Prop) (x : LinkM α) : Prop :=
  ∀ Lc : LinkCtx, Inv I (x Lc)

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

section
variable {α β : Type}

theorem InvL.pure (a : α) : InvL I (Pure.pure a : LinkM α) := fun Lc => Inv.pure (a, Lc)

theorem InvL.bind {x : LinkM α} {f : α → LinkM β} (hx : InvL I x) (hf : ∀ a, InvL I (f a)) :
    InvL I (x >>= f) := fun Lc =>
  Inv.bind (x := x Lc) (f := fun p => f p.1 p.2) (hx Lc) fun p => hf p.1 p.2

theorem InvL.map {x : LinkM α} (f : α → β) (hx : InvL I x) : InvL I (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => InvL.pure _

theorem InvL.lift {x : SubM α} (hx : Inv I x) : InvL I (StateT.lift x : LinkM α) := fun Lc =>
  Inv.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Inv.pure _

theorem InvL.sub {x : SubM α} (hx : Inv I x) : InvL I (LinkM.sub x) := fun Lc =>
  Inv.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Inv.pure _

theorem InvL.monadLift {x : SubM α} (hx : Inv I x) :
    InvL I (MonadLiftT.monadLift x : LinkM α) := InvL.lift hx

theorem InvL.liftM {x : SubM α} (hx : Inv I x) : InvL I (_root_.liftM x : LinkM α) :=
  InvL.lift hx

theorem InvL.monadLiftB (b : Blk α) : InvL I (MonadLiftT.monadLift b : LinkM α) :=
  InvL.lift (Inv.lift b)

theorem InvL.liftMB (b : Blk α) : InvL I (_root_.liftM b : LinkM α) :=
  InvL.lift (Inv.lift b)

theorem InvL.get : InvL I (MonadState.get : LinkM LinkCtx) := fun Lc => Inv.pure (Lc, Lc)

theorem InvL.set (s : LinkCtx) : InvL I (MonadStateOf.set s : LinkM PUnit) := by
  intro _
  exact Inv.pure (α := PUnit × LinkCtx) (PUnit.unit, s)

theorem InvL.modify (f : LinkCtx → LinkCtx) : InvL I (_root_.modify f : LinkM PUnit) := by
  intro Lc
  exact Inv.pure (α := PUnit × LinkCtx) (PUnit.unit, f Lc)

theorem InvL.fn {x : LinkCtx → SubM (α × LinkCtx)} (h : ∀ Lc, Inv I (x Lc)) :
    InvL I (x : LinkM α) := h

theorem InvL.forIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)} (hf : ∀ a s, InvL I (f a s)) :
    ∀ (l : List α) (s : σ), InvL I (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact InvL.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact InvL.pure b
    | yield b => exact InvL.forIn hf l b

theorem InvL.arrayForIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)}
    (hf : ∀ a s, InvL I (f a s)) (l : Array α) (s : σ) : InvL I (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact InvL.forIn hf _ s

theorem InvL.foldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, InvL I (f s a)) :
    ∀ (l : List α) (s : σ), InvL I (l.foldlM f s)
  | [], s => InvL.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => InvL.foldlM hf l s'

theorem InvL.arrayFoldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, InvL I (f s a))
    (l : Array α) (s : σ) : InvL I (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact InvL.foldlM hf _ s

theorem InvL.forM {f : α → LinkM PUnit} (hf : ∀ a, InvL I (f a)) :
    ∀ l : List α, InvL I (l.forM f)
  | [] => InvL.pure _
  | a :: l => by
    show InvL I (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => InvL.forM hf l

theorem InvL.arrayForM {f : α → LinkM PUnit} (hf : ∀ a, InvL I (f a)) (l : Array α) :
    InvL I (l.forM f) := by
  unfold Array.forM
  exact InvL.arrayFoldlM (fun _ a => hf a) l _

end

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `InvL I x`. -/
elab "invL_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.InvL 3 do throwError "not a goal InvL I x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if n == ``LinkM.sub then throwError "a lifted routine"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible first
  | exact InvL.pure _ | exact InvL.get | exact InvL.set _ | exact InvL.modify _
  | exact InvL.monadLiftB _ | exact InvL.liftMB _
  | apply InvL.sub | apply InvL.lift | apply InvL.monadLift | apply InvL.liftM
  | apply InvL.bind | apply InvL.map
  | apply InvL.forIn | apply InvL.arrayForIn | apply InvL.foldlM | apply InvL.arrayFoldlM
  | apply InvL.forM | apply InvL.arrayForM)

macro_rules | `(tactic| inv_open) => `(tactic| invL_open)

theorem InvL.call (f : ChainCheck → Blk ChainCheck) : InvL I (LinkM.call f) := by
  intro Lc
  show Inv I (SubM.must _ >>= fun _ => _)
  inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible exact InvL.call _)

theorem InvL.rootInH (trees : List ℕ) : InvL I (rootInH trees) := by inv
theorem InvL.t2Batch (used : ℕ) : InvL I (t2Batch used) := by inv

end Fo

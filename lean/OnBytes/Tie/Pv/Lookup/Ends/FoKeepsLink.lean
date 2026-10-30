-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean.
Routines of a link that keep what lies under the filled slots.

A routine of a link (LinkM) is a routine of the sub-proof with one more state, the link's.
`KeepsL x`: from every state of the link, x has `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean).
The file has the rules for the ways in which such routines are put together, and gives them to the
tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean), which from here on also works on a
goal `KeepsL x`. It proves `KeepsL` of LinkM.call, rootInH and t2Batch (OnBytes/Model/Trees.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsLook
import OnBytes.Model.Trees

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- From every state of the link the routine keeps what lies under the filled slots. -/
def KeepsL {α : Type} (x : LinkM α) : Prop := ∀ Lc : LinkCtx, Keeps (x Lc)

section
variable {α β : Type}

theorem KeepsL.pure (a : α) : KeepsL (Pure.pure a : LinkM α) := fun Lc => Keeps.pure (a, Lc)

theorem KeepsL.bind {x : LinkM α} {f : α → LinkM β} (hx : KeepsL x) (hf : ∀ a, KeepsL (f a)) :
    KeepsL (x >>= f) := fun Lc =>
  Keeps.bind (x := x Lc) (f := fun p => f p.1 p.2) (hx Lc) fun p => hf p.1 p.2

theorem KeepsL.map {x : LinkM α} (f : α → β) (hx : KeepsL x) : KeepsL (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => KeepsL.pure _

theorem KeepsL.lift {x : SubM α} (hx : Keeps x) : KeepsL (StateT.lift x : LinkM α) := fun Lc =>
  Keeps.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Keeps.pure _

theorem KeepsL.sub {x : SubM α} (hx : Keeps x) : KeepsL (LinkM.sub x) := fun Lc =>
  Keeps.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Keeps.pure _

theorem KeepsL.monadLift {x : SubM α} (hx : Keeps x) :
    KeepsL (MonadLiftT.monadLift x : LinkM α) := KeepsL.lift hx

theorem KeepsL.liftM {x : SubM α} (hx : Keeps x) : KeepsL (_root_.liftM x : LinkM α) :=
  KeepsL.lift hx

theorem KeepsL.monadLiftB (b : Blk α) : KeepsL (MonadLiftT.monadLift b : LinkM α) :=
  KeepsL.lift (Keeps.lift b)

theorem KeepsL.liftMB (b : Blk α) : KeepsL (_root_.liftM b : LinkM α) :=
  KeepsL.lift (Keeps.lift b)

theorem KeepsL.get : KeepsL (MonadState.get : LinkM LinkCtx) := fun Lc => Keeps.pure (Lc, Lc)

theorem KeepsL.set (s : LinkCtx) : KeepsL (MonadStateOf.set s : LinkM PUnit) := by
  intro _
  exact Keeps.pure (α := PUnit × LinkCtx) (PUnit.unit, s)

theorem KeepsL.modify (f : LinkCtx → LinkCtx) : KeepsL (_root_.modify f : LinkM PUnit) := by
  intro Lc
  exact Keeps.pure (α := PUnit × LinkCtx) (PUnit.unit, f Lc)

theorem KeepsL.fn {x : LinkCtx → SubM (α × LinkCtx)} (h : ∀ Lc, Keeps (x Lc)) :
    KeepsL (x : LinkM α) := h

theorem KeepsL.forIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)} (hf : ∀ a s, KeepsL (f a s)) :
    ∀ (l : List α) (s : σ), KeepsL (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact KeepsL.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact KeepsL.pure b
    | yield b => exact KeepsL.forIn hf l b

theorem KeepsL.arrayForIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)}
    (hf : ∀ a s, KeepsL (f a s)) (l : Array α) (s : σ) : KeepsL (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact KeepsL.forIn hf _ s

theorem KeepsL.foldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, KeepsL (f s a)) :
    ∀ (l : List α) (s : σ), KeepsL (l.foldlM f s)
  | [], s => KeepsL.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => KeepsL.foldlM hf l s'

theorem KeepsL.arrayFoldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, KeepsL (f s a))
    (l : Array α) (s : σ) : KeepsL (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact KeepsL.foldlM hf _ s

theorem KeepsL.forM {f : α → LinkM PUnit} (hf : ∀ a, KeepsL (f a)) :
    ∀ l : List α, KeepsL (l.forM f)
  | [] => KeepsL.pure _
  | a :: l => by
    show KeepsL (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => KeepsL.forM hf l

theorem KeepsL.arrayForM {f : α → LinkM PUnit} (hf : ∀ a, KeepsL (f a)) (l : Array α) :
    KeepsL (l.forM f) := by
  unfold Array.forM
  exact KeepsL.arrayFoldlM (fun _ a => hf a) l _

end

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `KeepsL x`. -/
elab "keepsL_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.KeepsL 2 do throwError "not a goal KeepsL x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if n == ``LinkM.sub then throwError "a lifted routine"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible first
  | exact KeepsL.pure _ | exact KeepsL.get | exact KeepsL.set _ | exact KeepsL.modify _
  | exact KeepsL.monadLiftB _ | exact KeepsL.liftMB _
  | apply KeepsL.sub | apply KeepsL.lift | apply KeepsL.monadLift | apply KeepsL.liftM
  | apply KeepsL.bind | apply KeepsL.map
  | apply KeepsL.forIn | apply KeepsL.arrayForIn | apply KeepsL.foldlM | apply KeepsL.arrayFoldlM
  | apply KeepsL.forM | apply KeepsL.arrayForM)

macro_rules | `(tactic| keeps_open) => `(tactic| keepsL_open)

theorem KeepsL.call (f : ChainCheck → Blk ChainCheck) : KeepsL (LinkM.call f) := by
  intro Lc
  show Keeps (SubM.must _ >>= fun _ => _)
  keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact KeepsL.call _)

theorem KeepsL.rootInH (trees : List ℕ) : KeepsL (rootInH trees) := by keeps
theorem KeepsL.t2Batch (used : ℕ) : KeepsL (t2Batch used) := by keeps

end Fo

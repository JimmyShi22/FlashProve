-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTallyLink.lean.
Routines of a link that leave the number of claims added and the number of claims planned as they
were.

A routine of a link (LinkM) is a routine of the sub-proof with one more state, the link's.
`TallyL x`: from every state of the link, x has `Tally` (OnBytes/Tie/Pv/Lookup/Ends/FoTally.lean).
The file has the rules for the ways in which such routines are put together, teaches them to the
tactic `tally`, and proves the property of LinkM.call, rootInH and t2Batch. It follows
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean, which does the same for another property.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTally
import OnBytes.Model.Trees

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- From every state of the link the routine leaves the two numbers as they were. -/
def TallyL {α : Type} (x : LinkM α) : Prop := ∀ Lc : LinkCtx, Tally (x Lc)

section
variable {α β : Type}

theorem TallyL.pure (a : α) : TallyL (Pure.pure a : LinkM α) := fun Lc => Tally.pure (a, Lc)

theorem TallyL.bind {x : LinkM α} {f : α → LinkM β} (hx : TallyL x) (hf : ∀ a, TallyL (f a)) :
    TallyL (x >>= f) := fun Lc =>
  Tally.bind (x := x Lc) (f := fun p => f p.1 p.2) (hx Lc) fun p => hf p.1 p.2

theorem TallyL.map {x : LinkM α} (f : α → β) (hx : TallyL x) : TallyL (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => TallyL.pure _

theorem TallyL.lift {x : SubM α} (hx : Tally x) : TallyL (StateT.lift x : LinkM α) := fun Lc =>
  Tally.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Tally.pure _

theorem TallyL.sub {x : SubM α} (hx : Tally x) : TallyL (LinkM.sub x) := fun Lc =>
  Tally.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Tally.pure _

theorem TallyL.monadLift {x : SubM α} (hx : Tally x) :
    TallyL (MonadLiftT.monadLift x : LinkM α) := TallyL.lift hx

theorem TallyL.liftM {x : SubM α} (hx : Tally x) : TallyL (_root_.liftM x : LinkM α) :=
  TallyL.lift hx

theorem TallyL.monadLiftB (b : Blk α) : TallyL (MonadLiftT.monadLift b : LinkM α) :=
  TallyL.lift (Tally.lift b)

theorem TallyL.liftMB (b : Blk α) : TallyL (_root_.liftM b : LinkM α) :=
  TallyL.lift (Tally.lift b)

theorem TallyL.get : TallyL (MonadState.get : LinkM LinkCtx) := fun Lc => Tally.pure (Lc, Lc)

theorem TallyL.set (s : LinkCtx) : TallyL (MonadStateOf.set s : LinkM PUnit) := by
  intro _
  exact Tally.pure (α := PUnit × LinkCtx) (PUnit.unit, s)

theorem TallyL.modify (f : LinkCtx → LinkCtx) : TallyL (_root_.modify f : LinkM PUnit) := by
  intro Lc
  exact Tally.pure (α := PUnit × LinkCtx) (PUnit.unit, f Lc)

theorem TallyL.fn {x : LinkCtx → SubM (α × LinkCtx)} (h : ∀ Lc, Tally (x Lc)) :
    TallyL (x : LinkM α) := h

theorem TallyL.forIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)} (hf : ∀ a s, TallyL (f a s)) :
    ∀ (l : List α) (s : σ), TallyL (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact TallyL.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact TallyL.pure b
    | yield b => exact TallyL.forIn hf l b

theorem TallyL.arrayForIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)}
    (hf : ∀ a s, TallyL (f a s)) (l : Array α) (s : σ) : TallyL (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact TallyL.forIn hf _ s

theorem TallyL.foldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, TallyL (f s a)) :
    ∀ (l : List α) (s : σ), TallyL (l.foldlM f s)
  | [], s => TallyL.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => TallyL.foldlM hf l s'

theorem TallyL.arrayFoldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, TallyL (f s a))
    (l : Array α) (s : σ) : TallyL (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact TallyL.foldlM hf _ s

theorem TallyL.forM {f : α → LinkM PUnit} (hf : ∀ a, TallyL (f a)) :
    ∀ l : List α, TallyL (l.forM f)
  | [] => TallyL.pure _
  | a :: l => by
    show TallyL (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => TallyL.forM hf l

theorem TallyL.arrayForM {f : α → LinkM PUnit} (hf : ∀ a, TallyL (f a)) (l : Array α) :
    TallyL (l.forM f) := by
  unfold Array.forM
  exact TallyL.arrayFoldlM (fun _ a => hf a) l _

end

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `TallyL x`. -/
elab "tallyL_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.TallyL 2 do throwError "not a goal TallyL x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if n == ``LinkM.sub then throwError "a lifted routine"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

macro_rules | `(tactic| tally_rule) => `(tactic| with_reducible first
  | exact TallyL.pure _ | exact TallyL.get | exact TallyL.set _ | exact TallyL.modify _
  | exact TallyL.monadLiftB _ | exact TallyL.liftMB _
  | apply TallyL.sub | apply TallyL.lift | apply TallyL.monadLift | apply TallyL.liftM
  | apply TallyL.bind | apply TallyL.map
  | apply TallyL.forIn | apply TallyL.arrayForIn | apply TallyL.foldlM | apply TallyL.arrayFoldlM
  | apply TallyL.forM | apply TallyL.arrayForM)

macro_rules | `(tactic| tally_open) => `(tactic| tallyL_open)

theorem TallyL.call (f : ChainCheck → Blk ChainCheck) : TallyL (LinkM.call f) := by
  intro Lc
  show Tally (SubM.must _ >>= fun _ => _)
  tally

macro_rules | `(tactic| tally_rule) => `(tactic| with_reducible exact TallyL.call _)

theorem TallyL.rootInH (trees : List Nat) : TallyL (rootInH trees) := by tally
theorem TallyL.t2Batch (used : Nat) : TallyL (t2Batch used) := by tally

end Fo

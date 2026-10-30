-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/FrameN.lean: THE NOTING ROUTINES READ NO ROUND AND NO CALL
NOTED BEFORE: a routine of Johnson/G/Calls.lean | Johnson/Desc/First/Link/RowsRun.lean that returns
from (cs, p) returns the like from (C ++ cs, p with the rounds R in front). Theorems. A law file; no
running text imports it.
  `Fr x`        wherever x returns ((a, cs'), q) from (cs, p): q.set = p.set, and from (C ++ cs,
                under R p) it returns ((a, C ++ cs'), under R q).
  `fr_pure`, `fr_bind`, `fr_ite`, `fr_forIn`, `fr_lift`, `fr_note`, `fr_noteV`; the tactic `frn`;
  then each routine by its name: among them `fr_nArm`, `fr_nFrameA`, `fr_nRanges`.
`fr_forIn` goes step for step as the older `keeps_forIn` (OnBytes/Iop/DrySizes.lean).
Limits. A CONDITIONAL ON RETURNS: of a routine that refuses nothing is said. Nothing on soundness or
on hiding.

-/
import Johnson.AtFull.Rows.FrameP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- A noting routine that reads no round and no call noted before, and leaves the setting. -/
def Fr {α : Type} (x : N α) : Prop :=
  ∀ cs p a cs' q, (x.run cs).run p = .ok ((a, cs'), q) →
    q.set = p.set ∧ ∀ C R, (x.run (C ++ cs)).run (under R p) = .ok ((a, C ++ cs'), under R q)

section
variable {α β : Type}

theorem fr_pure (a : α) : Fr (pure a : N α) := by
  intro cs p b cs' q h
  cases h
  exact ⟨rfl, fun _ _ => rfl⟩

theorem fr_bind {x : N α} {f : α → N β} (hx : Fr x) (hf : ∀ a, Fr (f a)) : Fr (x >>= f) := by
  intro cs p b cs' q h
  obtain ⟨a, cs1, p1, h1, h2⟩ := run_bind_ok h
  obtain ⟨s1, g1⟩ := hx cs p a cs1 p1 h1
  obtain ⟨s2, g2⟩ := hf a cs1 p1 b cs' q h2
  refine ⟨s2.trans s1, fun C R => ?_⟩
  rw [StateT.run_bind, StateT.run_bind, g1 C R]
  exact g2 C R

theorem fr_ite {c : Prop} [Decidable c] {x y : N α} (hx : Fr x) (hy : Fr y) :
    Fr (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem fr_lift {y : Planning α} (hy : FrP y) : Fr (liftM y : N α) := by
  intro cs p b cs' q h
  have h' : (y.run p >>= fun r => (pure ((r.1, cs), r.2) : Except String _)) =
      .ok ((b, cs'), q) := h
  obtain ⟨⟨a, q1⟩, h1, h2⟩ := exc_bind h'
  cases h2
  obtain ⟨s1, g1⟩ := hy p a q1 h1
  refine ⟨s1, fun C R => ?_⟩
  show (y.run (under R p) >>= fun r => (pure ((r.1, C ++ cs), r.2) : Except String _)) = _
  rw [g1 R]
  rfl

theorem fr_noteV (c : Call) {y : Planning α} (hy : FrP y) : Fr (noteV c y) := by
  intro cs p b cs' q h
  have h' : (y.run p >>= fun r => (pure ((r.1, cs.push c), r.2) : Except String _)) =
      .ok ((b, cs'), q) := h
  obtain ⟨⟨a, q1⟩, h1, h2⟩ := exc_bind h'
  cases h2
  obtain ⟨s1, g1⟩ := hy p a q1 h1
  refine ⟨s1, fun C R => ?_⟩
  show (y.run (under R p) >>= fun r => (pure ((r.1, (C ++ cs).push c), r.2) : Except String _)) = _
  rw [g1 R, app_push]
  rfl

theorem fr_forIn {γ : Type} {f : γ → PUnit → N (ForInStep PUnit)} (h : ∀ a r, Fr (f a r)) :
    ∀ (l : List γ) (b : PUnit), Fr (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact fr_pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine fr_bind (h a b) fun s => ?_
    cases s with
    | done b' => exact fr_pure b'
    | yield b' => exact fr_forIn h l b'

end

theorem fr_note (c : Call) : Fr (note c) := by
  intro cs p b cs' q h
  have h' : (c.plan.run p >>= fun r => (pure ((r.1, cs.push c), r.2) : Except String _)) =
      .ok ((b, cs'), q) := h
  obtain ⟨⟨a, q1⟩, h1, h2⟩ := exc_bind h'
  cases h2
  obtain ⟨s1, g1⟩ := frP_plan c p a q1 h1
  refine ⟨s1, fun C R => ?_⟩
  show (c.plan.run (under R p) >>= fun r =>
      (pure ((r.1, (C ++ cs).push c), r.2) : Except String _)) = _
  rw [g1 R, app_push]
  rfl

/-- One step through a noting routine. Each routine's own lemma is added below it. -/
syntax "frn_step" : tactic
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible intro _)
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible assumption)
macro_rules | `(tactic| frn_step) => `(tactic| (with_reducible refine fr_lift ?_) <;> frp)
macro_rules | `(tactic| frn_step) => `(tactic| (with_reducible refine fr_noteV _ ?_) <;> frp)
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_note _)
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_pure _)
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible apply fr_forIn)
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible apply fr_ite)
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible apply fr_bind)

/-- Steps through a noting routine. -/
macro "frn" : tactic => `(tactic| (try dsimp only) <;> repeat' frn_step)

theorem fr_nLookup (x : LookupSize) : Fr (nLookup x) := by
  unfold nLookup
  frn
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nLookup _)

theorem fr_nForest (x : ForestSize) : Fr (nForest x) := fr_nLookup _
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nForest _)

theorem fr_nSmall (x : SmallSize) (which : Nat) : Fr (nSmall x which) := by
  unfold nSmall
  frn
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nSmall _ _)

theorem fr_nLayerOwn (x : LayerRounds) : Fr (nLayerOwn x) := by
  unfold nLayerOwn
  frn
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nLayerOwn _)

theorem fr_nLayer (look : ForestSize) (x : LayerRounds) (small : SmallSize) (claims moment : Nat) :
    Fr (nLayer look x small claims moment) := by
  unfold nLayer
  frn

theorem fr_nAttentionOwn (x : AttentionRounds) : Fr (nAttentionOwn x) := by
  unfold nAttentionOwn
  frn
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nAttentionOwn _)

theorem fr_nAttention (look : ForestSize) (x : AttentionRounds) (small : SmallSize) (moment : Nat) :
    Fr (nAttention look x small moment) := by
  unfold nAttention
  frn

theorem fr_nHead (look : ForestSize) (x : HeadRounds) (small : SmallSize) (moment : Nat) :
    Fr (nHead look x small moment) := by
  unfold nHead
  frn

/-- **An arm's routine.** -/
theorem fr_nArm (a : Arm) (moment : Nat) : Fr (nArm a moment) := by
  cases a with
  | head l x s => exact fr_nHead l x s moment
  | layer l x s c => exact fr_nLayer l x s c moment
  | attention l x s => exact fr_nAttention l x s moment
  | none => exact fr_lift (frP_needs _ _)
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nArm _ _)

theorem fr_nStages (f : Nat) (m : Bool) :
    ∀ (first : Bool) (st : List StageSize), Fr (nStages f m first st)
  | first, x :: y :: rest => by
    have := fr_nStages f m false (y :: rest)
    unfold nStages
    frn
  | _, [x] => by
    unfold nStages
    frn
  | _, [] => by
    unfold nStages
    frn
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nStages _ _ _ _)

theorem fr_nIopp (st : List StageSize) (rows f : Nat) (m : Bool) : Fr (nIopp st rows f m) := by
  unfold nIopp
  frn
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nIopp _ _ _ _)

theorem fr_nReqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) (ownRound : Bool) : Fr (nReqSend codes sent group atStart riders ownRound) := by
  unfold nReqSend
  frn
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nReqSend _ _ _ _ _ _)

theorem fr_nMomentsA (A : Nat → Arm) (z : ProofSized) (l : Nat) (msgs : List ReqMessage) :
    ∀ fuel moment, Fr (nMomentsA A z l msgs fuel moment)
  | 0, _ => fr_pure _
  | fuel + 1, moment => by
    have := fr_nMomentsA A z l msgs fuel (moment + 1)
    unfold nMomentsA
    frn
macro_rules | `(tactic| frn_step) => `(tactic| with_reducible exact fr_nMomentsA _ _ _ _ _ _)

/-- **The frame.** -/
theorem fr_nFrameA (A : Nat → Arm) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat) (before : GroupSize),
    Fr (nFrameA A z l gs links open_ before)
  | [], _, _, _, _ => by
    unfold nFrameA
    exact fr_pure _
  | g :: gs, l, links, open_, before => by
    have ih := fun c => fr_nFrameA A z gs (l + 1) (links.drop 1) (open_.drop 1) c
    unfold nFrameA
    cases links.head? with
    | none =>
      frn
    | some lk =>
      frn
      all_goals exact ih _

theorem fr_nLinFirst (codes : Codes) (x : LinSized) : Fr (nLinFirst codes x) := by
  unfold nLinFirst
  frn

theorem fr_nLinShared (codes : Codes) (x : LinSized) : Fr (nLinShared codes x) := by
  unfold nLinShared
  frn

theorem fr_nLinSecond (x : LinSized) : Fr (nLinSecond x) := by
  unfold nLinSecond
  frn

theorem fr_nLinkPlan (x : LinkSized) : Fr (nLinkPlan x) := by
  unfold nLinkPlan
  frn

open OnBytes.Plan in
/-- **The ranges.** -/
theorem fr_nRanges (codes : Codes) (z : RangesSized) : Fr (nRanges codes z) := by
  unfold nRanges
  frn

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.fr_bind
#print axioms VerifiableInference.Desc.LinkJoin.fr_note
#print axioms VerifiableInference.Desc.LinkJoin.fr_nArm
#print axioms VerifiableInference.Desc.LinkJoin.fr_nFrameA
#print axioms VerifiableInference.Desc.LinkJoin.fr_nLinFirst
#print axioms VerifiableInference.Desc.LinkJoin.fr_nLinShared
#print axioms VerifiableInference.Desc.LinkJoin.fr_nLinSecond
#print axioms VerifiableInference.Desc.LinkJoin.fr_nLinkPlan
#print axioms VerifiableInference.Desc.LinkJoin.fr_nRanges

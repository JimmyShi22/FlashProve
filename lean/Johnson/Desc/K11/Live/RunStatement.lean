-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Live/RunStatement.lean: THE RUN OF CLAIMS OF THE MERGE OF THE CLAIMS ON THE WEIGHTS
(`headMergeClaim`, Johnson/Desc/First/Fork/MergeKind.lean): WHICH SLOTS ITS ONE CLAIM NAMES, AND
WHERE ITS COEFFICIENTS ON THEM ARE NOT 0: one definition of a condition on the verifier's state, and
STATEMENTS: seven, each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and none of
the seven is one of the library's goals: they are lemmas' statements. The texts are the
description's; no prover is named.

Why. The batching behind the head's link adds the runs' claims under powers of one challenge; a
count on that challenge wants that on each slot some claim bears a coefficient that is not 0
(`liveAt`), that each claim which names the slot takes its own number (`plainAt`), and that no claim
names the slot of the merge's end value (`unnamedAt`): three tests with code on a list of claims
(Johnson/Desc/K9/Honest/SlotsLive.lean). Here: what the merge's own run gives of the three.

The run yields one claim: the form that the merge's masked sumcheck leaves (`Psc.rowForm`,
OnBytes/Model/Psc.lean). It names the 2 lk + 2 slots of the hiding polynomial's coefficients, from
the sumcheck's first slot on, and the one slot of the sumcheck's start. The coefficient at variable
l and degree t is γ_l ^ t times the product of the later γ; the last two are 1 and β (`hidingWalk`,
OnBytes/Iop/Psc.lean); on the start's slot it is the start's own coefficient times -(ε times the
product of all γ). γ: the challenges of the lk rounds; β: that of the round in the further variable;
ε: the factor of the summand.

  `MergeLive lk first sv s`   the condition: s stands in the head's link; what the merge left is
                              laid; of its sumcheck: the first slot is first, lk plain variables of
                              degree 2 and the further one, lk + 1 challenges; the start names one
                              slot, sv, BELOW first, with a coefficient that reads other than 0; the
                              end value's slot is first + 2 lk + 2; AND ε AND EVERY ONE OF THE
                              lk + 1 CHALLENGES READ AS ELEMENTS OTHER THAN 0
  `WalkLive`                  on `hidingWalk` alone: at plain variables of degree 2 and the further
                              one, at challenges that all read other than 0: every coefficient, and
                              the product, read other than 0
  `MergeRunLive`              under the condition, at every yes of the run: `liveAt` at each slot
                              from first to first + 2 lk + 1
  `MergeRunLiveStart`         under the condition, at every yes of the run: `liveAt` at sv
  `MergeRunPlain`             at every yes of the run, with no condition: `plainAt` at every slot
  `MergeRunUnnamed`           under the condition, at every yes of the run: `unnamedAt` at the end
                              value's slot
  `MergeRunHands`             under the condition, at every yes of the run: the condition holds
                              behind
  `MergeLiveSlot`             under the condition: the slot of the merge's end value, as the
                              batching's tests read it (`mergeOf`,
                              Johnson/Desc/First/Batch/AtS.lean), is first + 2 lk + 2

Limits. The condition is shown at no state here; `MergeLiveBehindRaw`
(Johnson/Desc/K11/Front/LiveBehindStatement.lean) has it, at 18 and 3531, behind the merge's
decision at a reached state, under its own premises. That the challenges in what the merge left are
those that the merge's rounds drew is not said here; nor how often one of them is 0. Nothing on any
property.
-/
import Johnson.Desc.First.Fork.MergeKind
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.K9.Honest.SlotsLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Live
open OnBytes (E)
open OnBytes.Model (Reading WsForkOut)
open OnBytes.Psc (Weight hidingWalk)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (mergeOf)
open VerifiableInference.Desc.K9H (liveAt plainAt unnamedAt)

/-- **The condition.** lk: the number of column bits. first: the sumcheck's first slot. sv: the one
slot that the sumcheck's start names. -/
def MergeLive (lk first sv : Nat) (s : S) : Prop :=
  ∃ (a : HeadOwn) (wo : WsForkOut) (c : E), s.here = .head a ∧ a.wo = some wo ∧
    wo.p.first = first ∧
    wo.p.vars.toList = List.replicate lk (Weight.plain 3) ++ [Weight.atZero 2] ∧
    wo.p.r.size = lk + 1 ∧ wo.p.start.slots.toList = [(sv, c)] ∧ Reading.gl.val c ≠ 0 ∧
    sv < first ∧ wo.sFv = first + 2 * lk + 2 ∧ Reading.gl.val wo.p.eps ≠ 0 ∧
    ∀ e ∈ wo.p.r.toList, Reading.gl.val e ≠ 0

/-- The statement on the hiding polynomial's linear form. gs: the rounds' challenges. b: that of the
round in the further variable. Not proved here; a lemma's statement, none of the library's goals. -/
def WalkLive : Prop :=
  ∀ (gs : List E) (b : E), (∀ g ∈ gs, Reading.gl.val g ≠ 0) → Reading.gl.val b ≠ 0 →
    (∀ e ∈ (hidingWalk (gs.map (fun g => (Weight.plain 3, g)) ++ [(Weight.atZero 2, b)])).1,
      Reading.gl.val e ≠ 0) ∧
    Reading.gl.val
      (hidingWalk (gs.map (fun g => (Weight.plain 3, g)) ++ [(Weight.atZero 2, b)])).2 ≠ 0

/-- The statement on the window. Not proved here; a lemma's statement, none of the library's goals.
-/
def MergeRunLive : Prop :=
  ∀ (lk first sv n : Nat) (s : S) (z : List Claim × S), MergeLive lk first sv s →
    headMergeClaim n s = .ok z →
    ∀ j, first ≤ j → j < first + 2 * lk + 2 → liveAt z.1 j = true

/-- The statement on the start's slot. Not proved here; a lemma's statement, none of the library's
goals. -/
def MergeRunLiveStart : Prop :=
  ∀ (lk first sv n : Nat) (s : S) (z : List Claim × S), MergeLive lk first sv s →
    headMergeClaim n s = .ok z → liveAt z.1 sv = true

/-- The statement that the claim takes its own number. Not proved here; a lemma's statement, none of
the library's goals. -/
def MergeRunPlain : Prop :=
  ∀ (n : Nat) (s : S) (z : List Claim × S), headMergeClaim n s = .ok z →
    ∀ j, plainAt z.1 j = true

/-- The statement on the end value's slot. Not proved here; a lemma's statement, none of the
library's goals. -/
def MergeRunUnnamed : Prop :=
  ∀ (lk first sv n : Nat) (s : S) (z : List Claim × S), MergeLive lk first sv s →
    headMergeClaim n s = .ok z → unnamedAt z.1 (first + 2 * lk + 2) = true

/-- The statement that the run hands the condition on. Not proved here; a lemma's statement, none of
the library's goals. -/
def MergeRunHands : Prop :=
  ∀ (lk first sv n : Nat) (s : S) (z : List Claim × S), MergeLive lk first sv s →
    headMergeClaim n s = .ok z → MergeLive lk first sv z.2

/-- The statement on the slot that the batching's tests read. Not proved here; a lemma's statement,
none of the library's goals. -/
def MergeLiveSlot : Prop :=
  ∀ (lk first sv : Nat) (s : S), MergeLive lk first sv s →
    mergeOf s = some (first + 2 * lk + 2)

end Johnson.Desc.First.ForkMerge.Live

#print axioms Johnson.Desc.First.ForkMerge.Live.MergeLive
#print axioms Johnson.Desc.First.ForkMerge.Live.WalkLive
#print axioms Johnson.Desc.First.ForkMerge.Live.MergeRunLive
#print axioms Johnson.Desc.First.ForkMerge.Live.MergeRunLiveStart
#print axioms Johnson.Desc.First.ForkMerge.Live.MergeRunPlain
#print axioms Johnson.Desc.First.ForkMerge.Live.MergeRunUnnamed
#print axioms Johnson.Desc.First.ForkMerge.Live.MergeRunHands
#print axioms Johnson.Desc.First.ForkMerge.Live.MergeLiveSlot

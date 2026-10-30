-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/PlanRowsAtHeadStatement.lean: UNDER THE LIBRARY's HEAD THE NUMBER OF ROWS THAT EACH OF
THE 25 SEGMENTS' PLANS GIVES ITS BATCHING's ROUND IS THE WRITTEN NUMBER `rowsAtLink l`
(Johnson/P1K8R/RowsAtLink.lean): hp.nBatched at a layers' segment, a.own.rows at an attention
segment, X.H.rows at the head's. NO NUMBER IS COMPUTED OFF A PLAN. STATEMENTS ALONE: two definitions
with code, this file's own, and six definitions of propositions. NOTHING IS PROVED IN THIS FILE, and
none is one of the library's goals: they are lemmas' statements.

WHAT IT IS NOT. Nothing on the public test `rowsFitB`: this is one of its parts. The full size
alone. UNDER THE HEAD, NOT IN SCOPE ALONE: it leans on the head's entry test that the planner's
first plan is the written one.

  `planRows X l`      THIS FILE's OWN: the three numbers above, by the segment's number
  `framesB`           THIS FILE's OWN: a test with code on the written sizes alone: 25 groups or
                      more; at each i below 25 the request has a link, with JUST TWO later moments
  `ChainSigmaBat`     GENERAL: a first chain's list whose first k records have a link, two later
                      moments and, as the last round of moment 2, "BAT-sigma" with r i rows: a list
                      W of length k with r i at i is a sublist of `sigmaBat` of the list's entries
  `FramesWritten`     `framesB` says yes
  `SigmaBatWritten`   `sigmaBat` of the written first plan's entries IS rowsAtLink 0, ...,
                      rowsAtLink 24
  `SigmaBatBites`     that sentence can fail: with the numbers of 0 and 2 changed over it is false
  `PlanRowsAtHead`    under `P5J.AtMg`, at every earlier hash: planRows Zp.p.X l = rowsAtLink l at
                      each l below 25
  `PlanRowsByPlan`    the same, plan by plan

MIND: "JUST TWO": were there a third later moment, the last round of moment 2 would not stand right
before the frame's "BAT".

NEAR. `full_rows` (Johnson/Desc/First/Batch/Law/Condition.lean): the fifth statement on the written
list's records and runs, by that file's own walk. `head_rows_in_scope`
(Johnson/P1K8R/HeadRowsInScope.lean): X.H.rows = 24653737 in scope alone, by another road: a
cross-check. `own_at_places` (Johnson/Desc/First/Att/Row/K5OwnAtPlaces.lean): every field of a.own
in scope but rows. `armsB_of_fields` (Johnson/AtFull/Rows/ArmsOfFields.lean) takes hp.nBatched and
a.own as premises. `Fo.planned_plan` (OnBytes/Tie/Pv/Lookup/Ends/FoPlannedCut.lean): the plan as a
list in letters, at the verifier's own planner; the description has a copy of its own.
`frames_written`, `frames_some` (Johnson/G/SwitchFramesAt.lean): the planner's records at the
written sizes, other fields of them; the first shares its name with a helper of the proofs' file
PlanRowsAtHead.lean, in another namespace.

Limits. Equations of numbers. Nothing on any property.
-/
import Johnson.P1K8R.SigmaBatStatement
import Johnson.P1K8R.RowsAtLink
import Johnson.P5J.NumbersAtHead
import Johnson.Desc.Ok.PlanWritten.MadeTest
import OnBytes.Tie.Pv.Lookup.Peel.FoPlanAtFrames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Params (RoundSpec Setting Scope ProofSized Subproofs batSigmaFrom)
open OnBytes.Plan (framesOf firstChainList)
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (proofSizedFull proofLit)

/-- **A plan's rows, by the segment's number.** This file's own. -/
def planRows (X : Verify.Public) (l : Nat) : Nat :=
  if l = 24 then X.H.rows
  else if l % 2 = 0 then ((X.G[l / 2]?).map (·.nBatched)).getD 0
  else ((X.A[l / 2]?).map (·.own.rows)).getD 0

/-- **The test on the written sizes.** This file's own. -/
def framesB : Bool :=
  decide (25 ≤ (reqGroups proofSizedFull.request).toList.length) &&
    (List.range 25).all fun i =>
      (proofSizedFull.request.link[i]?).isSome &&
        decide (TwLaw.laterOf (proofSizedFull.request.link[i]?) = 2)

/-- The general statement. Not proved here; a lemma's statement, none of the library's goals. -/
def ChainSigmaBat : Prop :=
  ∀ (z : ProofSized) (sub : Subproofs) (L : Nat → Nat → List RoundSpec) (after : List RoundSpec)
    (s : Setting) (c : Scope) (r : Nat → Nat) (k : Nat),
    (∀ i, i < k → ∃ n v, (framesOf z sub)[i]? = some n ∧ n.link = some v ∧ n.moments = 2 ∧
      n.l = i) →
    (∀ i, i < k → ∃ pre, L i 2 = pre ++ [batSigmaFrom s (r i) 0]) →
    ∃ W : List Nat, W.length = k ∧ (∀ i, i < k → W[i]? = some (r i)) ∧
      W.Sublist (sigmaBat ((firstChainList z sub L after).map fun y => (y.round s c).entry))

/-- The closed fact on the sizes. Not proved here; a lemma's statement, none of the library's goals.
-/
def FramesWritten : Prop := framesB = true

/-- The closed fact on the plan. Not proved here; a lemma's statement, none of the library's goals.
-/
def SigmaBatWritten : Prop :=
  sigmaBat (proofLit.plan.rounds.map (·.entry)) = (List.range 25).map rowsAtLink

/-- That it can fail. Not proved here; a lemma's statement, none of the library's goals. -/
def SigmaBatBites : Prop :=
  decide (sigmaBat (proofLit.plan.rounds.map (·.entry)) = (List.range 25).map fun l =>
    if l = 0 then 32005793 else if l = 2 then 32005923 else rowsAtLink l) = false

/-- The statement under the head. Not proved here; a lemma's statement, none of the library's goals.
-/
def PlanRowsAtHead : Prop :=
  ∀ (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
    P5J.AtMg o Z D r Zp Np cF → ∀ l, l < 25 → planRows Zp.p.X l = rowsAtLink l

/-- The same, plan by plan. Not proved here; a lemma's statement, none of the library's goals. -/
def PlanRowsByPlan : Prop :=
  ∀ (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
    P5J.AtMg o Z D r Zp Np cF →
    (∀ g, g < 12 → ∀ hp, Zp.p.X.G[g]? = some hp → hp.nBatched = rowsAtLink (2 * g)) ∧
      (∀ g, g < 12 → ∀ a, Zp.p.X.A[g]? = some a → a.own.rows = rowsAtLink (2 * g + 1)) ∧
      Zp.p.X.H.rows = rowsAtLink 24

end P1K8

#print axioms P1K8.planRows
#print axioms P1K8.framesB
#print axioms P1K8.ChainSigmaBat
#print axioms P1K8.FramesWritten
#print axioms P1K8.SigmaBatWritten
#print axioms P1K8.SigmaBatBites
#print axioms P1K8.PlanRowsAtHead
#print axioms P1K8.PlanRowsByPlan

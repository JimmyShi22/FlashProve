-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TestAtHead.lean: the proximity test on the request's group (the kind K12) at
its seat in the proof file's own first chain (member 354 of the flat list: the second place behind
the links): one step on the chain's shape, and WHAT A YES CARRIES. One law of the two: "carries"
alone. Under the head `P5J.AtMgA`; a joining of laws; nothing is evaluated.

Main names.
* `testGS p`: the step at the seat, a function of the chain's shape alone: no mark; no count of
  claims waits; the chain stands at its finish; then `testCore`
  (Johnson/Desc/K12/Honest/Shape/TestCore.lean) at the shape's core, at the group and the first
  fold's mask that the shape's component `fin` holds; the core that it returns is laid; every other
  component stands.
* `test_plan_at`: under the head the test's numbers `H2U.p12OfMade Zp.made` have the masks early and
  one answer to a sample: off the member's own test on the plan.
* `test_carries_at`: the member b at number 354 of cF.blocksInOrder is such that, where b says yes from s to
  t, `testGS (H2U.p12OfMade Zp.made)` returns at the shape of s, and returns the shape of t. From a
  yes alone.

How. `IM.back_of` and `IM.back_numbers` (Johnson/IMR/BackSeat.lean: which block stands there,
alone), `IM.yes_alone` (Johnson/IMR/SeatForm.lean), `K12.Seat.atFinish_ok`
(Johnson/Desc/K12/SeatLaws.lean), `k12_core_sh` (TestCore.lean), `plans_at`
(Johnson/AtFull/Shape/PlansAtHead.lean), `early_of_planOk` and `answers_of_planOk`
(Johnson/Desc/K12/Law/Top.lean).

Limits. NO "RETURNS": that the member says yes where `testGS` returns is not shown, here or in the
file that this one calls (TestReturnsFrame.lean has "returns" behind a guard of its own on the shape
and under a test on values: not from `testGS`'s return). testGS tells that the chain stands at its
finish by asking whether the finish's record is there (a.fin); it does not read the place's number
(a.here). At a state's shape the two agree; at an arbitrary shape they need not. Of the head the
proofs name scope, reads and laid.opened, and hand it whole to plans_at. No state is shown at which
`testGS` returns. That the head has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the format's second hash function. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.K12.Honest.Shape.TestCore
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.K12.Law.Top
import Johnson.AtFull.Shape.PlansAtHead
import Johnson.IMR.BackSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts atFinish T12)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest.Sh (testCore k12_core_sh)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **The step at the seat.** -/
def testGS (p : VerifiableInference.Desc.K12.P12) (a : ChainSh) : Option ChainSh :=
  if a.marked then none
  else if !(match a.rowsOwed with
      | none => true
      | some n => n == 0) then none
  else a.fin.bind fun f => (testCore p a.core f.fr.group f.mask).map a.setCore

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the masks come early and a sample has one answer. -/
theorem test_plan_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (H2U.p12OfMade Zp.made).early = true ∧ (H2U.p12OfMade Zp.made).answers = 1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ⟨b, b', eb, -, rfl, la⟩, -, -⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 1 b eb
  have h1 : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := plans_at h _ (List.mem_of_getElem? q)
  have h2 : b.planOk = true := (Bool.and_eq_true _ _ ▸ h1).1
  rw [IM.alone_planOk la] at h2
  have h3 : ((proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).planOk &&
      (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).claims.isEmpty &&
      (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).after.isEmpty) = true :=
    (IM.retype_planOk _ h2).1
  simp only [Bool.and_eq_true] at h3
  exact ⟨H2K.JointK.early_of_planOk _ h3.1.1, H2K.JointK.answers_of_planOk _ h3.1.1⟩

/-- **What a yes of the seated test carries.** -/
theorem test_carries_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[354]? = some b ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t →
        testGS (H2U.p12OfMade Zp.made) (chainSh s) = some (chainSh t) := by
  obtain ⟨he, ha⟩ := test_plan_at h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ⟨b, b', eb, -, rfl, la⟩, -, -⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 1 b eb
  have hy := IM.yes_alone la (by intro k; cases k)
  refine ⟨_, q, fun s rs gs t hd => ?_⟩
  have h1 : (atFinish (H2U.p12OfMade Zp.made)).decide s rs gs = .ok t := ((hy s t rs gs).1 hd).1
  obtain ⟨o, t', ho, hw, hf, hk, rfl⟩ :=
    VerifiableInference.Desc.K12.Seat.atFinish_ok _ s t rs gs h1
  have hc := k12_core_sh _ he ha ⟨s.st, s.book, s.roots, o.fr.group, .nothing, o.mask⟩ t' rs gs hk
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  simp only at ho hw hf hc
  subst ho
  have hm : (chainSh ⟨st, book, roots, rowsOwed, failed, check, out, .fin o, req⟩).marked =
      false := by
    show failed.isSome = false
    cases failed with
    | none => rfl
    | some e => cases hf
  have hr : (match (chainSh ⟨st, book, roots, rowsOwed, failed, check, out, .fin o, req⟩).rowsOwed
      with
      | none => true
      | some n => n == 0) = true := hw
  have hfin : (chainSh ⟨st, book, roots, rowsOwed, failed, check, out, .fin o, req⟩).fin =
      some (finSh o) := rfl
  have hcore : (chainSh ⟨st, book, roots, rowsOwed, failed, check, out, .fin o, req⟩).core =
      VerifiableInference.Desc.Ground.Sh.coreSh ⟨st, book, roots⟩ := rfl
  unfold testGS
  rw [hm, hr, hfin, hcore]
  show (testCore (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.Ground.Sh.coreSh
    ⟨st, book, roots⟩) o.fr.group o.mask).map _ = _
  rw [hc]
  rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.test_plan_at
#print axioms Johnson.AtFull.Shape.test_carries_at
#print axioms Johnson.AtFull.Shape.testGS

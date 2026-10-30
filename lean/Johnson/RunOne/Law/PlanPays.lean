-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/PlanPays.lean: WHAT THE TEST ON THE PLAN OF A SEATED PROXIMITY TEST PAYS OF THE PREMISES ON THE PLAN THAT THE KIND's LAWS TAKE. Statements with proofs; every proof is a line over the kind's files' theorems (Johnson/Desc/K12/Law/SpendMade.lean, DealMade.lean, TieOkMade.lean, EntriesMade.lean, Top.lean).
OBJECT. The tests on the plan of `proximityTestKind guardedProximityTestParts p` (Johnson/Desc/K12/JoinGuarded.lean) and of `rangesTest laid back N` (Johnson/Desc/Key/Ranges.lean).
USER. The first five fields of AtPlace (Johnson/Desc/K12/Coin/Sheet.lean) at the ranges' test's seat.
LETTERS. p, N, the state, the two halves and the type of claims are free. The one premise is the test's yes.
  asksPlan_iff: where the kind's block's own test on the plan says yes, what the ranges' seat asks besides on the plan (Key.asksOnPlan: four clauses) is just "the masks come early, and a sample has one answer": its clauses cutOk and spendOk are then theorems.
  kind_pays: the kind's block's own test on the plan gives cutOk, spendOk, dealOk, tieOk, ownTieOk, nzOk.
  rng_pays: the ranges' seat's test on the plan gives the first five fields of the plain law's premise on the place (Coin/Sheet.lean: AtPlace: early, answers, planOk, spend, deal), and tieOk, nzOk besides.
Limits. The other fields of that premise (the codes' facts; the written rounds' likeness; the trees; the errors) are not touched. That the test on the plan says yes at a real place is a run's word. Nothing on soundness.

-/
import Johnson.RunOne.Law.RngAnyCl
import Johnson.Desc.K12.Law.SpendMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.PlanPays
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key
open Johnson.RunOne.Law.RngAsked (planOk_ok)
open Johnson.RunOne.Law.RngAnyCl (plan_unit)

theorem kind_pays (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) :
    H2K.First.cutOk p = true ∧ H2K.Pub.spendOk p = true ∧ H2K.First.dealOk p = true ∧
      H2K.First.tieOk p = true ∧ H2K.First.ownTieOk p = true ∧ H2K.First.nzOk p = true :=
  ⟨H2K.JointK.cut_of_planOk p hp, H2K.Made.spendOk_of_planOk p hp, H2K.Made.dealOk_of_planOk guardedProximityTestParts p hp,
    H2K.Made.tieOk_of_planOk guardedProximityTestParts p hp, H2K.Made.ownTieOk_of_planOk guardedProximityTestParts p hp,
    H2K.Made.nzOk_of_planOk guardedProximityTestParts p hp⟩

theorem asksPlan_iff (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) :
    asksOnPlan p = (p.early && p.answers == 1) := by
  unfold asksOnPlan
  rw [(kind_pays p hp).1, (kind_pays p hp).2.1, Bool.and_true, Bool.and_true]

variable {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ} {N : H2U.PlaceNums}

theorem rng_pays (hp : (rangesTest laid back N : Block σ Cl).planOk = true) :
    (rangesParams N).early = true ∧ (rangesParams N).answers = 1 ∧
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).planOk = true ∧ H2K.Pub.spendOk (rangesParams N) = true ∧
      H2K.First.dealOk (rangesParams N) = true ∧ H2K.First.tieOk (rangesParams N) = true ∧ H2K.First.nzOk (rangesParams N) = true := by
  obtain ⟨hk, he, ha, _, _⟩ := planOk_ok (plan_unit hp)
  obtain ⟨_, h2, h3, h4, _, h6⟩ := kind_pays (rangesParams N) hk
  exact ⟨he, ha, hk, h2, h3, h4, h6⟩

end Johnson.RunOne.Law.PlanPays

#print axioms Johnson.RunOne.Law.PlanPays.kind_pays
#print axioms Johnson.RunOne.Law.PlanPays.asksPlan_iff
#print axioms Johnson.RunOne.Law.PlanPays.rng_pays
#print axioms H2K.Made.spendOk_of_planOk

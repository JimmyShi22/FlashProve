-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofFirstWritten.lean: THE PROOF FILE's FIRST PLAN RETURNS, AS A VALUE. Where
`shapesWith` (OnBytes/Model/VerifySubproofs.lean) returns x at public data X whose 26 links' arms
are the written ones (`armsB`, Johnson/LPFE1R/RowsAtArms.lean), the planner's routine for the proof
file's first chain, at the written sizes, returns the first written priced plan. It
pays the premise e₁ of `configure_of_parts` (Johnson/AtFull/Made/Ledger.lean) at z.proof =
proofSizedFull. A law file; no running text imports it.

How. `firstPlan` reads of x.sub four fields, and the routine among them at the links' numbers alone
(FirstReads.lean); under `armsB` these are those of the closed value `subW` (ArmList.lean). By the
law `Plan.runs_firstRounds` the routine that `firstPlan` finishes adds, where it ends well, the
rounds of a plain list and leaves nothing open. That it ends well is shown piece by piece
(ProofFirstGoes.lean); that the list's rounds are the written plan's is one closed fact
(ProofFirstListed.lean); that the written plan passes the planner's verdict lies in `proofAll_full`
(Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean). `finishHeld_of_runs` (OfRuns.lean) joins the
three.

Statements.
  `proof_first_holds`: proofThree.A.plan.holds = true.
  `proof_first_at_written`: firstPlan proofSizedFull subW = .ok proofThree.A.plan: a closed
    equation.
  `proof_first_written`: the statement above.

Limits. `armsB X` AND THE RETURN OF `shapesWith` ARE PREMISES: shown at no public files here. That
they can be met together is EVALUATED, NOT PROVED: at the stored full-size example's public files
a sheet for Lean's evaluator, which is not in this repository, finds a yes of `armsB`, a return of
`shapesOf` (OnBytes/Model/VerifyChains.lean, which calls `shapesWith`: between the two lies the
premise c₁ of the ledger), the written sizes, and the written plan. That the planner's sizes are
`proofSizedFull` at any public files is not said here. The written arms, sizes and plan stand on
prints of the library's own planner. Nothing says that an error bounds a count. Nothing on
soundness.
-/
import Johnson.AtFull.Made.OfRuns
import Johnson.AtFull.Made.ProofFirstGoes
import Johnson.AtFull.Made.ProofFirstListed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params OnBytes.Model.Verify
open VerifiableInference
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree proofAll_full)
open VerifiableInference.Desc.LinkJoin (armsB)

/-- The first written plan passes the planner's verdict. -/
theorem proof_first_holds : proofThree.A.plan.holds = true := by
  have h := proofAll_full.1
  unfold Desc.chainAll Desc.chainOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1

/-- **At the written sizes and arms the routine returns the first written plan.** -/
theorem proof_first_at_written : firstPlan proofSizedFull subW = .ok proofThree.A.plan := by
  have e := finishHeld_of_runs (runs_bodyOf (subRuns_subW proofSizedFull.set))
    proof_first_returns (by
      show proofFirstListed.holds = true
      rw [proof_first_listed]
      exact proof_first_holds)
  rw [firstPlan_body, e]
  show Except.ok proofFirstListed = _
  rw [proof_first_listed]

theorem links_le : proofSizedFull.request.link.length ≤ 26 := by
  rw [links_25]
  omega

/-- **The proof file's first plan returns, as a value.** -/
theorem proof_first_written {X : Public} {links : List ReqLink} {layout : ReqLayout}
    {identifiers : List Nat} {x : Shapes} (hx : shapesWith X links layout identifiers = .ok x)
    (ha : armsB X = true) : firstPlan proofSizedFull x.sub = .ok proofThree.A.plan :=
  (firstPlan_at_arms links_le hx ha).trans proof_first_at_written

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.links_le
#print axioms Johnson.AtFull.Made.proof_first_holds
#print axioms Johnson.AtFull.Made.proof_first_at_written
#print axioms Johnson.AtFull.Made.proof_first_written

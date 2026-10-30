-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/KeyInScope.lean: in the public part that the proof file's description computes
(`pureRoad.pub`, Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean), at all public files in the goals' scope, the
key of the strict scan of the parameter file (`keyOfScan`, Johnson/Desc/Ok/PlanWritten/Test.lean:
the number of layers, the width, the size of the vocabulary) is the full size's (`fullKey`). For
every function in the second hash function's place.

What it is for. The tests that hold what the planner made against written values (`seatPinnedProof`,
Test.lean; `sizedPinnedAt`, `firstPinnedAt`, Johnson/Desc/Ok/PlanWritten/SizedTest.lean) ask
something at the full size's key alone, and say yes at every other key. This law closes that arm in
scope.

How. The public record in that public part is what `publicOfO o` returns (`pub_public`,
Johnson/Desc/ProofFile/Law/MakerPublic.lean), so the steps of that text hold of it (`PublicSteps`,
Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean): its scan is the strict scan of the parameter file.
In scope that file is the stored one with some values of the eight free numbers (`inScope_policy`),
and its scan has L = 48, d = 5120, V = 202048 (`scan_sizes`; both in
Johnson/Goal/PlanValues/ScopeAtPlan.lean).

Statements and proofs.
  `key_of_steps`: where the steps hold of X at the parameter file with free numbers v and any scale
    file, the key of X's scan is `fullKey`.
  `key_at_policy_pure`: so at `VerifierAndGoals.policyFile v`, any layout file, any scale file, any o.
  `key_in_scope_pure`: at all public files in the goals' scope.
  `sized_in_scope`, `first_in_scope`: so in scope a yes of `sizedPinnedAt` at that public part's
    scan and planner's record gives that the planner's sizes of a proof file are `proofSizedFull`; a
    yes of `firstPinnedAt` at the first chain's parameters as read back gives the five equations.
No evaluation is made here.

What of OnBytes/Model/ is used: `Verify.Public`, `Verify.polLayout`, and what ScopeAtPlan.lean uses.

Limits. One way: from a public part that is computed; that it is computed at any files is not said.
That a verifier asks the two tests is not said. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Goal.PlanValues.ScopeAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Model OnBytes.Model.Verify Lk6.AtPlan

/-- At the parameter file with free numbers v the key of the scan is the full size's. -/
theorem key_of_steps {v : VerifierAndGoals.FreeLines} {KL : ByteArray} {X : Public}
    (C : PublicSteps (VerifierAndGoals.policyFile v) KL X) : keyOfScan X.P = fullKey := by
  obtain ⟨_, b1, b2, _, _, _, _, _, _, b9, _⟩ := scan_sizes (polLayout_scan C.layout)
  unfold keyOfScan fullKey
  rw [b1, b2, b9]

theorem key_at_policy_pure {o : ProofFile.SecondHashFunctionArgument} {v : VerifierAndGoals.FreeLines} {lay KL : ByteArray}
    {Z : ProofFile.Pub} (h : ProofFile.pureRoad.pub o (VerifierAndGoals.policyFile v) lay KL = .ok Z) :
    keyOfScan Z.p.X.P = fullKey :=
  key_of_steps (publicSteps_of_O (ProofFile.Law.pub_public h))

/-- **In the goals' scope the key is the full size's.** -/
theorem key_in_scope_pure {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z) :
    keyOfScan Z.p.X.P = fullKey := by
  obtain ⟨v, hv⟩ := inScope_policy hW
  rw [hv] at h
  exact key_at_policy_pure h

/-- **In scope a yes of the test on the sizes gives the written sizes.** -/
theorem sized_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : sizedPinnedAt Z.p.X.P Z.p.chains.made = true) :
    Z.p.chains.made.sized.proof = proofSizedFull :=
  sized_of_pinnedAt hy (key_in_scope_pure hW h)

/-- **The like for the first chain's parameters as read back.** -/
theorem first_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : firstPinnedAt Z.p.X.P Z.first = true) :
    Z.first.codes = proofSizedFull.codes ∧ Z.first.lin = proofSizedFull.batch.shape ∧
      Z.first.shape = proofSizedFull.request ∧ Z.first.pendingRows = 13 ∧
      Z.first.binding = ⟨6, 40⟩ :=
  first_of_pinnedAt hy (key_in_scope_pure hW h)

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.key_of_steps
#print axioms VerifiableInference.PlanWritten.key_at_policy_pure
#print axioms VerifiableInference.PlanWritten.key_in_scope_pure
#print axioms VerifiableInference.PlanWritten.sized_in_scope
#print axioms VerifiableInference.PlanWritten.first_in_scope

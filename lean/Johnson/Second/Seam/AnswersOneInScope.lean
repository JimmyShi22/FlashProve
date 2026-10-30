-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/AnswersOneInScope.lean: IN THE GOALS' SCOPE TWO ORACLE MESSAGES' SHAPES, AS THE
PLANNER SIZED THEM, HAVE ONE ANSWER TO THE OUT-OF-DOMAIN (OOD) SAMPLE EACH: the shape of the first
message that is sent at the very start (request.atStart's head; vAt takes it as its
field indexShape) and the shape w of the batch's shape, which is (ProofFile.pAt Z).S.w by the make of pAt.
Statements and proofs: one tie, from the verifier's test madePinnedAt, and closed facts by Lean's
kernel (decide +kernel).
  sized_proof_in_scope  InScope W · ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z · madePinnedAt
                          Z.p.X.P Z.p.chains.made Z.first Z.made = true ⊢
                          Z.p.chains.made.sized.proof = proofSizedFull. By key_in_scope_pure
                          (Johnson/Goal/Numbers/KeyInScope.lean) and made_of_pinned.
  start_there · answers_index · answers_w   at proofSizedFull: the list atStart has a first member;
                          its shape has one answer; batch.shape.w has one answer.
  answers_not_two         negative tests: neither count is 2 (so the two facts are no accident of a
                          test that says yes to all).
  answers_one_in_scope  the same three premises ⊢
                          ((Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD
                          default).answers = 1 ∧ (ProofFile.pAt Z).S.w.answers = 1.
  start_there_in_scope  the same three ⊢ the list atStart has a first member: so the getD above
                          never meets its default.
Limits. The three premises stay premises; they are met at VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap by an
evaluation. That a verifier's state has messages of these shapes is not said here. No soundness is
claimed.

-/
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.Plain.StartThreeAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes
open VerifiableInference.PlanWritten (madePinnedAt made_of_pinned proofSizedFull key_in_scope_pure)

theorem start_there : proofSizedFull.request.atStart.head?.isSome = true := by decide +kernel

theorem answers_index :
    ((proofSizedFull.request.atStart.head?.map fun n : OracleNotice => n.shape).getD
      default).answers = 1 := by
  decide +kernel

theorem answers_w : proofSizedFull.batch.shape.w.answers = 1 := by decide +kernel

theorem answers_not_two :
    ((proofSizedFull.request.atStart.head?.map fun n : OracleNotice => n.shape).getD
      default).answers ≠ 2 ∧
      proofSizedFull.batch.shape.w.answers ≠ 2 := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}


theorem sized_proof_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.p.chains.made.sized.proof = proofSizedFull := by
  unfold madePinnedAt at hy
  rw [key_in_scope_pure hW h] at hy
  exact (made_of_pinned hy).1.1


theorem answers_one_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    ((Z.p.chains.made.sized.proof.request.atStart.head?.map fun n : OracleNotice => n.shape).getD
      default).answers = 1 ∧
      (ProofFile.pAt Z).S.w.answers = 1 := by
  have e := sized_proof_in_scope hW h hy
  refine ⟨?_, ?_⟩
  · rw [e]
    exact answers_index
  · show Z.p.chains.made.sized.proof.batch.shape.w.answers = 1
    rw [e]
    exact answers_w


theorem start_there_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.p.chains.made.sized.proof.request.atStart.head?.isSome = true := by
  rw [sized_proof_in_scope hW h hy]
  exact start_there

end Second.Seam

#print axioms Second.Seam.answers_not_two
#print axioms Second.Seam.sized_proof_in_scope
#print axioms Second.Seam.answers_one_in_scope
#print axioms Second.Seam.start_there_in_scope

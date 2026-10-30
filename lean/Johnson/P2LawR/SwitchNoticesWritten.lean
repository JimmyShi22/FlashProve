-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SwitchNoticesWritten.lean: A CLOSED FACT AT THE WRITTEN CODES AND SHAPE OF THE FULL
SIZE, BY LEAN's KERNEL: the test noticesOkB (Johnson/P2LawR/SwitchNotices.lean) says true there: at
what each later link's switch and the finish's switch announce the sent shapes fit the codes and the
trees can be laid. And so at the public part's own codes and shape, in the goals' scope.

  notices_written    noticesOkB csW shW = true: by decide +kernel (csW, shW: the written
  values of Johnson/Top/H0/K2Hands/FrontsFull.lean)
  notices_in_scope   in scope, where the public part is made and the named test madePinnedAt
  accepts: noticesOkB Z.first.codes Z.first.shape
                   = true: by written_in_scope
                   (Johnson/Top/H0/K2Hands/WrittenInScope.lean)
Limits. The full size alone. THAT THE TEST CAN SAY FALSE IS SHOWN BY NO LINE HERE: negative lines
are left to other files. Nothing on soundness.
-/
import Johnson.P2LawR.SwitchNotices
import Johnson.Top.H0.K2Hands.WrittenInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.P2Notices
open VerifiableInference.Desc.First.K2Hands (csW shW written_in_scope)
open VerifiableInference.PlanWritten (madePinnedAt)

/-- **The test says true at the written codes and shape**: by Lean's kernel. -/
theorem notices_written : noticesOkB csW shW = true := by decide +kernel

/-- **So at the public part's own, in the goals' scope.** -/
theorem notices_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    noticesOkB Z.first.codes Z.first.shape = true := by
  obtain ⟨e1, e2, -⟩ := written_in_scope hW h hy
  rw [e1, e2]
  exact notices_written

end VerifiableInference.Desc.P2Notices

#print axioms VerifiableInference.Desc.P2Notices.notices_written
#print axioms VerifiableInference.Desc.P2Notices.notices_in_scope

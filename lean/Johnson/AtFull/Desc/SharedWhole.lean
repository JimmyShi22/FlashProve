-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Desc/SharedWhole.lean: THE SHARED CHAIN's SHARE OF THE MASTER LEDGER, WHOLE: of
A := what onlineSharedChain Z returns: DescOwed.r₆ · the first conjunct of PlanWordOwed.hF ·
PlanWordOwed.b₂ · the shared chain's part of PlanWordOwed.hC, AT ONE A, FROM HYPOTHESES BY FIELD
ALONE. A joining of Johnson/AtFull/Desc/SharedShare.lean (shared_share) and FileShare.lean
(file_share): one statement with its proof.

The hypotheses, fourteen: at c := Z.p.chains and X := Z.p.X the eleven of file_share (the sizes; the
three made plans; the first chain's planner's return; seven fields of what is read back; the
setting), of which the first gives shared_share's three fields; and the three members of
later_of_members (Johnson/AtFull/Desc/LaterSeats.lean). NONE IS PAID HERE.
Limits. No soundness is claimed. No example of the head is shown in this file; two, at storedPublicFiles and at
zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they
are worth.

-/
import Johnson.AtFull.Desc.SharedShare
import Johnson.AtFull.Desc.FileShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc VerifiableInference.PlanWritten
open VerifiableInference.Number.ByRuns

/-- **The shared chain's share, whole.** -/
theorem shared_whole (Z : ProofFile.Pub) {first : Planned}
    (hz : Z.p.chains.made.sized.proof = proofSizedFull)
    (hm : Z.p.chains.made.proof = [first, proofThree.B.plan, proofThree.C.plan])
    (e₁ : firstPlan proofSizedFull (Verify.subproofsWith Z.p.X proofSizedFull.request.link) =
      .ok first)
    (r₁ : Z.p.chains.proof.first.given.plan.entries = first.plan.entries)
    (r₂ : Z.p.chains.proof.shared.given.plan = proofThree.B.plan.plan)
    (r₃ : Z.p.chains.proof.second.given.plan = proofThree.C.plan.plan)
    (r₄ : Z.p.chains.proof.shared.lin = proofSizedFull.batch.shape)
    (r₅ : Z.p.chains.proof.shared.codes = proofSizedFull.codes)
    (r₆ : Z.p.chains.proof.first.given.plan.samples = first.plan.samples)
    (r₇ : Z.p.chains.proof.first.shape = proofSizedFull.request)
    (hs : proofSizedFull.set = settingOf Z.p.X.P.frame)
    (m₁ : H2U.p12FoldedOfMade Z.made 9 = piU) (m₂ : H2U.p12OmegaOfMade Z.made 10 = piO)
    (m₃ : H2U.p12OwnOfMade Z.made 2 = piW) :
    ∃ A : ProofFile.SharedSeat, ProofFile.onlineSharedChain Z = some A ∧ A.fileOk = true ∧
      (∀ b ∈ (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder, b.planOk = true) ∧
      cutOf (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSharedFull := by
  obtain ⟨hF, hB⟩ := file_share hz hm e₁ r₁ r₂ r₃ r₄ r₅ r₆ r₇ hs
  exact shared_share Z (congrArg (·.set) hz) (congrArg (·.codes) hz) (congrArg (·.batch) hz) m₁ m₂
    m₃ hF hB

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.shared_whole

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/CodesOneInScope.lean: IN THE GOALS' SCOPE THE FIRST CHAIN's CODES AS THE READER
MADE THEM (Z.first.codes) ARE THE CODES THAT THE LIST OF THE FIRST CHAIN's SENDINGS BEARS
(Z.made.proof.1.codes); so the two ways of laying the first chain's sendings (laidAtCodes at
Z.first.codes; laidOfChain, which reads the list's own codes) give ONE value there, the written
LFull. Statements and proofs: calls, and two closed facts by Lean's kernel (decide +kernel).
  codes_written            proofSizedFull.codes = proofSendsFull.1.codes: a closed fact.
  codes_full2              proofSendsFull.1.codes = codesFull2: a closed fact (written_codes of
                           Johnson/Desc/Ok/PlanWritten/SendsTestLaws.lean says it of all six lists
                           at once; asked here at the one list, so that this file needs none
                           of that file's cone beyond what WrittenAtScope.lean brings).
  codes_one_in_scope     InScope W · ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z · madePinnedAt
                           Z.p.X.P Z.p.chains.made Z.first Z.made = true · LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol
                           W.lay W.KL = .ok (D, r) ⊢ Z.first.codes = Z.made.proof.1.codes.
  laidOfChain_in_scope   the same four ⊢ laidOfChain Z.made.proof.1 = some LFull.
  laidAtCodes_in_scope   the same four ⊢ laidAtCodes Z.first.codes Z.made.proof.1 = some LFull.
Limits. At a free value of the planner's type nothing ties the two codes: the tie is the verifier's
test madePinnedAt's. The four premises stay premises; they are met at VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap
by an evaluation (ScopeMembers2.lean, not in this library). Another file has a laid_in_scope of
its own (Johnson/HB/LLHARD/PlanInScope.lean), from three of the four premises:
laidAtCodes_in_scope is its weaker twin. No soundness is claimed.

-/
import Johnson.P5T.WrittenAtScope
import Johnson.HB.LLHARD.LaidWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes Johnson.G P5T
open VerifiableInference.Desc.K13.Law (LFull laid_written)
open VerifiableInference.Desc.K12.Door (laidAtCodes laidOfChain laidOfChain_is)
open VerifiableInference.PlanWritten (madePinnedAt proofSizedFull)

theorem codes_written : proofSizedFull.codes = proofSendsFull.1.codes := by decide +kernel

theorem codes_full2 : proofSendsFull.1.codes = codesFull2 := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}


theorem codes_one_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    Z.first.codes = Z.made.proof.1.codes := by
  obtain ⟨a, _, c, _, _⟩ := written_at_in_scope hW h hy hl
  rw [c, a]
  exact codes_written


theorem laidOfChain_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    laidOfChain Z.made.proof.1 = some LFull := by
  obtain ⟨a, _, _, _, _⟩ := written_at_in_scope hW h hy hl
  rw [a, laidOfChain_is, codes_full2]
  exact laid_written


theorem laidAtCodes_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    laidAtCodes Z.first.codes Z.made.proof.1 = some LFull := by
  rw [codes_one_in_scope hW h hy hl, ← laidOfChain_is]
  exact laidOfChain_in_scope hW h hy hl

end Second.Seam

#print axioms Second.Seam.codes_written
#print axioms Second.Seam.codes_full2
#print axioms Second.Seam.codes_one_in_scope
#print axioms Second.Seam.laidOfChain_in_scope
#print axioms Second.Seam.laidAtCodes_in_scope

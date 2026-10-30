-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/PlanSitsInScope.lean: IN THE GOALS' SCOPE THE HANDED OWN GROUP's TWO MEMBERS SIT
WHERE THE PLAN SAYS: ToldDesc.PlanSits (Johnson/ToldDescR/OwnSitsBools.lean) AT L := the written
laid value LFull, M := msgsOfChain Z.made.proof.1 (the shapes that the first chain's own list of
sendings announces), V := LLT25.vAt Z N₁ (Johnson/LLT25R/LastAt.lean), idx := 4, nW := 197.
Statements and
proofs: ties under the verifier's test madePinnedAt, and closed facts by Lean's kernel
(decide +kernel).
  VFull                   the written value of vAt: the seats (1, 0) and (82, 0); the shape of the
                          first notice of proofSizedFull.request.atStart;
                          proofSizedFull.batch.shape.w.
  sits_written            planSitsB LFull MFull VFull 4 197 = true: a closed fact.
  sits_rejects            negative tests, closed: the two seats exchanged · the two shapes exchanged
                          · nW + 1 · idx + 1: each false.
  seats_two_in_scope      the four premises ⊢ at numbersOf (planSeats Z Z.D.1): index = (1, 0) ∧
                          w = (82, 0). By seats_first_in_scope and N0Full_seats.
  vAt_in_scope            three premises · N₁.index = (1, 0) · N₁.w = (82, 0) ⊢ vAt Z N₁ = VFull.
  planSits_in_scope     InScope W · ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z · madePinnedAt
                          Z.p.X.P Z.p.chains.made Z.first Z.made = true · LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol
                          W.lay W.KL = .ok (D, r) · N₁.index = (1, 0) · N₁.w = (82, 0) ⊢
                          PlanSits LFull (msgsOfChain Z.made.proof.1) (vAt Z N₁) 4 197.
  planSits_at_plan      the four alone ⊢ the same at N₁ := numbersOf (planSeats Z Z.D.1).
  planSits_at_N         the four alone ⊢ the same at N₁ := P5J.At.N Z cF, at every cF (that
                          value's fields index and w are numbersOf's: by rfl).
That LFull is the value of laidAtCodes Z.first.codes Z.made.proof.1 and of laidOfChain
Z.made.proof.1 there: CodesOneInScope.lean.
Limits. The four premises stay premises; they are met at VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap by an
evaluation (ScopeMembers2.lean, not in this library). The full size alone. Nothing on a reached
state: that a state's book and statement carry L and M is another's. No soundness is claimed.

-/
import Johnson.Second.Seam.SeatsPlacesInScope
import Johnson.Second.Seam.CodesOneInScope
import Johnson.Second.Seam.AnswersOneInScope
import Johnson.ToldDescR.OwnSitsBools
import Johnson.LLT25R.LastAt
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes Johnson.G P5T
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Last (OwnSeats)
open VerifiableInference.Desc.K13.Law (LFull MFull msgs_written)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.PlanWritten (madePinnedAt proofSizedFull)
open ToldDesc (PlanSits planSitsB planSits_iff)

/-- The written value of vAt. -/
def VFull : OwnSeats :=
  ⟨(1, 0), (82, 0),
    (proofSizedFull.request.atStart.head?.map fun n : OracleNotice => n.shape).getD default,
    proofSizedFull.batch.shape.w⟩

theorem sits_written : planSitsB LFull MFull VFull 4 197 = true := by decide +kernel

theorem sits_rejects :
    planSitsB LFull MFull ⟨VFull.w, VFull.index, VFull.indexShape, VFull.wShape⟩ 4 197 = false ∧
      planSitsB LFull MFull ⟨VFull.index, VFull.w, VFull.wShape, VFull.indexShape⟩ 4 197 = false ∧
      planSitsB LFull MFull VFull 4 198 = false ∧ planSitsB LFull MFull VFull 5 197 = false := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}

theorem seats_two_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    (numbersOf (planSeats Z Z.D.1)).index = (1, 0) ∧
      (numbersOf (planSeats Z Z.D.1)).w = (82, 0) := by
  rw [seats_first_in_scope hW h hy hl]
  exact ⟨congrArg Prod.fst N0Full_seats, congrArg Prod.snd N0Full_seats⟩

theorem vAt_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {N₁ : Numbers}
    (hI : N₁.index = (1, 0)) (hw : N₁.w = (82, 0)) : LLT25.vAt Z N₁ = VFull := by
  have e := sized_proof_in_scope hW h hy
  show (⟨N₁.index, N₁.w,
    (Z.p.chains.made.sized.proof.request.atStart.head?.map fun n : OracleNotice => n.shape).getD
      default, Z.p.chains.made.sized.proof.batch.shape.w⟩ : OwnSeats) = VFull
  rw [hI, hw, e]
  rfl


theorem planSits_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) {N₁ : Numbers}
    (hI : N₁.index = (1, 0)) (hw : N₁.w = (82, 0)) :
    PlanSits LFull (msgsOfChain Z.made.proof.1) (LLT25.vAt Z N₁) 4 197 := by
  obtain ⟨a, _, _, _, _⟩ := written_at_in_scope hW h hy hl
  rw [a, msgs_written, vAt_in_scope hW h hy hI hw]
  exact (planSits_iff _ _ _ _ _).1 sits_written


theorem planSits_at_plan (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    PlanSits LFull (msgsOfChain Z.made.proof.1)
      (LLT25.vAt Z (numbersOf (planSeats Z Z.D.1))) 4 197 :=
  planSits_in_scope hW h hy hl (seats_two_in_scope hW h hy hl).1 (seats_two_in_scope hW h hy hl).2


theorem planSits_at_N (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (cF : _) :
    PlanSits LFull (msgsOfChain Z.made.proof.1) (LLT25.vAt Z (P5J.At.N Z cF)) 4 197 :=
  planSits_in_scope hW h hy hl (seats_two_in_scope hW h hy hl).1 (seats_two_in_scope hW h hy hl).2

end Second.Seam

#print axioms Second.Seam.sits_written
#print axioms Second.Seam.sits_rejects
#print axioms Second.Seam.planSits_in_scope
#print axioms Second.Seam.planSits_at_plan
#print axioms Second.Seam.planSits_at_N

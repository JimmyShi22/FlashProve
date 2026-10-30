-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/SeatsPlacesInScope.lean: IN THE GOALS' SCOPE THE FIRST CHAIN's SEATS OFF THE PLAN ARE THE WRITTEN ONES, AND THEIR (tree, tenant) PAIRS ARE THE WRITTEN LAID VALUE's PLACES. Two statements with their proofs: calls alone: seats_first and the closed fact seats_are_places (FarWritten.lean: by Lean's kernel) at far_ties_in_scope (Johnson/P5T/WrittenAtScope.lean).
  seats_first_in_scope   InScope W · ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z · madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true · LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r) ⊢ planSeats Z Z.D.1 = psFull.
  seats_places_in_scope  the same four ⊢ (planSeats Z Z.D.1).map (fun p => (p.j, p.t)) = LFull.places.
Limits. The four premises stay premises; they are met at VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap by an evaluation (ScopeMembers.lean, not in this library). Another file has a statement of the first kind of its own (seats_in_scope, Johnson/P5T/PlanSeatsTie.lean): the two are not compared here. That laidAtCodes returns LFull in scope is laid_in_scope (Johnson/HB/LLHARD/PlanInScope.lean). No soundness is claimed.

-/
import Johnson.Second.Seam.FarWritten
import Johnson.P5T.WrittenAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes Johnson.G P5T
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.PlanWritten (madePinnedAt)

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}


theorem seats_first_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) : planSeats Z Z.D.1 = psFull := by
  obtain ⟨h1, _, hS, hD1, _⟩ := far_ties_in_scope hW h hy hl
  exact seats_first Z Z.D h1 hS hD1


theorem seats_places_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    (planSeats Z Z.D.1).map (fun p => (p.j, p.t)) = LFull.places := by
  rw [seats_first_in_scope hW h hy hl]
  exact seats_are_places

end Second.Seam

#print axioms Second.Seam.seats_first_in_scope
#print axioms Second.Seam.seats_places_in_scope

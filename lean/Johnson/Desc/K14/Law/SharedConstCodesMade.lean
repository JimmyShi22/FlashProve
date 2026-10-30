-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstCodesMade.lean: "THE TWO TABLES READ ONE LIST OF CODES"
(Sh.hcs_in_scope, Johnson/Desc/K14/Law/SharedConstCodesAt.lean) UNDER ONE PIN OF THE DOOR AND NO
LETTER MORE: the door's test on all that the planner has made (madePinnedAt) gives the two narrower
pins, and the typed shape has a witness. So the equation can stand as a term inside a letter.

  Sh.hcs_of_made       InScope · what the road and "the written data are laid" return · madePinnedAt
                       → Z.made.p.chains.proof.first.codes = (planAt Z N G).Q.codes
  Sh.written_of_made   likewise the equations on the public value: ∃ x, realSized = some (x, …) ∧
                       Written Z x
HOW. Calls: sized_of_made | first_of_made
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) · full_real (SharedConstFull.lean) ·
written_in_scope.
What is not claimed. That the pin accepts. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstCodesAt
import Johnson.Desc.K14.Law.SharedConstFull
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.PlanWritten (madePinnedAt sized_of_made first_of_made)

namespace Sh

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}

/-- **One list of codes, under one pin.** -/
theorem hcs_of_made {Xi : Type} (hW : VerifierAndGoals.InScope W = true)
    (pub : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (N : H2U.Places4) (G : FileDescription Xi) :
    Z.made.p.chains.proof.first.codes = (planAt Z N G).Q.codes := by
  obtain ⟨x, hx, _⟩ := full_real
  exact hcs_in_scope hW pub (sized_of_made hy) (first_of_made hy) hl hx N G

/-- **The equations on the public value, under one pin.** -/
theorem written_of_made (hW : VerifierAndGoals.InScope W = true)
    (pub : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    ∃ x, realSized = some (x, codesFull2) ∧ Written Z x := by
  obtain ⟨x, hx, _⟩ := full_real
  exact ⟨x, hx, written_in_scope hW pub (sized_of_made hy) (first_of_made hy) hl hx⟩

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.hcs_of_made
#print axioms Desc.K14.Law.Sh.written_of_made

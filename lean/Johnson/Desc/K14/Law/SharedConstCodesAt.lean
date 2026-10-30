-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstCodesAt.lean: THE FIRST CHAIN's CODES, AS THE LIBRARY's COMPOSED
MEANING's CONSTANT READS THEM OFF THE PUBLIC VALUE (its letter cs:
    Z.made.p.chains.proof.first.codes,
Johnson/P5J/LettersAt.lean), ARE IN THE GOALS' SCOPE THE SHARED CHAIN's PARAMETERS' CODES AT THE
    SEAT.

  Sh.cs_is             that term is Z.first.codes: by unfolding
  Sh.hcs_in_scope      in scope it is (planAt Z N G).Q.codes (Sh.codes_first_in_scope,
                       Johnson/Desc/K14/Law/SharedConstLaid.lean, called)
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstLaid

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

namespace Sh

/-- The composed meaning's term for the first chain's codes. -/
theorem cs_is (Z : ProofFile.Pub) : Z.made.p.chains.proof.first.codes = Z.first.codes := rfl

/-- **In scope the two tables read one list of codes.** -/
theorem hcs_in_scope {Xi : Type} {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {x : LinSized}
    (hW : VerifierAndGoals.InScope W = true) (pub : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hx : realSized = some (x, codesFull2)) (N : H2U.Places4) (G : FileDescription Xi) :
    Z.made.p.chains.proof.first.codes = (planAt Z N G).Q.codes :=
  (codes_first_in_scope hW pub hs hf hl hx N G).symm

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.cs_is
#print axioms Desc.K14.Law.Sh.hcs_in_scope

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstLastAt.lean: FOR THE LAST TABLE's LAW (Johnson/LLT25R/): AT A PROOF
    FILE's SEAT THE
SHARED CHAIN's PARAMETERS' CODES AND SHAPE ARE THE LAST CHAIN's OWN (ToldDesc.p14At Z), AND WHAT THE
TESTS IN THE PROMISE's SLOT SAY OF THE OOD sample AT OMEGA AT THE SHARED CHAIN's LAST BORDER
(Sh.omega_sampled, Johnson/Desc/K14/Law/SharedConstLast.lean) IN THOSE LETTERS.

  Sh.p_at              the constant's parameters for the last chain's door at the seat ARE p14At Z
  Sh.q_at              the two equations: by unfolding
  Sh.omega_sampled_at  Sh.omega_sampled at planAt Z N G, its one premise from the named tests, at
                       (p14At Z).codes and (p14At Z).S
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstLast
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.ToldDescR.LastBlocks

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


namespace Sh

variable {Xi : Type} (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi)

/-- The constant's parameters for the last chain's door, at the seat. -/
theorem p_at : (planAt Z N G).p = ToldDesc.p14At Z := rfl

/-- **The two pairs are one.** -/
theorem q_at : (planAt Z N G).Q.codes = (ToldDesc.p14At Z).codes ∧
    (planAt Z N G).Q.S = (ToldDesc.p14At Z).S := ⟨rfl, rfl⟩

/-- **What the tests in the slot say of the OOD sample at Omega, at the last chain's letters.** -/
theorem omega_sampled_at (hT : Tests (planAt Z N G)) (d : St) (h : X (planAt Z N G) 12 d = true) :
    ∃ x, d.st.oracles[d.loc.oOmega]? = some x ∧ x.shape = (ToldDesc.p14At Z).S.omega ∧
      H2K.Pin.ok (H2K.Pin.sampleL (ToldDesc.p14At Z).codes
        (seatY (ToldDesc.p14At Z).S.omega d.loc.oOmega) x) = true :=
  omega_sampled (planAt Z N G) (by rw [tests_hsO _ hT]; decide) d h

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.q_at
#print axioms Desc.K14.Law.Sh.omega_sampled_at

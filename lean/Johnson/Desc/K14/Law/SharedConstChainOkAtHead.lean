-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/Desc/K14/Law/SharedConstChainOkAtHead.lean: UNDER THE HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean) EVERY SUB-PROTOCOL OF THE SEATED SHARED CHAIN PASSES ITS OWN TEST ON ITS
PARAMETERS; AND, UNDER ONE PIN OF THE DOOR BESIDE IT, THE SHARED TABLE's CONSTANT's NAMED TESTS
    ACCEPT.
Two corollaries: no proof of their own.

  Sh.chainOk_at_head   Sh.chainOkAt Zp Np = true: from the head alone
  Sh.laidPOf_at_head   "the written data are laid", back from the head's fields
  Sh.tests_at_head     Sh.Tests (planAt Zp Np G), under madePinnedAt
HOW. Sh.chainOk_descPure (Johnson/Desc/K14/Law/SharedConstDoor.lean) at the head's value and its
    test's
accept; its Z and N are the head's by what the road and the places return · Sh.written_of_made
(SharedConstCodesMade.lean) · Sh.tests_at (SharedConstAt.lean).
What is not claimed. That the pin accepts. No example of the head in Lean at other files than storedPublicFiles
and zGap, at another hash than secondHashFunction, or at those files' own digest. No law. No soundness of a
verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstDoor
import Johnson.Desc.K14.Law.SharedConstCodesMade
import Johnson.P5J.MgAtAll

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

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **Every sub-protocol of the seated shared chain passes its own test: from the head alone.** -/
theorem chainOk_at_head (h : P5J.AtMgA o Z D r Zp Np cF x) : chainOkAt Zp Np = true := by
  obtain ⟨Z', N', hZ', hN', hc⟩ := chainOk_descPure h.laid.value h.laid.planOk
  obtain rfl : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  obtain rfl : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  exact hc

/-- "The written data are laid", back from the head's fields. -/
theorem laidPOf_at_head (h : P5J.AtMgA o Z D r Zp Np cF x) :
    LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r) :=
  h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks

/-- **The constant's named tests accept, under one pin.** -/
theorem tests_at_head (h : P5J.AtMgA o Z D r Zp Np cF x)
    (hy : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made =
      true) {Xi : Type} (G : FileDescription Xi) : Tests (planAt Zp Np G) := by
  obtain ⟨x', hx, hW⟩ := written_of_made h.scope h.laid.pub hy (laidPOf_at_head h)
  exact tests_at hx hW h.laid.places G (chainOk_at_head h)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.chainOk_at_head
#print axioms Desc.K14.Law.Sh.laidPOf_at_head
#print axioms Desc.K14.Law.Sh.tests_at_head

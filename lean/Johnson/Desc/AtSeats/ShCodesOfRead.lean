-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/ShCodesOfRead.lean: "THE TWO TABLES READ ONE LIST OF CODES" AND "ONE SHAPE
    OF
THE TEST ON THE TABLE", AT THE SHARED TABLE's CONSTANT AT A PROOF FILE's SEAT, WITH NO PIN OF THE
    DOOR
AND NO SCOPE: from what the road returns and the verifier's own test on what it has made. They
overtake Sh.hcs_in_scope | hcs_of_made (Johnson/Desc/K14/Law/SharedConstCodesAt.lean,
SharedConstCodesMade.lean) wherever that test's accept is in hand. Three calls: no proof of their
    own.

  Sh.front2_at_seat    the seat's test accepts → the shared chain's front test on the planner's
      chains
  Sh.hcs_of_read       Z.made.p.chains.proof.first.codes = (planAt Z N G).Q.codes
  Sh.hlin_of_read      (K13.whereOf Z).lin = (planAt Z N G).Q.par.S
HOW. front2_at_planOk · codes_p14Of · lin_p14Of (Johnson/P2R0R/SizedIsRead.lean): the
    planner's
chains are read back from what it has sized, and the front test compares the two.
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstOpenAt
import Johnson.P2R0R.SizedIsRead

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

/-- The seat's test gives the front test on the planner's chains. -/
theorem front2_at_seat {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub} (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (hG : (seatF o Z N B' cF).planOk = true) :
    VerifiableInference.OnPublicFiles.OkD.AtC.front2 Z.p.chains = true :=
  P2R0.front2_at_planOk o ProofFile.pureRoad.links Z Z.p.chains _ _ _ _ _ B' (fun s => s) (ProofFile.startS Z)
      cF
    hG

/-- **One list of codes: no pin, no scope.** -/
theorem hcs_of_read {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hp : ProofFile.pubPlain o pol lay KL = .ok Z) (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (hG : (seatF o Z N B' cF).planOk = true)
        {Xi : Type} (G : FileDescription Xi) :
    Z.made.p.chains.proof.first.codes = (planAt Z N G).Q.codes :=
  P2R0.codes_p14Of hp (front2_at_seat N B' cF hG) (Desc.K14.beforePointOf N)

/-- **One shape of the test on the table: no pin, no scope.** -/
theorem hlin_of_read {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hp : ProofFile.pubPlain o pol lay KL = .ok Z) (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (hG : (seatF o Z N B' cF).planOk = true)
        {Xi : Type} (G : FileDescription Xi) :
    (VerifiableInference.Desc.K13.whereOf Z).lin = (planAt Z N G).Q.par.S :=
  P2R0.lin_p14Of hp (front2_at_seat N B' cF hG) (Desc.K14.beforePointOf N)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.front2_at_seat
#print axioms Desc.K14.Law.Sh.hcs_of_read
#print axioms Desc.K14.Law.Sh.hlin_of_read

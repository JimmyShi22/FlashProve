-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.WrittenAtSeats
import Johnson.Desc.K12.Law.StretchFull
import Johnson.Desc.K12.Law.Sizes.PlacesAtScope
import Johnson.Desc.K12.Law.Sizes.MoreAtScope
import Johnson.Desc.K12.Law.FirstTreeOfMade
/-
Johnson/Loose/H2K12/WrittenAtFull.lean: AT THE FULL SIZE: THE WRITTEN ROUNDS OF THE PROXIMITY TEST's
THREE LATER PLACES IN THE PROOF FILE's DESCRIPTION ARE THE CLOSED PLACES': H2K.Pub.writtenOf
N.‹x›.nums = H2K.Pub.writtenOf pi‹X›Full.nums. An assembly, no letter left on the closed side:
WrittenAtSeats.lean's written_at_U | O | W at R := Johnson.G.dryProofFull · the kernel's lines
on that list (Law/StretchFull.lean) · stages, work and ownMask at the full size
(Law/Sizes/PlacesAtScope.lean | MoreAtScope.lean: under AtFull) · the first tree's number
(Law/FirstTreeOfMade.lean). BOOK-KEEPING ON THE PLAN. NO
SOUNDNESS IS CLAIMED. NOTHING ON HIDING. THE FIRST CHAIN's SEAT IS NOT HERE.
THE PREMISES: hZ (the plain road's public part) · hN (the places' numbers) · hp (the description's
tests on the plan) · A : AtFull (what the planner has made is the full size's) · hW : THE
DESCRIPTION's DECLARED ROUNDS, WRITTEN OUT, ARE THE WRITTEN LISTS (Johnson.G.OfPlan.writtenOf
"proof file" F.roundsDeclaredByBlocks = .ok dryProofFull): in scope the conclusion of seat_in_scope
(Johnson/Goal/Numbers/PlanWrittenDescScope.lean)
from the test seatPinnedProof, which the seated value asks; taken here as a hypothesis.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Member (piUFull piOFull piWFull dsOf earlierFull)
open Johnson.G (dryProofFull)

/-- AT G_u's SEAT, AT THE FULL SIZE. -/
theorem written_at_seat_U (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.writtenOf N.U.nums = H2K.Pub.writtenOf piUFull.nums :=
  written_at_U o pol lay KL Z hZ mk N c hN hp dryProofFull hW piUFull.nums (dsOf piUFull) 8
    H2K.Member.rounds_UFull H2K.Member.bat_UFull H2K.Member.stretch_UFull
    (H2K.Sizes.place_U_of_full A hN).2.1 (H2K.Sizes.place_U_of_full A hN).1
    (H2K.Sizes.more_U_of_full A hN).2.1
    (by
      rw [(H2K.Made.places_firstTree Z.made N hN).2.1]
      exact (congrArg (0 + ·) H2K.Member.roots_UFull).trans rfl)

/-- AT G_omega's SEAT, AT THE FULL SIZE. -/
theorem written_at_seat_O (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.writtenOf nO.nums = H2K.Pub.writtenOf piOFull.nums :=
  written_at_O o pol lay KL Z hZ mk N nO hO c hN hp dryProofFull hW piOFull.nums (dsOf piOFull) 43
    H2K.Member.rounds_OFull H2K.Member.bat_OFull H2K.Member.stretch_OFull
    (H2K.Sizes.place_O_of_full A hN nO hO).2.1 (H2K.Sizes.place_O_of_full A hN nO hO).1
    (H2K.Sizes.more_O_of_full A hN nO hO).2.1
    (by
      rw [(H2K.Made.places_firstTree Z.made N hN).2.2.1 nO hO]
      exact (congrArg (0 + ·) H2K.Member.roots_OFull).trans rfl)

/-- AT THE OWN TEST's SEAT, AT THE FULL SIZE. -/
theorem written_at_seat_W (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.writtenOf N.W.nums = H2K.Pub.writtenOf piWFull.nums :=
  written_at_W o pol lay KL Z hZ mk N c hN hp dryProofFull hW piWFull.nums (dsOf piWFull)
    earlierFull H2K.Member.rounds_WFull H2K.Member.stretch_WFull
    (H2K.Sizes.place_W_of_full A hN).2.1 (H2K.Sizes.place_W_of_full A hN).1
    (H2K.Sizes.more_W_of_full A hN).2.1
    (by
      have e1 : (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks.1 = Z.D.1 := ((FileDescription.planOk_ok _).1 hp).decl₁
      rw [H2K.Made.firstTree_W Z.made N Z.D hN (pub_D o pol lay KL Z hZ), ← e1,
        roots_whole (H2K.Pub.chains_of_written hW).1, H2K.Member.roots_first]
      rfl)

end H2K.JointK

#print axioms H2K.JointK.written_at_seat_U
#print axioms H2K.JointK.written_at_seat_O
#print axioms H2K.JointK.written_at_seat_W

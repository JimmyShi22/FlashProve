-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.WrittenAtFull
import Johnson.Desc.K12.Law.RoundsOfG
/-
Johnson/Loose/H2K12/RoundsAtFull.lean: AT THE FULL SIZE: THE DECLARED ROUNDS THEMSELVES, AND THE
NUMBER «free», OF THE PROXIMITY TEST's THREE LATER PLACES IN THE PROOF FILE's DESCRIPTION ARE THE
CLOSED PLACES': H2U.roundsOfNums N.‹x›.nums = H2U.roundsOfNums pi‹X›Full.nums · N.‹x›.nums.free =
pi‹X›Full.nums.free. An assembly beside H2K12/WrittenAtFull.lean, under the same premises (hZ · hN ·
hp · A : AtFull · hW), off H2K12/WrittenAtSeats.lean's stretch_at_U | O: the general step is
Law/RoundsOfG.lean's roundsOfNums_at_stretch (what readers take of a declared round tells its entry,
its shapes and its sources apart: at the own test's seat for the two earlier chains' stand-ins,
whose runs' tags are one byte each). BOOK-KEEPING ON THE
PLAN. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  earlier_full         at the written lists the stand-ins for the two earlier chains are the closed
      ones (83 and 11 roots).
  rounds_at_seat_U | O | W · free_at_seat_U | O | W
THE FIRST CHAIN's SEAT IS NOT HERE.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Member (piUFull piOFull piWFull dsOf earlierFull)
open Johnson.G (dryProofFull)

/-- At the written lists the stand-ins for the two earlier chains are the closed ones. -/
theorem earlier_full {D : Johnson.G.OfPlan.Decl3}
    (hW : Johnson.G.OfPlan.writtenOf "proof file" D = .ok dryProofFull) :
    H2K.Pub.earlierOf D = earlierFull := by
  unfold H2K.Pub.earlierOf
  rw [roots_whole (H2K.Pub.chains_of_written hW).1, H2K.Member.roots_first,
    roots_whole (H2K.Pub.chains_of_written hW).2.1]
  rw [show ((dryProofFull.2.1.map (·.1)).map (·.entry.roots)).sum = 11 from
    H2K.Member.roots_shared]
  rfl

/-- AT G_u's SEAT, AT THE FULL SIZE: the declared rounds. -/
theorem rounds_at_seat_U (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2U.roundsOfNums N.U.nums = H2U.roundsOfNums piUFull.nums := by
  obtain ⟨hx, hr0, hl, _⟩ := stretch_at_U o pol lay KL Z hZ mk N c hN hp dryProofFull hW 8
    H2K.Member.bat_UFull
  exact H2K.Pub.roundsOfNums_at_stretch H2K.Pub.srcInj_nil hx hr0 H2K.Member.rounds_UFull
    (by rw [hl]; exact H2K.Member.stretch_UFull)
    (H2K.Sizes.place_U_of_full A hN).2.1 (H2K.Sizes.place_U_of_full A hN).1

/-- AT G_omega's SEAT, AT THE FULL SIZE: the declared rounds. -/
theorem rounds_at_seat_O (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2U.roundsOfNums nO.nums = H2U.roundsOfNums piOFull.nums := by
  obtain ⟨hx, hr0, hl, _⟩ := stretch_at_O o pol lay KL Z hZ mk N nO hO c hN hp dryProofFull hW 43
    H2K.Member.bat_OFull
  exact H2K.Pub.roundsOfNums_at_stretch H2K.Pub.srcInj_nil hx hr0 H2K.Member.rounds_OFull
    (by rw [hl]; exact H2K.Member.stretch_OFull)
    (H2K.Sizes.place_O_of_full A hN nO hO).2.1 (H2K.Sizes.place_O_of_full A hN nO hO).1

/-- AT THE OWN TEST's SEAT, AT THE FULL SIZE: the declared rounds. The public part's road is not
asked. -/
theorem rounds_at_seat_W (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2U.roundsOfNums N.W.nums = H2U.roundsOfNums piWFull.nums := by
  obtain ⟨_, _, b3⟩ := Keeps.planOk_blocks _ hp
  have mW : ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk') ∈
      (descN o mk guardedProximityTestParts Z N c).second.blocksInOrder :=
    (descN_second o mk guardedProximityTestParts Z N c) ▸ List.mem_append_right _ List.mem_cons_self
  have pW : (proximityTestKind guardedProximityTestParts (pOwn N) : Blk').planOk = true :=
    (ownEntry_sits ProofFile.Cl _).plan (b3 _ mW)
  obtain ⟨hr0, _⟩ := seat_rounds ⟨3, none, 2, .K12⟩ N.W pW
  have hx := (H2K.Pub.chains_of_written hW).2.2
  rw [earlier_full hW, decl_atW] at hx
  exact H2K.Pub.roundsOfNums_at_stretch (pre := []) (H2K.Pub.srcInj_tags 83 11) hx hr0
    H2K.Member.rounds_WFull H2K.Member.stretch_WFull
    (H2K.Sizes.place_W_of_full A hN).2.1 (H2K.Sizes.place_W_of_full A hN).1

/-- «free» at G_u's seat, at the full size. No AtFull is asked. -/
theorem free_at_seat_U (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    N.U.nums.free = piUFull.nums.free :=
  (stretch_at_U o pol lay KL Z hZ mk N c hN hp dryProofFull hW 8
    H2K.Member.bat_UFull).2.2.2.trans H2K.Member.roots_UFull

/-- «free» at G_omega's seat, at the full size. -/
theorem free_at_seat_O (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    nO.nums.free = piOFull.nums.free :=
  (stretch_at_O o pol lay KL Z hZ mk N nO hO c hN hp dryProofFull hW 43
    H2K.Member.bat_OFull).2.2.2.trans H2K.Member.roots_OFull

/-- «free» at the own test's seat: nothing is declared in front. No written list is asked. -/
theorem free_at_seat_W (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    N.W.nums.free = piWFull.nums.free :=
  (plain_free o pol lay KL Z hZ mk N c hN hp).2.2.2

end H2K.JointK

#print axioms H2K.JointK.rounds_at_seat_U
#print axioms H2K.JointK.rounds_at_seat_O
#print axioms H2K.JointK.rounds_at_seat_W
#print axioms H2K.JointK.free_at_seat_U
#print axioms H2K.JointK.free_at_seat_O
#print axioms H2K.JointK.free_at_seat_W

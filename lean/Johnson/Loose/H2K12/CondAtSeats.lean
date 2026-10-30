-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.WrittenAtFull
import Johnson.Loose.H2K12.ClosedAtSeats
import Johnson.Desc.K12.Law.CondAtFull
/-
H2K12/CondAtSeats.lean: the condition of the law of a proximity test (the kind K12),
and the two forms "every written round is below", at the three later seats of the proof file's
description, at the full size: an assembly: Johnson/Desc/K12/Law/CondAtFull.lean (all three at the
places made off a plan whose sized record is the full size's, under one named premise on the written
rounds), H2K12/WrittenAtFull.lean (that premise at the seats) and H2K12/ClosedAtSeats.lean (the test
on the plan of the kind's block at a seat, from the description's).
The premises, each with who can pay it: hZ: the plain road's public part; hN: the places' numbers;
hp: the description's tests on the plan: from the yes of `onlineDescription` and of the seat's test on the
plan (H2K12/SitsAtDescPure.lean). A: what the planner has made is sized as at the full size
(`AtFull`): in the goals' scope from `configure`'s yes (Law/Sizes/StageSizesAtScope.lean). hW: the
description's declared rounds, written out, are the written lists: in scope from a yes of the
test `seatPinnedProof` (`seat_in_scope`, Johnson/Goal/Numbers/PlanWrittenDescScope.lean); the
description itself does not ask that test; the value that is laid for the proof file does.
The three on the condition take one more: hpub: `pubOk` at the seat's place and the record's codes
K: from a yes of the block's decision (`k12_guards`, Law/TopH.lean). K is a free letter.
THE SIX ON THE ROUNDS TAKE NO CODES AND NO RECORD: they are sentences on public data alone.
`roundsHold_at_seat_U` and its like: `RoundsHoldAt` (RoundsHold.lean): the radii pinned by facts.
`roundsBelow_at_seat_U` and its like: `RoundsBelowAt`, which holds no clause on the
radii: the weight lies in the former.
No test on the plan's prices is asked.
Limits: those of the files that it calls. The payers are named, not called: no theorem here joins
them. Not the first chain's seat. At Omega's seat: that the plan has such a place is a premise. The
full size only. One round's share each, no sum; part of the 128 bits is work at "CS" and "BASE";
"BAT"'s number is priced and is no law's count.
Nothing on soundness of a verifier. Nothing on hiding.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open OnBytes.Slice
open Johnson.G (dryProofFull)
open scoped ENNReal

/-- The condition at the seat of the folded row's test. -/
theorem k12Condition_at_seat_U (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) (K : OnBytes.Codes)
    (hpub : H2K.Pub.pubOk (pGu N) K = true) :
    H2K.Pub.K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.folded.stages)
      (pGu N) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.k12Condition_at_full_U A hN _ K
    (written_at_seat_U o pol lay KL Z hZ mk N c hN hp A hW) hpub

/-- Every written round is below, with the radii pinned, at that seat: on public data alone. -/
theorem roundsHold_at_seat_U (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.RoundsHoldAt (pGu N)
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.folded.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.roundsHold_at_full_U A hN _
    (written_at_seat_U o pol lay KL Z hZ mk N c hN hp A hW) (plan_at_seat_U o Z mk N c hp)

/-- So the form `RoundsBelowAt`. -/
theorem roundsBelow_at_seat_U (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.RoundsBelowAt (pGu N)
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.folded.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (roundsHold_at_seat_U o pol lay KL Z hZ mk N c hN hp A hW).below

/-- The condition at the seat of Omega's test. -/
theorem k12Condition_at_seat_O (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) (K : OnBytes.Codes)
    (hpub : H2K.Pub.pubOk (pGomega nO) K = true) :
    H2K.Pub.K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.omega.stages)
      (pGomega nO) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.k12Condition_at_full_O A hN _ K nO hO
    (written_at_seat_O o pol lay KL Z hZ mk N nO hO c hN hp A hW) hpub

/-- Every written round is below, with the radii pinned, at that seat: on public data alone. -/
theorem roundsHold_at_seat_O (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.RoundsHoldAt (pGomega nO)
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.omega.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.roundsHold_at_full_O A hN _ nO hO
    (written_at_seat_O o pol lay KL Z hZ mk N nO hO c hN hp A hW)
        (plan_at_seat_O o Z mk N nO hO c hp)

/-- So the form `RoundsBelowAt`. -/
theorem roundsBelow_at_seat_O (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.RoundsBelowAt (pGomega nO)
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.omega.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (roundsHold_at_seat_O o pol lay KL Z hZ mk N nO hO c hN hp A hW).below

/-- The condition at the seat of the request's own test. -/
theorem k12Condition_at_seat_W (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) (K : OnBytes.Codes)
    (hpub : H2K.Pub.pubOk (pOwn N) K = true) :
    H2K.Pub.K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.own.stages)
      (pOwn N) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.k12Condition_at_full_W A hN _ K
    (written_at_seat_W o pol lay KL Z hZ mk N c hN hp A hW) hpub

/-- Every written round is below, with the radii pinned, at that seat: on public data alone. -/
theorem roundsHold_at_seat_W (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.RoundsHoldAt (pOwn N)
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.own.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.roundsHold_at_full_W A hN _
    (written_at_seat_W o pol lay KL Z hZ mk N c hN hp A hW) (plan_at_seat_W o Z mk N c hp)

/-- So the form `RoundsBelowAt`. -/
theorem roundsBelow_at_seat_W (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) :
    H2K.Pub.RoundsBelowAt (pOwn N)
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.own.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (roundsHold_at_seat_W o pol lay KL Z hZ mk N c hN hp A hW).below

end H2K.JointK

#print axioms H2K.JointK.k12Condition_at_seat_U
#print axioms H2K.JointK.roundsHold_at_seat_U
#print axioms H2K.JointK.roundsBelow_at_seat_U
#print axioms H2K.JointK.k12Condition_at_seat_O
#print axioms H2K.JointK.roundsHold_at_seat_O
#print axioms H2K.JointK.roundsBelow_at_seat_O
#print axioms H2K.JointK.k12Condition_at_seat_W
#print axioms H2K.JointK.roundsHold_at_seat_W
#print axioms H2K.JointK.roundsBelow_at_seat_W

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/RowTakers/AllSeg.lean: EIGHT MORE PIECES OF THE WRITTEN BOOK's ENTRIES, WITHOUT A TEST
ON THE NUMBERS: AT EACH g = 1 … 11: THE 5,130 CARRYING ENTRIES OF THE CHAIN OF SEGMENTS GIVE
allCarriedAt g; THE FIRST CHAIN's FOLDS' PIECE GIVES foldSpentAt g ALONE; THE SIX OTHER SMALL PIECES
GIVE NOTHING; AND TWO TWINS THAT SAY NO. (The tenth piece is the written "[]": ownedIn_nil,
AllDefs.lean.) THE OPTIONS' LINES AND THE TWO LINES "unfold … simp only …" IN FRONT OF THE KERNEL
FOLLOW ANOTHER HOUSE's raw5_seg (AtFullSide/K14/RawTwinFifth.lean) AND rawSegW_length
(AtFullSide/K14/RawLengthsWritten.lean). EVALUATIONS IN LEAN's KERNEL (decide +kernel; no compiled
code). A sister of AllDefs.lean in this folder; the whole and its limits:
AtFullSide/K1/OwnerEntriesAtSwitches.lean's head. NO PROPERTY IS CLAIMED.

Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.RowTakers.AllDefs
import AtFullSide.K14.RawLengthsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open VerifiableInference.Desc (Place KindName)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At each of the eleven groups: all entries of that owner in the chain of segments' piece.** -/
theorem ownedSegB : ((List.range 11).all fun i =>
    decide (ownedIn rawSegW (i + 1) = allCarriedAt (i + 1))) = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A NEGATIVE TEST: with the first entry struck the test says no. -/
theorem ownedSegB_bent : decide (ownedIn rawSegW 1 = (allCarriedAt 1).tail) = false := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The seven small pieces**: the first holds one entry of that owner, the six others none. -/
theorem ownedShortB : ((List.range 11).all fun i =>
    decide (ownedIn foldsFirstW (i + 1) = [foldSpentAt (i + 1)]) &&
    decide (ownedIn foldsSharedW (i + 1) = []) &&
    decide (ownedIn [splitEntryWritten] (i + 1) = []) &&
    decide (ownedIn rawCarriesFoldedW (i + 1) = []) &&
    decide (ownedIn rawCarriesOmegaW (i + 1) = []) &&
    decide (ownedIn rawCarriesWW (i + 1) = []) &&
    decide (ownedIn rawOwnCarryW (i + 1) = [])) = true := by
  decide +kernel

/-- A NEGATIVE TEST: asked for nothing in the first small piece, at g = 1, the test says no. -/
theorem ownedShortB_bent : decide (ownedIn foldsFirstW 1 = []) = false := by
  decide +kernel

end AtFullSide.K1

#print axioms AtFullSide.K1.ownedSegB
#print axioms AtFullSide.K1.ownedSegB_bent
#print axioms AtFullSide.K1.ownedShortB
#print axioms AtFullSide.K1.ownedShortB_bent

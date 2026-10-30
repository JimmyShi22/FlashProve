-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/RawAtK7.lean: at the written description WP, the library's written sendings and the
merges that mergesByName guesses: at the one part of the place ⟨1, some 24, 1, K7⟩ (the next token)
the first chain's table has no count, the part spends nothing and nothing is carried to it. Closed
facts, each by one evaluation in Lean's kernel, and their consequences at whatever book bookWhole
returns there. No definition.

  `rawDueW_atK7`, `rawDueAtK7`       the table has no count for the part
  `rawNoFoldAtK7`, `rawWantsAtK7`    the place holds no fold; the part has no stretch
  `rawSpentEAtK7`                    the part spends nothing
  `rawCarryFrontAtK7`, `rawCarrySegAtK7`, `rawCarryBackAtK7`, `rawCarryAtK7`   nothing is carried to it
  `rawCarrySeg_control`, `rawWants_control`   the same evaluations can come out otherwise: at two
                                     other addresses their answer is not empty

The road is that of AtFullSide/K14/RawAtSwitch24.lean. rawSegW is what the maker returns
(`rawSeg_returns`, AtFullSide/K14/RawAheadWritten.lean): at a rejection it would be empty, and a
statement on it idle.

Limits. That bookWhole returns at WP is a premise here. The sendings are found by labels; the merges
are a guess. The evaluations are Lean's kernel's: no independent checker has replayed them. Names,
numbers and addresses alone: nothing on soundness, completeness or hiding.
-/
import AtFullSide.K14.RawAtSwitch24

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
/-- The written rows have no count for the part. -/
theorem rawDueW_atK7 : dueAt rawRowsFirstW ⟨⟨1, some 24, 1, .K7⟩, 0⟩ = ⟨0, 0⟩ := by
  decide +kernel

/-- **The first chain's table has no count for the part.** -/
theorem rawDueAtK7 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    dueAt (B.rowsOf 0) ⟨⟨1, some 24, 1, .K7⟩, 0⟩ = ⟨0, 0⟩ :=
  rawDue_of_written hB rawDueW_atK7

set_option maxRecDepth 1000000 in
/-- The place holds no fold. -/
theorem rawNoFoldAtK7 : rawNoFoldAt ⟨1, some 24, 1, .K7⟩ = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The part has no stretch. -/
theorem rawWantsAtK7 : rawWantsAt ⟨⟨1, some 24, 1, .K7⟩, 0⟩ = some [] := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at K13's part 1 the same evaluation has a stretch. -/
theorem rawWants_control :
    (rawWantsAt ⟨⟨1, none, 3, .K13⟩, 1⟩).any (fun l => !l.isEmpty) = true := by
  decide +kernel

/-- **The part spends nothing.** -/
theorem rawSpentEAtK7 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    spentE B ⟨⟨1, some 24, 1, .K7⟩, 0⟩ = [] :=
  rawSpentE_nil_of_wants hB rawNoFoldAtK7 rawWantsAtK7

set_option maxRecDepth 1000000 in
/-- The written pieces in front carry nothing to the part. -/
theorem rawCarryFrontAtK7 : rawCarryNamed rawFrontW ⟨⟨1, some 24, 1, .K7⟩, 0⟩ = [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The chain of segments' carrying entries carry nothing to the part: an evaluation in Lean's
kernel. -/
theorem rawCarrySegAtK7 : rawCarryNamed rawSegW ⟨⟨1, some 24, 1, .K7⟩, 0⟩ = [] := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at the part 0 of the switch of segment 24 the same evaluation is not empty. -/
theorem rawCarrySeg_control :
    (rawCarryNamed rawSegW ⟨⟨1, some 24, 2, .K2⟩, 0⟩).isEmpty = false := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Nor do the written pieces behind. -/
theorem rawCarryBackAtK7 : rawCarryNamed rawBackW ⟨⟨1, some 24, 1, .K7⟩, 0⟩ = [] := by
  decide +kernel

/-- **Nothing is carried to the part.** -/
theorem rawCarryAtK7 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    (carryE B ⟨⟨1, some 24, 1, .K7⟩, 0⟩).map Ahead.named = [] :=
  rawCarry_of_pieces hB rawCarryFrontAtK7 rawCarrySegAtK7 rawCarryBackAtK7

end AtFullSide.K14

#print axioms AtFullSide.K14.rawDueW_atK7
#print axioms AtFullSide.K14.rawDueAtK7
#print axioms AtFullSide.K14.rawNoFoldAtK7
#print axioms AtFullSide.K14.rawWantsAtK7
#print axioms AtFullSide.K14.rawWants_control
#print axioms AtFullSide.K14.rawSpentEAtK7
#print axioms AtFullSide.K14.rawCarryFrontAtK7
#print axioms AtFullSide.K14.rawCarrySegAtK7
#print axioms AtFullSide.K14.rawCarrySeg_control
#print axioms AtFullSide.K14.rawCarryBackAtK7
#print axioms AtFullSide.K14.rawCarryAtK7

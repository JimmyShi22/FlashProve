-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawTwinFifth.lean: THE FIFTH TEST's TWIN clause5P (Honest/BookLinear/Fifth.lean)
ACCEPTS THE RAW BOOK's 13,116 ENTRIES rawAheadW AT orderOf WP AND posW (raw5_test). BY EVALUATIONS
IN LEAN's KERNEL (decide +kernel), PIECE BY PIECE, AND ONE JOIN. A WORKING FILE. Statements with
their proofs; no definition.

  raw5_wants      at the 7,940 stretches' entries: the maker's own term
  raw5_short      at the folds' and the split's entries, and at the four short written lists of
                  carrying entries
  raw5_seg        at rawSegW, the 5,130 carrying entries of the chain of segments: the maker's own
                  term at the written messages
  raw5_test       **clause5P posW (orderOf WP) rawAheadW = true**: the four, by clause5P_append and
                  rawAhead_three (AtFullSide/K14/RawTwinKit.lean)
  raw5_bent       with posW one off the twin rejects the stretches' entries

What it is for: with orderW_nodup and clause5P_of it is the fifth test's Bool at rawAheadW; with
rawAhead_written (AtFullSide/K14/RawAheadWritten.lean) at the raw book's own entries. Neither step
is drawn here.

In front of raw5_wants and raw5_seg maxRecDepth and maxHeartbeats are lifted. raw5_seg first unfolds
rawSegW, segmentCarries and linkOf and rewrites by Johnson.Unfolds.splitOn_eq and slice_toNat?_eq:
the kernel cannot run linkOf's text as it stands. IF THE FRAME's segmentCarries TURNS, THAT PROOF
RIDES ANEW; that its text can stay is a forecast.

Limits. A FACT ON WRITTEN VALUES: at the proof file's IOP as written in Lean at the full size
(P2Law.ProofPlan.WP), the written sendings (Johnson.G.proofSendsFull) and the merges that
mergesByName lays ("a guess", in the frame's own word): rawAheadW
(AtFullSide/K14/RawAheadWritten.lean) is made at these. rawSegW STANDS OVER THE FRAME's
segmentCarries AS IT IS TODAY. The twin's yes, not the test's. Nothing on what an evaluation costs.
Nothing on any property.
-/
import AtFullSide.K14.RawTwinKit
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The twin accepts the 7,940 stretches' entries. -/
theorem raw5_wants : clause5P posW (orderOf WP) (rawWantsW.map (·.entry)) = true := by
  decide +kernel

/-- The twin accepts the short written pieces. -/
theorem raw5_short :
    clause5P posW (orderOf WP) (foldsFirstW ++ foldsSharedW ++ [] ++ [splitEntryWritten]) = true ∧
    clause5P posW (orderOf WP) rawCarriedShortW = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The twin accepts the 5,130 carrying entries of the chain of segments. -/
theorem raw5_seg : clause5P posW (orderOf WP) rawSegW = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **THE FIFTH TEST's TWIN ACCEPTS THE RAW BOOK's ENTRIES.** -/
theorem raw5_test : clause5P posW (orderOf WP) rawAheadW = true := by
  have e : rawSpentW =
      rawWantsW.map (·.entry) ++ (foldsFirstW ++ foldsSharedW ++ [] ++ [splitEntryWritten]) := by
    unfold rawSpentW
    simp only [List.append_assoc]
  rw [rawAhead_three, clause5P_append, clause5P_append, e, clause5P_append, raw5_wants,
    raw5_short.1, raw5_seg, raw5_short.2]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- With posW one off the twin rejects the stretches' entries. -/
theorem raw5_bent :
    clause5P (fun p => posW p + 1) (orderOf WP) (rawWantsW.map (·.entry)) = false := by
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.raw5_wants
#print axioms AtFullSide.K14.raw5_short
#print axioms AtFullSide.K14.raw5_seg
#print axioms AtFullSide.K14.raw5_test
#print axioms AtFullSide.K14.raw5_bent

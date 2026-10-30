-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawTwinSeventh.lean: THE SEVENTH TEST's TWIN clause7S
(Honest/BookLinear/Seventh.lean) ACCEPTS THE RAW BOOK's 13,116 ENTRIES rawAheadW, AT 20 ROUNDS OF
THE SORT (raw7_test). BY EVALUATIONS IN LEAN's KERNEL (decide +kernel), A LAW OF THE FRAME's, AND
ONE JOIN. A WORKING FILE. Statements with their proofs; no definition.

  raw7_spent      at rawSpentW (AtFullSide/K14/RawTwinKit.lean): the stretches' 7,940 entries, the
                  folds' 28, the split's one
  rawSeg_carried  none of rawSegW's entries is a spending one: NO EVALUATION: the frame's
                  BookRow.segmentCarries_once (Honest/BookRowKit.lean) at rawSeg_returns
                  (AtFullSide/K14/RawAheadWritten.lean)
  rawShort_carried   nor any of the four short written lists' 17
  raw7_test       **clause7S 20 rawAheadW = true**: the twin reads the spending entries alone
                  (clause7S_filter), and these are rawSpentW's
  raw7_bent       with the split's entry laid in a second time the twin rejects

What it is for: by clause7_of it is the seventh test's Bool at rawAheadW, and by spent_apart the
premise "no two spending entries share a coin" of the eighth's law. Neither step is drawn here.

In front of raw7_spent and raw7_bent maxRecDepth and maxHeartbeats are lifted. No proof here opens
segmentCarries: what stands inside that maker is not named.

Limits. A FACT ON WRITTEN VALUES: at the proof file's IOP as written in Lean at the full size
(P2Law.ProofPlan.WP), the written sendings (Johnson.G.proofSendsFull) and the merges that
mergesByName lays ("a guess", in the frame's own word): rawAheadW
(AtFullSide/K14/RawAheadWritten.lean) is made at these. rawSegW STANDS OVER THE FRAME's
segmentCarries AS IT IS TODAY. The twin's yes, not the test's. Nothing on what an evaluation costs.
Nothing on any property.
-/
import AtFullSide.K14.RawTwinKit
import Johnson.Desc.ProofFile.Honest.BookRowKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The twin accepts the pieces that hold all spending entries. -/
theorem raw7_spent : clause7S 20 rawSpentW = true := by
  decide +kernel

/-- None of the carrying entries of the chain of segments is a spending one: by the frame's own law
on the maker, at the maker's return. -/
theorem rawSeg_carried : rawSegW.filter (·.once) = [] :=
  List.filter_eq_nil_iff.2 fun e he => by
    rw [BookRow.segmentCarries_once rawSeg_returns e he]
    decide

/-- Nor any entry of the four short written lists. -/
theorem rawShort_carried : rawCarriedShortW.filter (·.once) = [] := by
  decide +kernel

/-- **THE SEVENTH TEST's TWIN ACCEPTS THE RAW BOOK's ENTRIES.** -/
theorem raw7_test : clause7S 20 rawAheadW = true := by
  have h := raw7_spent
  rw [clause7S_filter] at h ⊢
  rw [rawAhead_three, List.filter_append, List.filter_append, rawSeg_carried, rawShort_carried,
    List.append_nil, List.append_nil]
  exact h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- With the split's entry laid in a second time the twin rejects. -/
theorem raw7_bent : clause7S 20 (rawSpentW ++ [splitEntryWritten]) = false := by
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.raw7_spent
#print axioms AtFullSide.K14.rawSeg_carried
#print axioms AtFullSide.K14.rawShort_carried
#print axioms AtFullSide.K14.raw7_test
#print axioms AtFullSide.K14.raw7_bent

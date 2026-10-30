-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsCut/Join.lean: the entries of the written book at the kind's place are its two entries,
so at that place the test k11Lends at the written book is the test at two entries.

  k11_short            no entry of the eight written pieces stands at the kind's place
  ahead_at_k11         the entries at the kind's place
  k11Lends_is_small    the test at the written book is the test over the two entries

Limits. At the written book; that bookWhole returns its rows and entries stands in
LotsAnswerAtTheBook.lean.
-/
import AtFullSide.K11.LendsCut.Wants
import AtFullSide.K11.LendsCut.Seg
import AtFullSide.K14.RawEntriesKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open ProofFile.Honest
open ProofFile.Honest.K11 (k11Lends)
open AtFullSide.K14 (rawAheadW rawWantsW rawSegW rawShortW rawRowsFirstW rawRowsSharedW rawRowsSecondW)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No entry of the eight written pieces stands at the kind's place. -/
theorem k11_short : (rawShortW.all fun e => e.spender.place != IM.k11Place) = true := by
  decide +kernel

/-- Of a list with no entry at the kind's place the filter is empty. -/
theorem filter_off_k11 (l : List Ahead)
    (h : (l.all fun e => e.spender.place != IM.k11Place) = true) :
    (l.filter fun e => e.spender.place == IM.k11Place) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he h2
  have h1 := List.all_eq_true.1 h e he
  exact (bne_iff_ne.1 h1) (beq_iff_eq.1 h2)

/-- **The written book's entries at the kind's place.** -/
theorem ahead_at_k11 :
    (rawAheadW.filter fun e => e.spender.place == IM.k11Place) = [k11Sum, k11Ends] := by
  have hs := filter_off_k11 _ k11_seg
  have ht := filter_off_k11 _ k11_short
  have e : (rawAheadW.filter fun e => e.spender.place == IM.k11Place) =
      ((rawWantsW.map (·.entry)).filter fun e => e.spender.place == IM.k11Place) ++
        (rawShortW.filter fun e => e.spender.place == IM.k11Place) := by
    unfold rawAheadW rawShortW
    simp only [List.filter_append, hs, List.nil_append, List.append_nil, List.append_assoc]
  rw [e, k11_wants, ht, List.append_nil]

/-- **At the kind's place the test at the written book is the test over the two entries.** -/
theorem k11Lends_is_small (P : HeadMergeP) :
    k11Lends k11BookW 0 IM.k11Place P = k11Lends k11BookS 0 IM.k11Place P := by
  unfold k11Lends
  refine lendsRow_of_fields (by show rawRowsFirstW = rawRowsFirstW; rfl)
    (by show rawRowsSharedW = rawRowsSharedW; rfl) (by show rawRowsSecondW = rawRowsSecondW; rfl)
    0 IM.k11Place (fun i => ?_) _
  show (rawAheadW.filter fun e => e.spender == ⟨IM.k11Place, i⟩) =
    [k11Sum, k11Ends].filter fun e => e.spender == ⟨IM.k11Place, i⟩
  rw [filter_spender, ahead_at_k11]

end AtFullSide.K11

#print axioms AtFullSide.K11.k11_short
#print axioms AtFullSide.K11.filter_off_k11
#print axioms AtFullSide.K11.ahead_at_k11
#print axioms AtFullSide.K11.k11Lends_is_small

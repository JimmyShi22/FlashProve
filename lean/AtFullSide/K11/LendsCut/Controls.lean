-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsCut/Controls.lean: the test k11Lends at the written book on another chain, and at the place in front, read through a book with few entries: so that the controls of LendsWritten.lean are evaluated over these.

  k11Lends_is_small_at   on any chain, at the kind's place, the test at the written book is the test over the two entries
  off8_wants, off8_seg, off8_short   no entry of the pieces stands at the place in front
  k11Lends_is_empty_at8  at the place in front the test at the written book is the test at a book with no entry
  k11LendsS_other, k11LendsE_elsewhere   the two evaluations

Limits. Closed facts by evaluation in Lean's kernel, at the written book.
-/
import AtFullSide.K11.LendsCut.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.Desc (Place)
open ProofFile.Honest
open ProofFile.Honest.K11 (k11Lends)
open AtFullSide.K14 (rawAheadW rawWantsW rawSegW rawShortW rawRowsFirstW rawRowsSharedW rawRowsSecondW)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- **On any chain, at the kind's place, the test at the written book is the test over the two
entries.** -/
theorem k11Lends_is_small_at (ch : Nat) (P : HeadMergeP) :
    k11Lends k11BookW ch IM.k11Place P = k11Lends k11BookS ch IM.k11Place P := by
  unfold k11Lends
  refine lendsRow_of_fields (by show rawRowsFirstW = rawRowsFirstW; rfl)
    (by show rawRowsSharedW = rawRowsSharedW; rfl) (by show rawRowsSecondW = rawRowsSecondW; rfl)
    ch IM.k11Place (fun i => ?_) _
  show (rawAheadW.filter fun e => e.spender == ⟨IM.k11Place, i⟩) =
    [k11Sum, k11Ends].filter fun e => e.spender == ⟨IM.k11Place, i⟩
  rw [filter_spender, ahead_at_k11]

/-- The place in front of the kind's. -/
def k11Front : Place := ⟨1, some 24, 8, .K11⟩

/-- The written rows, with no entry. No book of record. -/
def k11BookE : ProverCoinCounts := ⟨rawRowsFirstW, rawRowsSharedW, rawRowsSecondW, [], []⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No stretch is spent at the place in front. -/
theorem off8_wants : ((rawWantsW.map (·.entry)).all fun e => e.spender.place != k11Front) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No carrying entry stands at the place in front. -/
theorem off8_seg : (rawSegW.all fun e => e.spender.place != k11Front) = true := by
  unfold rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No entry of the eight written pieces stands at the place in front. -/
theorem off8_short : (rawShortW.all fun e => e.spender.place != k11Front) = true := by
  decide +kernel

/-- Of a list with no entry at a place the filter is empty. -/
theorem filter_off_place (l : List Ahead) (pl : Place)
    (h : (l.all fun e => e.spender.place != pl) = true) :
    (l.filter fun e => e.spender.place == pl) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he h2
  have h1 := List.all_eq_true.1 h e he
  exact (bne_iff_ne.1 h1) (beq_iff_eq.1 h2)

/-- **No entry of the written book stands at the place in front.** -/
theorem ahead_at_front : (rawAheadW.filter fun e => e.spender.place == k11Front) = [] := by
  have hw := filter_off_place _ _ off8_wants
  have hs := filter_off_place _ _ off8_seg
  have ht := filter_off_place _ _ off8_short
  unfold rawAheadW
  unfold rawShortW at ht
  simp only [List.filter_append, List.append_eq_nil_iff] at ht
  simp only [List.filter_append, hw, hs, ht, List.nil_append, List.append_nil]

/-- **At the place in front the test at the written book is the test at a book with no entry.** -/
theorem k11Lends_is_empty_at8 (P : HeadMergeP) :
    k11Lends k11BookW 0 k11Front P = k11Lends k11BookE 0 k11Front P := by
  unfold k11Lends
  refine lendsRow_of_fields (by show rawRowsFirstW = rawRowsFirstW; rfl)
    (by show rawRowsSharedW = rawRowsSharedW; rfl) (by show rawRowsSecondW = rawRowsSecondW; rfl)
    0 k11Front (fun i => ?_) _
  show (rawAheadW.filter fun e => e.spender == ⟨k11Front, i⟩) =
    ([] : List Ahead).filter fun e => e.spender == ⟨k11Front, i⟩
  rw [filter_spender, ahead_at_front]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- On chain 1 the row is not lent, over the two entries. -/
theorem k11LendsS_other : k11Lends k11BookS 1 IM.k11Place (k11ParW 18) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At the place in front the row is not lent, over no entry. -/
theorem k11LendsE_elsewhere : k11Lends k11BookE 0 k11Front (k11ParW 18) = false := by
  decide +kernel

end AtFullSide.K11

#print axioms AtFullSide.K11.ahead_at_front
#print axioms AtFullSide.K11.k11LendsS_other
#print axioms AtFullSide.K11.k11LendsE_elsewhere

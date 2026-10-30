-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecNum.lean: at the small files of the setting "record with work", every error
count in the conclusion of `sr_link_joh` (OnBytes/Slice/SmallRecLink.lean) is at most 2 ^ -128 as
a share of its round's written verifier messages, WORK COUNTED.

`sr_link_joh` concludes round-by-round soundness with a list of counts: a 0 in front, then 24: the
link's five, the batching's and the chain's 18. With large counts such a statement is true for free.
This file bounds them. The ground is the planner's yes: the plan that `entrySized` returns at
`smallRecordLines` holds, that is, each round's error, with the planner's term for the distance from
uniform of its draws, is at most 2 ^ (work - 128) (an exact comparison, evaluated in Lean's kernel
in OnBytes/Params/EntryStagesRecordSmall.lean); each number of `smallRecordCounts` is at most its
round's error (OnBytes/Params/EntryCoveredRecord.lean); the plan's entries but the first are the
entries of the 24 written rounds (`record_rounds_entries`, `sr_fmt`). So each written round has its
number as a price (`sr_priced`). Each count of the list is at most its round's number times the
number of the round's typed values (OnBytes/Slice/PricedRound.lean), and `below_of_priced` gives the
clause.

Main definitions: `srCounts`.
Main theorems: `sr_counts`, `sr_entries`, `sr_priced`, `sr_smallAt`, **`sr_err_below`**.

WHAT THE 128 BITS ARE. They are one round's: the share of a round's written verifier messages that
are counted as bad. At the rounds 3, 14, 21 and 23 (LINK, the rounds CS, BASE) 32 of the 128 bits
are work: a written verifier message holds 32 test bits, of which one setting passes. At the other
rounds no bit is work. Without the work the shares at these rounds are about 2 ^ -96.8, 2 ^ -96.5,
2 ^ -97.4 and 2 ^ -97.4 (arithmetic outside Lean; no theorem here). The bound is no bound on the
chance of a false proof and not the sum over the rounds. Two entries of the list are 0 by definition
and cost nothing: the first, which stands before the link's rounds, and that of round 2 (SEND
answer), which draws nothing.

Not claimed. THIS IS NO PROOF OF SOUNDNESS: what `sr_link_joh` asks (`Cb.BCHKS46At`; the tie to the
decision) it still asks, and this file says nothing on it. That proof of work is worth its bits. The
counts for exceptional points are the integer parts of `Cb.bchksBound`, the number in the theorem on
codes that is taken as given. The counts are those of every round of the entry's chain (24); the
record's own seed is not among them: the plan's entry RECORD is no round of the chain, and nothing
is said on it. What the heads of OnBytes/Slice/PricedRound.lean, OnBytes/Slice/HeldRound.lean,
OnBytes/Params/EntryCoveredRecord.lean and OnBytes/Params/HoldsLaws.lean do not claim. For proofs
only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.EntryFactsRecord
import OnBytes.Slice.PricedRound
import OnBytes.Slice.SmallRecLink

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run OnBytes.Params
open scoped ENNReal

/-! ## The prices -/

/-- The setting has the format's field and the target 128. -/
theorem sr_set : SetOK smallRecordSet :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A sample has one answer. -/
theorem sr_samples : smallRecordSet.samples = 1 := by decide +kernel

/-- The numbers of the 24 rounds of the entry's chain: `smallRecordCounts` but for the first,
written out. -/
noncomputable def srCounts : List ℝ :=
  [linkPointCount smallRecordSet smallRecordTable smallRecordRadius smallRecordRadius,
    2 * seedsShare smallRecordSet (groupList smallRecordG1 65304) 20 1,
    0,
    linkPositionsShare smallRecordTable smallRecordRadius smallRecordRadius 51 51,
    ((19 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ),
    (groupList smallRecordG1 65304 : ℝ) * ((107 - 1 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ),
    (groupList smallRecordG1 65304 : ℝ) / (smallRecordSet.cardE : ℝ),
    foldCount smallRecordSet smallRecordG1 65304 1,
    foldCount smallRecordSet smallRecordG1 65304 2,
    foldCount smallRecordSet smallRecordG1 65304 3,
    foldCount smallRecordSet smallRecordG1 65304 4,
    foldCount smallRecordSet smallRecordG1 65304 5,
    foldCount smallRecordSet smallRecordG1 65304 6,
    seedsShare smallRecordSet (groupList smallRecordG2 10490) 16 smallRecordSet.samples,
    positionsShare smallRecordG1 65304 97 +
      (groupList smallRecordG2 10490 : ℝ) * ((293 - 1 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ),
    (groupList smallRecordG2 10490 : ℝ) / (smallRecordSet.cardE : ℝ),
    foldCount smallRecordSet smallRecordG2 10490 1,
    foldCount smallRecordSet smallRecordG2 10490 2,
    foldCount smallRecordSet smallRecordG2 10490 3,
    foldCount smallRecordSet smallRecordG2 10490 4,
    seedsShare smallRecordSet (groupList smallRecordG3 10490) 12 smallRecordSet.samples,
    positionsShare smallRecordG2 10490 66 +
      (groupList smallRecordG3 10490 : ℝ) * ((200 - 1 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ),
    lastStepCount smallRecordSet smallRecordG3 10490,
    positionsShare smallRecordG3 10490 66]

/-- They are `smallRecordCounts` but for the first. -/
theorem sr_counts (b : ℕ) (x : ℝ) : (smallRecordCounts b x).tail = srCounts := by
  have r1 : List.range' 1 smallRecordG1.k = [1, 2, 3, 4, 5, 6] := rfl
  have r2 : List.range' 1 smallRecordG2.k = [1, 2, 3, 4] := rfl
  simp only [smallRecordCounts, srCounts, foldCounts, switchCounts, r1, r2,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.tail_cons]

/-- The entries of the format's 24 rounds are the written rounds'. -/
theorem sr_entries : srFmt.map (·.entry) =
    [(srRd 0).entry, (srRd 1).entry, (srRd 2).entry, (srRd 3).entry, (srRd 4).entry,
    (srRd 5).entry, (srRd 6).entry, (srRd 7).entry, (srRd 8).entry, (srRd 9).entry,
    (srRd 10).entry, (srRd 11).entry, (srRd 12).entry, (srRd 13).entry, (srRd 14).entry,
    (srRd 15).entry, (srRd 16).entry, (srRd 17).entry, (srRd 18).entry, (srRd 19).entry,
    (srRd 20).entry, (srRd 21).entry, (srRd 22).entry, (srRd 23).entry] := by
  simp only [sr_rd]
  decide +kernel

/-- **Each of the 24 written rounds has its number as a price**: a round of the plan that
`entrySized` returns at `smallRecordLines` has its entry, holds, and has an error of at least that
number. -/
theorem sr_priced : List.Forall₂ (PricedAt smallRecordSet) srCounts (srFmt.map (·.entry)) := by
  obtain ⟨P, hP, hc⟩ := small_record_entry_covered_plan (b := 0) (x := 0) le_rfl (by norm_num)
  cases hF : finishHeld smallRecordSet .once
      (linkPlan ⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩) with
  | error e =>
    have hp := small_record_finish
    rw [hF] at hp
    cases hp
  | ok P' =>
    have hP' := entrySized_of small_record_table small_record_link hF
    have e : P' = P := by
      have h := hP'.symm.trans hP
      simpa using h
    subst e
    have h1 := priced_of_plan (finishHeld_set hF) (finishHeld_holds hF) hc
    obtain ⟨P1, hP1, hp, _⟩ := small_record_sized
    have e1 : P1 = P' := by
      have h := hP1.symm.trans hP
      simpa using h
    subst e1
    have he : P1.rounds.map (·.entry) = smallRecordPlan.entries := congrArg Fmt.Plan.entries hp
    rw [he] at h1
    have h2 := forall₂_tail h1
    have h3 : smallRecordRounds.map (·.1.entry) = srFmt.map (·.entry) := by
      rw [← sr_fmt, List.map_map]
      rfl
    rw [sr_counts, ← record_rounds_entries.2, h3] at h2
    exact h2

/-- The same, with the written rounds' entries written out. -/
theorem sr_pricedL : List.Forall₂ (PricedAt smallRecordSet) srCounts
    [(srRd 0).entry, (srRd 1).entry, (srRd 2).entry, (srRd 3).entry, (srRd 4).entry,
    (srRd 5).entry, (srRd 6).entry, (srRd 7).entry, (srRd 8).entry, (srRd 9).entry,
    (srRd 10).entry, (srRd 11).entry, (srRd 12).entry, (srRd 13).entry, (srRd 14).entry,
    (srRd 15).entry, (srRd 16).entry, (srRd 17).entry, (srRd 18).entry, (srRd 19).entry,
    (srRd 20).entry, (srRd 21).entry, (srRd 22).entry, (srRd 23).entry] := by
  rw [← sr_entries]
  exact sr_priced

/-! The prices of the rounds whose counts are written out, one by one. Of a fold's equal rounds the
first is taken: its number is the largest, by the `if` in the definition of `foldCount`; there is no
theorem on that, and none is needed: the written round is one round, repeated. -/

/-- The price of round 0. -/
theorem sr_price0 :
    PricedAt smallRecordSet
      (linkPointCount smallRecordSet smallRecordTable smallRecordRadius smallRecordRadius)
      (srRd 0).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  exact (List.forall₂_cons.1 h).1

/-- The price of round 1. -/
theorem sr_price1 :
    PricedAt smallRecordSet
      (2 * seedsShare smallRecordSet (groupList smallRecordG1 65304) 20 1)
      (srRd 1).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 1 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 3. -/
theorem sr_price3 :
    PricedAt smallRecordSet
      (linkPositionsShare smallRecordTable smallRecordRadius smallRecordRadius 51 51)
      (srRd 3).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 3 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 4. -/
theorem sr_price4 :
    PricedAt smallRecordSet
      (((19 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ))
      (srRd 4).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 4 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 5. -/
theorem sr_price5 :
    PricedAt smallRecordSet
      ((groupList smallRecordG1 65304 : ℝ) * ((107 - 1 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ))
      (srRd 5).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 5 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 6. -/
theorem sr_price6 :
    PricedAt smallRecordSet
      ((groupList smallRecordG1 65304 : ℝ) / (smallRecordSet.cardE : ℝ))
      (srRd 6).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 6 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 7. -/
theorem sr_price7 :
    PricedAt smallRecordSet
      (foldCount smallRecordSet smallRecordG1 65304 1)
      (srRd 7).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 7 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 13. -/
theorem sr_price13 :
    PricedAt smallRecordSet
      (seedsShare smallRecordSet (groupList smallRecordG2 10490) 16 smallRecordSet.samples)
      (srRd 13).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 13 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 14. -/
theorem sr_price14 :
    PricedAt smallRecordSet
      (positionsShare smallRecordG1 65304 97 +
        (groupList smallRecordG2 10490 : ℝ) * ((293 - 1 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ))
      (srRd 14).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 14 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 15. -/
theorem sr_price15 :
    PricedAt smallRecordSet
      ((groupList smallRecordG2 10490 : ℝ) / (smallRecordSet.cardE : ℝ))
      (srRd 15).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 15 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 16. -/
theorem sr_price16 :
    PricedAt smallRecordSet
      (foldCount smallRecordSet smallRecordG2 10490 1)
      (srRd 16).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 16 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 20. -/
theorem sr_price20 :
    PricedAt smallRecordSet
      (seedsShare smallRecordSet (groupList smallRecordG3 10490) 12 smallRecordSet.samples)
      (srRd 20).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 20 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 21. -/
theorem sr_price21 :
    PricedAt smallRecordSet
      (positionsShare smallRecordG2 10490 66 +
        (groupList smallRecordG3 10490 : ℝ) * ((200 - 1 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ))
      (srRd 21).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 21 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 22. -/
theorem sr_price22 :
    PricedAt smallRecordSet
      (lastStepCount smallRecordSet smallRecordG3 10490)
      (srRd 22).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 22 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 23. -/
theorem sr_price23 :
    PricedAt smallRecordSet
      (positionsShare smallRecordG3 10490 66)
      (srRd 23).entry := by
  have h := sr_pricedL
  unfold srCounts at h
  iterate 23 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-! ## The rounds -/

/-- Each round has positions of at most 64 bits, its elements other than 0 among its elements, and
at most 62 bits of work. -/
theorem sr_ok {i : ℕ} (hi : i < 24) : RoundOK (srRd i) := by
  have h : ((List.range 24).all fun i => decide ((srRt i).entry.logN ≤ 64) &&
      decide ((srRt i).entry.drawNZ ≤ (srRt i).entry.drawE) &&
      decide ((srRt i).entry.work + 66 ≤ 128)) = true := by decide +kernel
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  rw [sr_rd]
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

/-- Those of the rounds that draw one element at which a clause is proved. -/
theorem sr_one {i : ℕ} (hi : i ∈ [5, 6, 7, 15, 16, 22]) :
    nVals (Fmt.dsOf (srRd i).entry (srRd i).kind) = Fintype.card GE := by
  have h : ([5, 6, 7, 15, 16, 22].all fun i =>
      decide (Fmt.dsOf (srRt i).entry (srRt i).kind = [.elem, .trits 0])) = true := by
    decide +kernel
  have h1 := List.all_eq_true.1 h i hi
  rw [sr_rd, of_decide_eq_true h1]
  exact nVals_elem

/-- The link's point: 8 elements. -/
theorem sr_n0 : nVals (Fmt.dsOf (srRd 0).entry (srRd 0).kind) = Fintype.card GE ^ 8 := by
  have h : Fmt.dsOf (srRt 0).entry (srRt 0).kind =
      List.replicate 8 Fmt.Draw.elem ++ [.trits 0] := by decide +kernel
  rw [sr_rd, h]
  exact nVals_elems 8

/-- The seed of the two folded rows' samples: 20 coordinates and a factor. -/
theorem sr_n1 : nVals (Fmt.dsOf (srRd 1).entry (srRd 1).kind) =
    Fintype.card GE ^ 20 * (Fintype.card GE - 1) := by
  have h : Fmt.dsOf (srRt 1).entry (srRt 1).kind =
      List.replicate 20 Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by decide +kernel
  rw [sr_rd, h]
  exact nVals_seed 20

/-- The link's draws: 51 and 51 positions of 23 bits. -/
theorem sr_n3 : nVals (Fmt.dsOf (srRd 3).entry (srRd 3).kind) = (2 ^ 23) ^ (51 + 51) := by
  have h : Fmt.dsOf (srRt 3).entry (srRt 3).kind =
      List.replicate (51 + 51) (Fmt.Draw.pos 23) ++ [.trits 0] := by decide +kernel
  rw [sr_rd, h, nVals_rep, nVals_end, mul_one]

/-- The link's second point: 19 elements. -/
theorem sr_n4 : nVals (Fmt.dsOf (srRd 4).entry (srRd 4).kind) = Fintype.card GE ^ 19 := by
  have h : Fmt.dsOf (srRt 4).entry (srRt 4).kind =
      List.replicate 19 Fmt.Draw.elem ++ [.trits 0] := by decide +kernel
  rw [sr_rd, h]
  exact nVals_elems 19

/-- The seed of the second stage's sample: 16 coordinates and a factor. -/
theorem sr_n13 : nVals (Fmt.dsOf (srRd 13).entry (srRd 13).kind) =
    Fintype.card GE ^ 16 * (Fintype.card GE - 1) := by
  have h : Fmt.dsOf (srRt 13).entry (srRt 13).kind =
      List.replicate 16 Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by decide +kernel
  rw [sr_rd, h]
  exact nVals_seed 16

/-- The code switch from the first stage: 97 positions of 17 bits and one element. -/
theorem sr_n14 : nVals (Fmt.dsOf (srRd 14).entry (srRd 14).kind) =
    (2 ^ 17) ^ 97 * Fintype.card GE := by
  have h : Fmt.dsOf (srRt 14).entry (srRt 14).kind =
      List.replicate 97 (Fmt.Draw.pos 17) ++ [.elem, .trits 0] := by decide +kernel
  rw [sr_rd, h, nVals_rep, nVals_elem_end]

/-- The seed of the third stage's sample: 12 coordinates and a factor. -/
theorem sr_n20 : nVals (Fmt.dsOf (srRd 20).entry (srRd 20).kind) =
    Fintype.card GE ^ 12 * (Fintype.card GE - 1) := by
  have h : Fmt.dsOf (srRt 20).entry (srRt 20).kind =
      List.replicate 12 Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by decide +kernel
  rw [sr_rd, h]
  exact nVals_seed 12

/-- The code switch from the second stage: 66 positions of 14 bits and one element. -/
theorem sr_n21 : nVals (Fmt.dsOf (srRd 21).entry (srRd 21).kind) =
    (2 ^ 14) ^ 66 * Fintype.card GE := by
  have h : Fmt.dsOf (srRt 21).entry (srRt 21).kind =
      List.replicate 66 (Fmt.Draw.pos 14) ++ [.elem, .trits 0] := by decide +kernel
  rw [sr_rd, h, nVals_rep, nVals_elem_end]

/-- The last round: 66 positions of 14 bits. -/
theorem sr_n23 : nVals (Fmt.dsOf (srRd 23).entry (srRd 23).kind) = (2 ^ 14) ^ 66 := by
  have h : Fmt.dsOf (srRt 23).entry (srRt 23).kind =
      List.replicate 66 (Fmt.Draw.pos 14) ++ [.trits 0] := by decide +kernel
  rw [sr_rd, h, nVals_rep, nVals_end, mul_one]

/-! ## Sizes and the planner's table and groups -/

/-- The sizes have the planner's table. -/
theorem sr_asTable : srS.AsTable smallRecordTable :=
  ⟨rfl, by decide, rfl, by decide +kernel, by decide +kernel⟩

/-- The first stage has the planner's first group. -/
theorem sr_as1 : (srS.sg 97).AsGroup smallRecordG1 := by
  have h : srS.sg 97 = srSg1 := sr_sg _ _ _ _
  rw [h]
  exact ⟨srSg1_group, srSg1_sized, srSg1_pos, by decide +kernel, by decide +kernel⟩

/-- The second stage has the planner's second group. -/
theorem sr_as2 : srSg2.AsGroup smallRecordG2 :=
  ⟨srSg2_group, srSg2_sized, srSg2_pos, by decide +kernel, by decide +kernel⟩

/-- The third stage has the planner's third group. -/
theorem sr_as3 : srSg3.AsGroup smallRecordG3 :=
  ⟨srSg3_group, srSg3_sized, srSg3_pos, by decide +kernel, by decide +kernel⟩

/-- The coordinates of the later stages' samples. -/
theorem sr_na : srSg2.st.na = 16 ∧ srSg3.st.na = 12 := by
  decide +kernel

/-- The list of a folded row's oracle message is that of the first group's main code. -/
theorem sr_memb_list :
    listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU =
      groupList smallRecordG1 65304 := by
  rw [sr_link_lists.1]
  unfold groupList listMax
  decide +kernel

/-! ## The counts -/

/-- The link's point. -/
theorem sr_below0 : RoundBelow (srS.lk.errGam (srS.badJ srS.e0) (srS.badJ srS.e1)) (srRd 0)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price0 _ sr_n0 _
    (point_share sr_set sr_asTable rfl rfl rfl)

/-- The seed of the two folded rows' samples. -/
theorem sr_below1 : RoundBelow (ldSendFamErr srS.lk.N srS.seeds fun _ =>
      listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU) (srRd 1)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rw [sr_memb_list]
  exact below_of_priced sr_set (sr_ok (by decide)) sr_price1 _ sr_n1 _
    (send_share sr_set srS (groupList smallRecordG1 65304) (sr_cube _ _ _ _))

/-- The link's draws, with 32 bits of work. -/
theorem sr_below3 : RoundBelow srS.lk.errLoc (srRd 3)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price3 _ sr_n3 _
    (loc_share sr_asTable rfl rfl rfl rfl rfl)

/-- The link's second point. -/
theorem sr_below4 : RoundBelow srS.lk.errPhi (srRd 4)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price4 _ sr_n4 _
    (phi_share sr_set srS (sr_aPhi _ _ _ _))

/-- The batching. -/
theorem sr_below5 : RoundBelow ((srS.sg 97).lstJ 65304 * (107 - 1)) (srRd 5)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price5 _ (sr_one (by decide)) _
    (bat_share_joh sr_set sr_as1 65304 107)

/-- The first round of the first stage's fold. -/
theorem sr_below6 : RoundBelow ((srS.sg 97).lstJ 65304) (srRd 6)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price6 _ (sr_one (by decide)) _
    (eps_share sr_set sr_as1 65304)

/-- A round of the first stage's fold: no mask row is folded. -/
theorem sr_below7 : RoundBelow ((srS.sg 97).flC 65304 + (srS.sg 97).lstJ 65304 * 2) (srRd 7)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price7 _ (sr_one (by decide)) _
    (fold_share sr_set sr_as1 65304 1 (by decide))

/-- The seed of the second stage's sample. -/
theorem sr_below13 : RoundBelow ((csSw (sr_fit12g 6137119 6137119 6137119 65304)).W.err1
      (srSg2.lstJ 10490)) (srRd 13) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := sr_price13
  rw [sr_samples] at h
  exact below_of_priced sr_set (sr_ok (by decide)) h _ sr_n13 _
    (seed_share sr_set sr_as2 _ 10490 sr_na.1)

/-- The code switch from the first stage, with 32 bits of work. -/
theorem sr_below14 : RoundBelow ((csSw (sr_fit12g 6137119 6137119 6137119 65304)).W.err2 65304
      (srSg2.lstJ 10490)) (srRd 14) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price14 _ sr_n14 _
    (cs_share sr_set sr_as1 sr_as2 _ 65304 10490 293 rfl rfl (by decide))

/-- The first round of the second stage's fold. -/
theorem sr_below15 : RoundBelow (srSg2.lstJ 10490) (srRd 15)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price15 _ (sr_one (by decide)) _
    (eps_share sr_set sr_as2 10490)

/-- A round of the second stage's fold in which mask rows are folded too. -/
theorem sr_below16 : RoundBelow (srSg2.flC 10490 + (srSg2.flZ 10490 + srSg2.flZ 10490) +
      srSg2.lstJ 10490 * 2) (srRd 16)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price16 _ (sr_one (by decide)) _
    (fold_share_mask sr_set sr_as2 10490 1 (by decide))

/-- The seed of the third stage's sample. -/
theorem sr_below20 : RoundBelow ((csSw sr_fit23).W.err1
      (srSg3.lstJ 10490)) (srRd 20) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := sr_price20
  rw [sr_samples] at h
  exact below_of_priced sr_set (sr_ok (by decide)) h _ sr_n20 _
    (seed_share sr_set sr_as3 _ 10490 sr_na.2)

/-- The code switch from the second stage, with 32 bits of work. -/
theorem sr_below21 : RoundBelow ((csSw sr_fit23).W.err2 10490
      (srSg3.lstJ 10490)) (srRd 21) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price21 _ sr_n21 _
    (cs_share sr_set sr_as2 sr_as3 _ 10490 10490 200 rfl rfl (by decide))

/-- The last step's first round. -/
theorem sr_below22 : RoundBelow (srSg3.flC 10490 + srSg3.flZ 10490 + srSg3.lstJ 10490) (srRd 22)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price22 _ (sr_one (by decide)) _
    (lambda_share sr_set sr_as3 10490)

/-- The last round, with 32 bits of work. -/
theorem sr_below23 : RoundBelow ((2 ^ srSg3.C.a - 10490 - 1) ^ srSg3.t) (srRd 23)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced sr_set (sr_ok (by decide)) sr_price23 _ sr_n23 _
    (base_share sr_as3 10490 rfl rfl)

/-! ## The chain and the whole list -/

/-- The base case. -/
theorem sr_smallAt3 : srChain3.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Chain.smallAt_lastAt sr_below22 sr_below23

/-- The chain from the second stage on. -/
theorem sr_smallAt2 : srChain2.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Chain.smallAt_stepEndAt sr_fit23 (e' := 10490) rfl sr_below15
    (sr_below16.mono (by omega)) (fun _ => sr_below16)
    sr_below20 sr_below21 sr_smallAt3

/-- **Each count of the chain that is written out is at most 2 ^ -128 as a share of its round's
written verifier messages.** -/
theorem sr_smallAt : srC.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Chain.smallAt_stepMidAt (sr_fit12g 6137119 6137119 6137119 65304) (e' := 10490) rfl sr_below6
    sr_below7 (fun h => absurd rfl h)
    sr_below13 sr_below14 sr_smallAt2

/-- **EVERY COUNT IN THE CONCLUSION OF `sr_link_joh` IS AT MOST 2 ^ -128 AS A SHARE OF ITS ROUND'S
WRITTEN VERIFIER MESSAGES, WORK COUNTED**: at the rounds LINK, CS (twice) and BASE 32 of the
128 bits are work; at the others none. One round's bits: no bound on the chance of a false proof. -/
theorem sr_err_below (xs : List PQ.XO) (dec : PQ.View → Bool) :
    Err.Below (s := (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4)
        (srRd 5 :: srC.rds) xs dec).shape)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  link_chain_below srS srZ srN (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5) xs dec _ _ _
    srC _ (e := 65304) (rows := 107) rfl rfl sr_below0 sr_below1 sr_below3 sr_below4 sr_below5
    (sr_chain_plain _ _ _ _) sr_smallAt

end OnBytes.Slice

#print axioms OnBytes.Slice.sr_set
#print axioms OnBytes.Slice.sr_samples
#print axioms OnBytes.Slice.sr_counts
#print axioms OnBytes.Slice.sr_entries
#print axioms OnBytes.Slice.sr_priced
#print axioms OnBytes.Slice.sr_pricedL
#print axioms OnBytes.Slice.sr_price0
#print axioms OnBytes.Slice.sr_price1
#print axioms OnBytes.Slice.sr_price3
#print axioms OnBytes.Slice.sr_price4
#print axioms OnBytes.Slice.sr_price5
#print axioms OnBytes.Slice.sr_price6
#print axioms OnBytes.Slice.sr_price7
#print axioms OnBytes.Slice.sr_price13
#print axioms OnBytes.Slice.sr_price14
#print axioms OnBytes.Slice.sr_price15
#print axioms OnBytes.Slice.sr_price16
#print axioms OnBytes.Slice.sr_price20
#print axioms OnBytes.Slice.sr_price21
#print axioms OnBytes.Slice.sr_price22
#print axioms OnBytes.Slice.sr_price23
#print axioms OnBytes.Slice.sr_ok
#print axioms OnBytes.Slice.sr_one
#print axioms OnBytes.Slice.sr_n0
#print axioms OnBytes.Slice.sr_n1
#print axioms OnBytes.Slice.sr_n3
#print axioms OnBytes.Slice.sr_n4
#print axioms OnBytes.Slice.sr_n13
#print axioms OnBytes.Slice.sr_n14
#print axioms OnBytes.Slice.sr_n20
#print axioms OnBytes.Slice.sr_n21
#print axioms OnBytes.Slice.sr_n23
#print axioms OnBytes.Slice.sr_asTable
#print axioms OnBytes.Slice.sr_as1
#print axioms OnBytes.Slice.sr_as2
#print axioms OnBytes.Slice.sr_as3
#print axioms OnBytes.Slice.sr_na
#print axioms OnBytes.Slice.sr_memb_list
#print axioms OnBytes.Slice.sr_below0
#print axioms OnBytes.Slice.sr_below1
#print axioms OnBytes.Slice.sr_below3
#print axioms OnBytes.Slice.sr_below4
#print axioms OnBytes.Slice.sr_below5
#print axioms OnBytes.Slice.sr_below6
#print axioms OnBytes.Slice.sr_below7
#print axioms OnBytes.Slice.sr_below13
#print axioms OnBytes.Slice.sr_below14
#print axioms OnBytes.Slice.sr_below15
#print axioms OnBytes.Slice.sr_below16
#print axioms OnBytes.Slice.sr_below20
#print axioms OnBytes.Slice.sr_below21
#print axioms OnBytes.Slice.sr_below22
#print axioms OnBytes.Slice.sr_below23
#print axioms OnBytes.Slice.sr_smallAt3
#print axioms OnBytes.Slice.sr_smallAt2
#print axioms OnBytes.Slice.sr_smallAt
#print axioms OnBytes.Slice.sr_err_below

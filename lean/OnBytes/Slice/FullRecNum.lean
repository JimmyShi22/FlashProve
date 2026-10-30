-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecNum.lean: at the full-size files of the setting "record with work", every error
count in the conclusion of `fr_link_joh` (OnBytes/Slice/FullRecLink.lean) is at most 2 ^ -128 as
a share of its round's written verifier messages, WORK COUNTED.

`fr_link_joh` concludes round-by-round soundness with a list of counts: a 0 in front, then 41: the
link's five, the batching's and the chain's 35. With large counts such a statement is true for free.
This file bounds them. The ground is the planner's yes: the plan that `entrySized` returns at
`recordLines` holds, that is, each round's error, with the planner's term for the distance from
uniform of its draws, is at most 2 ^ (work - 128) (an exact comparison, evaluated in Lean's kernel
in OnBytes/Params/EntryStagesRecord.lean); each number of `recordCounts` is at most its round's
error (OnBytes/Params/EntryCoveredRecord.lean); the plan's entries but the first are the entries of
the 41 written rounds (`record_rounds_entries`, `fr_fmt`). So each written round has its number as a
price (`fr_priced`). Each count of the list is at most its round's number times the number of the
round's typed values (OnBytes/Slice/PricedRound.lean), and `below_of_priced` gives the clause.

Main definitions: `frCounts`.
Main theorems: `fr_counts`, `fr_entries`, `fr_priced`, `fr_smallAt`, **`fr_err_below`**.

WHAT THE 128 BITS ARE. They are one round's: the share of a round's written verifier messages that
are counted as bad. At the rounds 3, 16, 24, 31, 38 and 40 (LINK, the rounds CS, BASE) 32 of the 128
bits are work: a written verifier message holds 32 test bits, of which one setting passes. At the
other rounds no bit is work. Without the work the shares at these rounds are about 2 ^ -97.6,
2 ^ -96.2, 2 ^ -97.6, 2 ^ -97.6, 2 ^ -96.6 and 2 ^ -97.7 (arithmetic outside Lean; no theorem here).
The bound is no bound on the chance of a false proof and not the sum over the rounds. Two entries of
the list are 0 by definition and cost nothing: the first, which stands before the link's rounds, and
that of round 2 (SEND answer), which draws nothing.

Not claimed. THIS IS NO PROOF OF SOUNDNESS: what `fr_link_joh` asks (`Cb.BCHKS46At`; the tie to the
decision) it still asks, and this file says nothing on it. That proof of work is worth its bits. The
counts for exceptional points are the integer parts of `Cb.bchksBound`, the number in the theorem on
codes that is taken as given. The counts are those of every round of the entry's chain (41); the
record's own seed is not among them: the plan's entry RECORD is no round of the chain, and nothing
is said on it. What the heads of OnBytes/Slice/PricedRound.lean, OnBytes/Slice/HeldRound.lean,
OnBytes/Params/EntryCoveredRecord.lean and OnBytes/Params/HoldsLaws.lean do not claim. For proofs
only; the program, that is the Lean text `verify-on-bytes`, does not import this file.

-/
import OnBytes.Params.EntryFactsRecord
import OnBytes.Slice.PricedRound
import OnBytes.Slice.FullRecLink

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run OnBytes.Params
open scoped ENNReal

/-! ## The prices -/

/-- The setting has the format's field and the target 128. -/
theorem fr_set : SetOK recordSet :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A sample has one answer. -/
theorem fr_samples : recordSet.samples = 1 := by decide +kernel

/-- The numbers of the 41 rounds of the entry's chain: `recordCounts` but for the first,
written out. -/
noncomputable def frCounts : List ℝ :=
  [linkPointCount recordSet recordTable recordRadius recordRadius,
    2 * seedsShare recordSet (groupList recordG1 8342420) 29 1,
    0,
    linkPositionsShare recordTable recordRadius recordRadius 62 62,
    ((29 : ℕ) : ℝ) / (recordSet.cardE : ℝ),
    (groupList recordG1 8342420 : ℝ) * ((129 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ),
    (groupList recordG1 8342420 : ℝ) / (recordSet.cardE : ℝ),
    foldCount recordSet recordG1 8342420 1,
    foldCount recordSet recordG1 8342420 2,
    foldCount recordSet recordG1 8342420 3,
    foldCount recordSet recordG1 8342420 4,
    foldCount recordSet recordG1 8342420 5,
    foldCount recordSet recordG1 8342420 6,
    foldCount recordSet recordG1 8342420 7,
    foldCount recordSet recordG1 8342420 8,
    seedsShare recordSet (groupList recordG2 1569886) 23 recordSet.samples,
    positionsShare recordG1 8342420 97 +
      (groupList recordG2 1569886 : ℝ) * ((293 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ),
    (groupList recordG2 1569886 : ℝ) / (recordSet.cardE : ℝ),
    foldCount recordSet recordG2 1569886 1,
    foldCount recordSet recordG2 1569886 2,
    foldCount recordSet recordG2 1569886 3,
    foldCount recordSet recordG2 1569886 4,
    foldCount recordSet recordG2 1569886 5,
    seedsShare recordSet (groupList recordG3 98104) 18 recordSet.samples,
    positionsShare recordG2 1569886 49 +
      (groupList recordG3 98104 : ℝ) * ((149 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ),
    (groupList recordG3 98104 : ℝ) / (recordSet.cardE : ℝ),
    foldCount recordSet recordG3 98104 1,
    foldCount recordSet recordG3 98104 2,
    foldCount recordSet recordG3 98104 3,
    foldCount recordSet recordG3 98104 4,
    seedsShare recordSet (groupList recordG4 6044) 14 recordSet.samples,
    positionsShare recordG3 98104 49 +
      (groupList recordG4 6044 : ℝ) * ((149 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ),
    (groupList recordG4 6044 : ℝ) / (recordSet.cardE : ℝ),
    foldCount recordSet recordG4 6044 1,
    foldCount recordSet recordG4 6044 2,
    foldCount recordSet recordG4 6044 3,
    foldCount recordSet recordG4 6044 4,
    seedsShare recordSet (groupList recordG5 13370) 10 recordSet.samples,
    positionsShare recordG4 6044 50 +
      (groupList recordG5 13370 : ℝ) * ((152 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ),
    lastStepCount recordSet recordG5 13370,
    positionsShare recordG5 13370 40]

/-- They are `recordCounts` but for the first. -/
theorem fr_counts (b : ℕ) (x : ℝ) : (recordCounts b x).tail = frCounts := by
  have r1 : List.range' 1 recordG1.k = [1, 2, 3, 4, 5, 6, 7, 8] := rfl
  have r2 : List.range' 1 recordG2.k = [1, 2, 3, 4, 5] := rfl
  have r3 : List.range' 1 recordG3.k = [1, 2, 3, 4] := rfl
  have r4 : List.range' 1 recordG4.k = [1, 2, 3, 4] := rfl
  simp only [recordCounts, frCounts, foldCounts, switchCounts, r1, r2, r3, r4,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.tail_cons]

/-- The entries of the format's 41 rounds are the written rounds'. -/
theorem fr_entries : frFmt.map (·.entry) =
    [(frRd 0).entry, (frRd 1).entry, (frRd 2).entry, (frRd 3).entry, (frRd 4).entry,
    (frRd 5).entry, (frRd 6).entry, (frRd 7).entry, (frRd 8).entry, (frRd 9).entry,
    (frRd 10).entry, (frRd 11).entry, (frRd 12).entry, (frRd 13).entry, (frRd 14).entry,
    (frRd 15).entry, (frRd 16).entry, (frRd 17).entry, (frRd 18).entry, (frRd 19).entry,
    (frRd 20).entry, (frRd 21).entry, (frRd 22).entry, (frRd 23).entry, (frRd 24).entry,
    (frRd 25).entry, (frRd 26).entry, (frRd 27).entry, (frRd 28).entry, (frRd 29).entry,
    (frRd 30).entry, (frRd 31).entry, (frRd 32).entry, (frRd 33).entry, (frRd 34).entry,
    (frRd 35).entry, (frRd 36).entry, (frRd 37).entry, (frRd 38).entry, (frRd 39).entry,
    (frRd 40).entry] := by
  simp only [fr_rd]
  decide +kernel

/-- **Each of the 41 written rounds has its number as a price**: a round of the plan that
`entrySized` returns at `recordLines` has its entry, holds, and has an error of at least that
number. -/
theorem fr_priced : List.Forall₂ (PricedAt recordSet) frCounts (frFmt.map (·.entry)) := by
  obtain ⟨P, hP, hc⟩ := record_entry_covered_plan (b := 0) (x := 0) le_rfl (by norm_num)
  cases hF : finishHeld recordSet .once
      (linkPlan ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩) with
  | error e =>
    have hp := record_finish
    rw [hF] at hp
    cases hp
  | ok P' =>
    have hP' := entrySized_of record_table record_link hF
    have e : P' = P := by
      have h := hP'.symm.trans hP
      simpa using h
    subst e
    have h1 := priced_of_plan (finishHeld_set hF) (finishHeld_holds hF) hc
    obtain ⟨P1, hP1, hp, _⟩ := record_sized
    have e1 : P1 = P' := by
      have h := hP1.symm.trans hP
      simpa using h
    subst e1
    have he : P1.rounds.map (·.entry) = recordPlan.entries := congrArg Fmt.Plan.entries hp
    rw [he] at h1
    have h2 := forall₂_tail h1
    have h3 : recordRounds.map (·.1.entry) = frFmt.map (·.entry) := by
      rw [← fr_fmt, List.map_map]
      rfl
    rw [fr_counts, ← record_rounds_entries.1, h3] at h2
    exact h2

/-- The same, with the written rounds' entries written out. -/
theorem fr_pricedL : List.Forall₂ (PricedAt recordSet) frCounts
    [(frRd 0).entry, (frRd 1).entry, (frRd 2).entry, (frRd 3).entry, (frRd 4).entry,
    (frRd 5).entry, (frRd 6).entry, (frRd 7).entry, (frRd 8).entry, (frRd 9).entry,
    (frRd 10).entry, (frRd 11).entry, (frRd 12).entry, (frRd 13).entry, (frRd 14).entry,
    (frRd 15).entry, (frRd 16).entry, (frRd 17).entry, (frRd 18).entry, (frRd 19).entry,
    (frRd 20).entry, (frRd 21).entry, (frRd 22).entry, (frRd 23).entry, (frRd 24).entry,
    (frRd 25).entry, (frRd 26).entry, (frRd 27).entry, (frRd 28).entry, (frRd 29).entry,
    (frRd 30).entry, (frRd 31).entry, (frRd 32).entry, (frRd 33).entry, (frRd 34).entry,
    (frRd 35).entry, (frRd 36).entry, (frRd 37).entry, (frRd 38).entry, (frRd 39).entry,
    (frRd 40).entry] := by
  rw [← fr_entries]
  exact fr_priced

/-! The prices of the rounds whose counts are written out, one by one. Of a fold's equal rounds the
first is taken: its number is the largest, by the `if` in the definition of `foldCount`; there is no
theorem on that, and none is needed: the written round is one round, repeated. -/

/-- The price of round 0. -/
theorem fr_price0 :
    PricedAt recordSet
      (linkPointCount recordSet recordTable recordRadius recordRadius)
      (frRd 0).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  exact (List.forall₂_cons.1 h).1

/-- The price of round 1. -/
theorem fr_price1 :
    PricedAt recordSet
      (2 * seedsShare recordSet (groupList recordG1 8342420) 29 1)
      (frRd 1).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 1 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 3. -/
theorem fr_price3 :
    PricedAt recordSet
      (linkPositionsShare recordTable recordRadius recordRadius 62 62)
      (frRd 3).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 3 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 4. -/
theorem fr_price4 :
    PricedAt recordSet
      (((29 : ℕ) : ℝ) / (recordSet.cardE : ℝ))
      (frRd 4).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 4 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 5. -/
theorem fr_price5 :
    PricedAt recordSet
      ((groupList recordG1 8342420 : ℝ) * ((129 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ))
      (frRd 5).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 5 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 6. -/
theorem fr_price6 :
    PricedAt recordSet
      ((groupList recordG1 8342420 : ℝ) / (recordSet.cardE : ℝ))
      (frRd 6).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 6 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 7. -/
theorem fr_price7 :
    PricedAt recordSet
      (foldCount recordSet recordG1 8342420 1)
      (frRd 7).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 7 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 15. -/
theorem fr_price15 :
    PricedAt recordSet
      (seedsShare recordSet (groupList recordG2 1569886) 23 recordSet.samples)
      (frRd 15).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 15 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 16. -/
theorem fr_price16 :
    PricedAt recordSet
      (positionsShare recordG1 8342420 97 +
        (groupList recordG2 1569886 : ℝ) * ((293 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ))
      (frRd 16).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 16 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 17. -/
theorem fr_price17 :
    PricedAt recordSet
      ((groupList recordG2 1569886 : ℝ) / (recordSet.cardE : ℝ))
      (frRd 17).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 17 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 18. -/
theorem fr_price18 :
    PricedAt recordSet
      (foldCount recordSet recordG2 1569886 1)
      (frRd 18).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 18 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 23. -/
theorem fr_price23 :
    PricedAt recordSet
      (seedsShare recordSet (groupList recordG3 98104) 18 recordSet.samples)
      (frRd 23).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 23 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 24. -/
theorem fr_price24 :
    PricedAt recordSet
      (positionsShare recordG2 1569886 49 +
        (groupList recordG3 98104 : ℝ) * ((149 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ))
      (frRd 24).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 24 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 25. -/
theorem fr_price25 :
    PricedAt recordSet
      ((groupList recordG3 98104 : ℝ) / (recordSet.cardE : ℝ))
      (frRd 25).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 25 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 26. -/
theorem fr_price26 :
    PricedAt recordSet
      (foldCount recordSet recordG3 98104 1)
      (frRd 26).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 26 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 30. -/
theorem fr_price30 :
    PricedAt recordSet
      (seedsShare recordSet (groupList recordG4 6044) 14 recordSet.samples)
      (frRd 30).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 30 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 31. -/
theorem fr_price31 :
    PricedAt recordSet
      (positionsShare recordG3 98104 49 +
        (groupList recordG4 6044 : ℝ) * ((149 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ))
      (frRd 31).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 31 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 32. -/
theorem fr_price32 :
    PricedAt recordSet
      ((groupList recordG4 6044 : ℝ) / (recordSet.cardE : ℝ))
      (frRd 32).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 32 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 33. -/
theorem fr_price33 :
    PricedAt recordSet
      (foldCount recordSet recordG4 6044 1)
      (frRd 33).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 33 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 37. -/
theorem fr_price37 :
    PricedAt recordSet
      (seedsShare recordSet (groupList recordG5 13370) 10 recordSet.samples)
      (frRd 37).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 37 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 38. -/
theorem fr_price38 :
    PricedAt recordSet
      (positionsShare recordG4 6044 50 +
        (groupList recordG5 13370 : ℝ) * ((152 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ))
      (frRd 38).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 38 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 39. -/
theorem fr_price39 :
    PricedAt recordSet
      (lastStepCount recordSet recordG5 13370)
      (frRd 39).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 39 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-- The price of round 40. -/
theorem fr_price40 :
    PricedAt recordSet
      (positionsShare recordG5 13370 40)
      (frRd 40).entry := by
  have h := fr_pricedL
  unfold frCounts at h
  iterate 40 replace h := (List.forall₂_cons.1 h).2
  exact (List.forall₂_cons.1 h).1

/-! ## The rounds -/

/-- Each round has positions of at most 64 bits, its elements other than 0 among its elements, and
at most 62 bits of work. -/
theorem fr_ok {i : ℕ} (hi : i < 41) : RoundOK (frRd i) := by
  have h : ((List.range 41).all fun i => decide ((frRt i).entry.logN ≤ 64) &&
      decide ((frRt i).entry.drawNZ ≤ (frRt i).entry.drawE) &&
      decide ((frRt i).entry.work + 66 ≤ 128)) = true := by decide +kernel
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  rw [fr_rd]
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

/-- Those of the rounds that draw one element at which a clause is proved. -/
theorem fr_one {i : ℕ} (hi : i ∈ [5, 6, 7, 17, 18, 25, 26, 32, 33, 39]) :
    nVals (Fmt.dsOf (frRd i).entry (frRd i).kind) = Fintype.card GE := by
  have h : ([5, 6, 7, 17, 18, 25, 26, 32, 33, 39].all fun i =>
      decide (Fmt.dsOf (frRt i).entry (frRt i).kind = [.elem, .trits 0])) = true := by
    decide +kernel
  have h1 := List.all_eq_true.1 h i hi
  rw [fr_rd, of_decide_eq_true h1]
  exact nVals_elem

/-- The link's point: 11 elements. -/
theorem fr_n0 : nVals (Fmt.dsOf (frRd 0).entry (frRd 0).kind) = Fintype.card GE ^ 11 := by
  have h : Fmt.dsOf (frRt 0).entry (frRt 0).kind =
      List.replicate 11 Fmt.Draw.elem ++ [.trits 0] := by decide +kernel
  rw [fr_rd, h]
  exact nVals_elems 11

/-- The seed of the two folded rows' samples: 29 coordinates and a factor. -/
theorem fr_n1 : nVals (Fmt.dsOf (frRd 1).entry (frRd 1).kind) =
    Fintype.card GE ^ 29 * (Fintype.card GE - 1) := by
  have h : Fmt.dsOf (frRt 1).entry (frRt 1).kind =
      List.replicate 29 Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by decide +kernel
  rw [fr_rd, h]
  exact nVals_seed 29

/-- The link's draws: 62 and 62 positions of 32 bits. -/
theorem fr_n3 : nVals (Fmt.dsOf (frRd 3).entry (frRd 3).kind) = (2 ^ 32) ^ (62 + 62) := by
  have h : Fmt.dsOf (frRt 3).entry (frRt 3).kind =
      List.replicate (62 + 62) (Fmt.Draw.pos 32) ++ [.trits 0] := by decide +kernel
  rw [fr_rd, h, nVals_rep, nVals_end, mul_one]

/-- The link's second point: 29 elements. -/
theorem fr_n4 : nVals (Fmt.dsOf (frRd 4).entry (frRd 4).kind) = Fintype.card GE ^ 29 := by
  have h : Fmt.dsOf (frRt 4).entry (frRt 4).kind =
      List.replicate 29 Fmt.Draw.elem ++ [.trits 0] := by decide +kernel
  rw [fr_rd, h]
  exact nVals_elems 29

/-- The seed of the second stage's sample: 23 coordinates and a factor. -/
theorem fr_n15 : nVals (Fmt.dsOf (frRd 15).entry (frRd 15).kind) =
    Fintype.card GE ^ 23 * (Fintype.card GE - 1) := by
  have h : Fmt.dsOf (frRt 15).entry (frRt 15).kind =
      List.replicate 23 Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by decide +kernel
  rw [fr_rd, h]
  exact nVals_seed 23

/-- The code switch from the first stage: 97 positions of 24 bits and one element. -/
theorem fr_n16 : nVals (Fmt.dsOf (frRd 16).entry (frRd 16).kind) =
    (2 ^ 24) ^ 97 * Fintype.card GE := by
  have h : Fmt.dsOf (frRt 16).entry (frRt 16).kind =
      List.replicate 97 (Fmt.Draw.pos 24) ++ [.elem, .trits 0] := by decide +kernel
  rw [fr_rd, h, nVals_rep, nVals_elem_end]

/-- The seed of the third stage's sample: 18 coordinates and a factor. -/
theorem fr_n23 : nVals (Fmt.dsOf (frRd 23).entry (frRd 23).kind) =
    Fintype.card GE ^ 18 * (Fintype.card GE - 1) := by
  have h : Fmt.dsOf (frRt 23).entry (frRt 23).kind =
      List.replicate 18 Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by decide +kernel
  rw [fr_rd, h]
  exact nVals_seed 18

/-- The code switch from the second stage: 49 positions of 21 bits and one element. -/
theorem fr_n24 : nVals (Fmt.dsOf (frRd 24).entry (frRd 24).kind) =
    (2 ^ 21) ^ 49 * Fintype.card GE := by
  have h : Fmt.dsOf (frRt 24).entry (frRt 24).kind =
      List.replicate 49 (Fmt.Draw.pos 21) ++ [.elem, .trits 0] := by decide +kernel
  rw [fr_rd, h, nVals_rep, nVals_elem_end]

/-- The seed of the fourth stage's sample: 14 coordinates and a factor. -/
theorem fr_n30 : nVals (Fmt.dsOf (frRd 30).entry (frRd 30).kind) =
    Fintype.card GE ^ 14 * (Fintype.card GE - 1) := by
  have h : Fmt.dsOf (frRt 30).entry (frRt 30).kind =
      List.replicate 14 Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by decide +kernel
  rw [fr_rd, h]
  exact nVals_seed 14

/-- The code switch from the third stage: 49 positions of 17 bits and one element. -/
theorem fr_n31 : nVals (Fmt.dsOf (frRd 31).entry (frRd 31).kind) =
    (2 ^ 17) ^ 49 * Fintype.card GE := by
  have h : Fmt.dsOf (frRt 31).entry (frRt 31).kind =
      List.replicate 49 (Fmt.Draw.pos 17) ++ [.elem, .trits 0] := by decide +kernel
  rw [fr_rd, h, nVals_rep, nVals_elem_end]

/-- The seed of the fifth stage's sample: 10 coordinates and a factor. -/
theorem fr_n37 : nVals (Fmt.dsOf (frRd 37).entry (frRd 37).kind) =
    Fintype.card GE ^ 10 * (Fintype.card GE - 1) := by
  have h : Fmt.dsOf (frRt 37).entry (frRt 37).kind =
      List.replicate 10 Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by decide +kernel
  rw [fr_rd, h]
  exact nVals_seed 10

/-- The code switch from the fourth stage: 50 positions of 13 bits and one element. -/
theorem fr_n38 : nVals (Fmt.dsOf (frRd 38).entry (frRd 38).kind) =
    (2 ^ 13) ^ 50 * Fintype.card GE := by
  have h : Fmt.dsOf (frRt 38).entry (frRt 38).kind =
      List.replicate 50 (Fmt.Draw.pos 13) ++ [.elem, .trits 0] := by decide +kernel
  rw [fr_rd, h, nVals_rep, nVals_elem_end]

/-- The last round: 40 positions of 14 bits. -/
theorem fr_n40 : nVals (Fmt.dsOf (frRd 40).entry (frRd 40).kind) = (2 ^ 14) ^ 40 := by
  have h : Fmt.dsOf (frRt 40).entry (frRt 40).kind =
      List.replicate 40 (Fmt.Draw.pos 14) ++ [.trits 0] := by decide +kernel
  rw [fr_rd, h, nVals_rep, nVals_end, mul_one]

/-! ## Sizes and the planner's table and groups -/

/-- The sizes have the planner's table. -/
theorem fr_asTable : frS.AsTable recordTable :=
  ⟨rfl, by decide, rfl, by decide +kernel, by decide +kernel⟩

/-- The first stage has the planner's first group. -/
theorem fr_as1 : (frS.sg 97).AsGroup recordG1 := by
  have h : frS.sg 97 = frSg1 := fr_sg _ _ _ _
  rw [h]
  exact ⟨frSg1_group, frSg1_sized, frSg1_pos, by decide +kernel, by decide +kernel⟩

/-- The second stage has the planner's second group. -/
theorem fr_as2 : frSg2.AsGroup recordG2 :=
  ⟨frSg2_group, frSg2_sized, frSg2_pos, by decide +kernel, by decide +kernel⟩

/-- The third stage has the planner's third group. -/
theorem fr_as3 : frSg3.AsGroup recordG3 :=
  ⟨frSg3_group, frSg3_sized, frSg3_pos, by decide +kernel, by decide +kernel⟩

/-- The fourth stage has the planner's fourth group. -/
theorem fr_as4 : frSg4.AsGroup recordG4 :=
  ⟨frSg4_group, frSg4_sized, frSg4_pos, by decide +kernel, by decide +kernel⟩

/-- The fifth stage has the planner's fifth group. -/
theorem fr_as5 : frSg5.AsGroup recordG5 :=
  ⟨frSg5_group, frSg5_sized, frSg5_pos, by decide +kernel, by decide +kernel⟩

/-- The coordinates of the later stages' samples. -/
theorem fr_na : frSg2.st.na = 23 ∧ frSg3.st.na = 18 ∧ frSg4.st.na = 14 ∧ frSg5.st.na = 10 := by
  decide +kernel

/-- The list of a folded row's oracle message is that of the first group's main code. -/
theorem fr_memb_list :
    listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU =
      groupList recordG1 8342420 := by
  rw [fr_link_lists.1]
  unfold groupList listMax
  decide +kernel

/-! ## The counts -/

/-- The link's point. -/
theorem fr_below0 : RoundBelow (frS.lk.errGam (frS.badJ frS.e0) (frS.badJ frS.e1)) (frRd 0)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price0 _ fr_n0 _
    (point_share fr_set fr_asTable rfl rfl rfl)

/-- The seed of the two folded rows' samples. -/
theorem fr_below1 : RoundBelow (ldSendFamErr frS.lk.N frS.seeds fun _ =>
      listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU) (frRd 1)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rw [fr_memb_list]
  exact below_of_priced fr_set (fr_ok (by decide)) fr_price1 _ fr_n1 _
    (send_share fr_set frS (groupList recordG1 8342420) (fr_cube _ _ _ _))

/-- The link's draws, with 32 bits of work. -/
theorem fr_below3 : RoundBelow frS.lk.errLoc (frRd 3)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price3 _ fr_n3 _
    (loc_share fr_asTable rfl rfl rfl rfl rfl)

/-- The link's second point. -/
theorem fr_below4 : RoundBelow frS.lk.errPhi (frRd 4)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price4 _ fr_n4 _
    (phi_share fr_set frS (fr_aPhi _ _ _ _))

/-- The batching. -/
theorem fr_below5 : RoundBelow ((frS.sg 97).lstJ 8342420 * (129 - 1)) (frRd 5)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price5 _ (fr_one (by decide)) _
    (bat_share_joh fr_set fr_as1 8342420 129)

/-- The first round of the first stage's fold. -/
theorem fr_below6 : RoundBelow ((frS.sg 97).lstJ 8342420) (frRd 6)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price6 _ (fr_one (by decide)) _
    (eps_share fr_set fr_as1 8342420)

/-- A round of the first stage's fold: no mask row is folded. -/
theorem fr_below7 : RoundBelow ((frS.sg 97).flC 8342420 + (frS.sg 97).lstJ 8342420 * 2) (frRd 7)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price7 _ (fr_one (by decide)) _
    (fold_share fr_set fr_as1 8342420 1 (by decide))

/-- The seed of the second stage's sample. -/
theorem fr_below15 : RoundBelow ((csSw (fr_fit12g 2852142980 2852142980 2852142980 8342420)).W.err1
      (frSg2.lstJ 1569886)) (frRd 15) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := fr_price15
  rw [fr_samples] at h
  exact below_of_priced fr_set (fr_ok (by decide)) h _ fr_n15 _
    (seed_share fr_set fr_as2 _ 1569886 fr_na.1)

/-- The code switch from the first stage, with 32 bits of work. -/
theorem fr_below16 : RoundBelow
    ((csSw (fr_fit12g 2852142980 2852142980 2852142980 8342420)).W.err2 8342420
      (frSg2.lstJ 1569886)) (frRd 16) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price16 _ fr_n16 _
    (cs_share fr_set fr_as1 fr_as2 _ 8342420 1569886 293 rfl rfl (by decide))

/-- The first round of the second stage's fold. -/
theorem fr_below17 : RoundBelow (frSg2.lstJ 1569886) (frRd 17)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price17 _ (fr_one (by decide)) _
    (eps_share fr_set fr_as2 1569886)

/-- A round of the second stage's fold in which mask rows are folded too. -/
theorem fr_below18 : RoundBelow (frSg2.flC 1569886 + (frSg2.flZ 1569886 + frSg2.flZ 1569886) +
      frSg2.lstJ 1569886 * 2) (frRd 18)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price18 _ (fr_one (by decide)) _
    (fold_share_mask fr_set fr_as2 1569886 1 (by decide))

/-- The seed of the third stage's sample. -/
theorem fr_below23 : RoundBelow ((csSw fr_fit23).W.err1
      (frSg3.lstJ 98104)) (frRd 23) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := fr_price23
  rw [fr_samples] at h
  exact below_of_priced fr_set (fr_ok (by decide)) h _ fr_n23 _
    (seed_share fr_set fr_as3 _ 98104 fr_na.2.1)

/-- The code switch from the second stage, with 32 bits of work. -/
theorem fr_below24 : RoundBelow ((csSw fr_fit23).W.err2 1569886
      (frSg3.lstJ 98104)) (frRd 24) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price24 _ fr_n24 _
    (cs_share fr_set fr_as2 fr_as3 _ 1569886 98104 149 rfl rfl (by decide))

/-- The first round of the third stage's fold. -/
theorem fr_below25 : RoundBelow (frSg3.lstJ 98104) (frRd 25)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price25 _ (fr_one (by decide)) _
    (eps_share fr_set fr_as3 98104)

/-- A round of the third stage's fold in which mask rows are folded too. -/
theorem fr_below26 : RoundBelow (frSg3.flC 98104 + (frSg3.flZ 98104 + frSg3.flZ 98104) +
      frSg3.lstJ 98104 * 2) (frRd 26)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price26 _ (fr_one (by decide)) _
    (fold_share_mask fr_set fr_as3 98104 1 (by decide))

/-- The seed of the fourth stage's sample. -/
theorem fr_below30 : RoundBelow ((csSw fr_fit34).W.err1
      (frSg4.lstJ 6044)) (frRd 30) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := fr_price30
  rw [fr_samples] at h
  exact below_of_priced fr_set (fr_ok (by decide)) h _ fr_n30 _
    (seed_share fr_set fr_as4 _ 6044 fr_na.2.2.1)

/-- The code switch from the third stage, with 32 bits of work. -/
theorem fr_below31 : RoundBelow ((csSw fr_fit34).W.err2 98104
      (frSg4.lstJ 6044)) (frRd 31) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price31 _ fr_n31 _
    (cs_share fr_set fr_as3 fr_as4 _ 98104 6044 149 rfl rfl (by decide))

/-- The first round of the fourth stage's fold. -/
theorem fr_below32 : RoundBelow (frSg4.lstJ 6044) (frRd 32)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price32 _ (fr_one (by decide)) _
    (eps_share fr_set fr_as4 6044)

/-- A round of the fourth stage's fold in which mask rows are folded too. -/
theorem fr_below33 : RoundBelow (frSg4.flC 6044 + (frSg4.flZ 6044 + frSg4.flZ 6044) +
      frSg4.lstJ 6044 * 2) (frRd 33)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price33 _ (fr_one (by decide)) _
    (fold_share_mask fr_set fr_as4 6044 1 (by decide))

/-- The seed of the fifth stage's sample. -/
theorem fr_below37 : RoundBelow ((csSw fr_fit45).W.err1
      (frSg5.lstJ 13370)) (frRd 37) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := fr_price37
  rw [fr_samples] at h
  exact below_of_priced fr_set (fr_ok (by decide)) h _ fr_n37 _
    (seed_share fr_set fr_as5 _ 13370 fr_na.2.2.2)

/-- The code switch from the fourth stage, with 32 bits of work. -/
theorem fr_below38 : RoundBelow ((csSw fr_fit45).W.err2 6044
      (frSg5.lstJ 13370)) (frRd 38) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price38 _ fr_n38 _
    (cs_share fr_set fr_as4 fr_as5 _ 6044 13370 152 rfl rfl (by decide))

/-- The last step's first round. -/
theorem fr_below39 : RoundBelow (frSg5.flC 13370 + frSg5.flZ 13370 + frSg5.lstJ 13370) (frRd 39)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price39 _ (fr_one (by decide)) _
    (lambda_share fr_set fr_as5 13370)

/-- The last round, with 32 bits of work. -/
theorem fr_below40 : RoundBelow ((2 ^ frSg5.C.a - 13370 - 1) ^ frSg5.t) (frRd 40)
    ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_of_priced fr_set (fr_ok (by decide)) fr_price40 _ fr_n40 _
    (base_share fr_as5 13370 rfl rfl)

/-! ## The chain and the whole list -/

/-- The base case. -/
theorem fr_smallAt5 : frChain5.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Chain.smallAt_lastAt fr_below39 fr_below40

/-- The chain from the fourth stage on. -/
theorem fr_smallAt4 : frChain4.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Chain.smallAt_stepEndAt fr_fit45 (e' := 13370) rfl fr_below32
    (fr_below33.mono (by omega)) (fun _ => fr_below33)
    fr_below37 fr_below38 fr_smallAt5

/-- The chain from the third stage on. -/
theorem fr_smallAt3 : frChain3.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Chain.smallAt_stepMidAt fr_fit34 (e' := 6044) rfl fr_below25
    (fr_below26.mono (by omega)) (fun _ => fr_below26)
    fr_below30 fr_below31 fr_smallAt4

/-- The chain from the second stage on. -/
theorem fr_smallAt2 : frChain2.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Chain.smallAt_stepMidAt fr_fit23 (e' := 98104) rfl fr_below17
    (fr_below18.mono (by omega)) (fun _ => fr_below18)
    fr_below23 fr_below24 fr_smallAt3

/-- **Each count of the chain that is written out is at most 2 ^ -128 as a share of its round's
written verifier messages.** -/
theorem fr_smallAt : frC.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Chain.smallAt_stepMidAt (fr_fit12g 2852142980 2852142980 2852142980 8342420) (e' := 1569886)
    rfl fr_below6 fr_below7 (fun h => absurd rfl h)
    fr_below15 fr_below16 fr_smallAt2

/-- **EVERY COUNT IN THE CONCLUSION OF `fr_link_joh` IS AT MOST 2 ^ -128 AS A SHARE OF ITS ROUND'S
WRITTEN VERIFIER MESSAGES, WORK COUNTED**: at the rounds LINK, CS (four times) and BASE 32 of the
128 bits are work; at the others none. One round's bits: no bound on the chance of a false proof. -/
theorem fr_err_below (xs : List PQ.XO) (dec : PQ.View → Bool) :
    Err.Below (s := (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4)
        (frRd 5 :: frC.rds) xs dec).shape)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  link_chain_below frS frZ frN (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5) xs dec _ _ _
    frC _ (e := 8342420) (rows := 129) rfl rfl fr_below0 fr_below1 fr_below3 fr_below4 fr_below5
    (fr_chain_plain _ _ _ _) fr_smallAt

end OnBytes.Slice

#print axioms OnBytes.Slice.fr_set
#print axioms OnBytes.Slice.fr_samples
#print axioms OnBytes.Slice.fr_counts
#print axioms OnBytes.Slice.fr_entries
#print axioms OnBytes.Slice.fr_priced
#print axioms OnBytes.Slice.fr_pricedL
#print axioms OnBytes.Slice.fr_price0
#print axioms OnBytes.Slice.fr_price1
#print axioms OnBytes.Slice.fr_price3
#print axioms OnBytes.Slice.fr_price4
#print axioms OnBytes.Slice.fr_price5
#print axioms OnBytes.Slice.fr_price6
#print axioms OnBytes.Slice.fr_price7
#print axioms OnBytes.Slice.fr_price15
#print axioms OnBytes.Slice.fr_price16
#print axioms OnBytes.Slice.fr_price17
#print axioms OnBytes.Slice.fr_price18
#print axioms OnBytes.Slice.fr_price23
#print axioms OnBytes.Slice.fr_price24
#print axioms OnBytes.Slice.fr_price25
#print axioms OnBytes.Slice.fr_price26
#print axioms OnBytes.Slice.fr_price30
#print axioms OnBytes.Slice.fr_price31
#print axioms OnBytes.Slice.fr_price32
#print axioms OnBytes.Slice.fr_price33
#print axioms OnBytes.Slice.fr_price37
#print axioms OnBytes.Slice.fr_price38
#print axioms OnBytes.Slice.fr_price39
#print axioms OnBytes.Slice.fr_price40
#print axioms OnBytes.Slice.fr_ok
#print axioms OnBytes.Slice.fr_one
#print axioms OnBytes.Slice.fr_n0
#print axioms OnBytes.Slice.fr_n1
#print axioms OnBytes.Slice.fr_n3
#print axioms OnBytes.Slice.fr_n4
#print axioms OnBytes.Slice.fr_n15
#print axioms OnBytes.Slice.fr_n16
#print axioms OnBytes.Slice.fr_n23
#print axioms OnBytes.Slice.fr_n24
#print axioms OnBytes.Slice.fr_n30
#print axioms OnBytes.Slice.fr_n31
#print axioms OnBytes.Slice.fr_n37
#print axioms OnBytes.Slice.fr_n38
#print axioms OnBytes.Slice.fr_n40
#print axioms OnBytes.Slice.fr_asTable
#print axioms OnBytes.Slice.fr_as1
#print axioms OnBytes.Slice.fr_as2
#print axioms OnBytes.Slice.fr_as3
#print axioms OnBytes.Slice.fr_as4
#print axioms OnBytes.Slice.fr_as5
#print axioms OnBytes.Slice.fr_na
#print axioms OnBytes.Slice.fr_memb_list
#print axioms OnBytes.Slice.fr_below0
#print axioms OnBytes.Slice.fr_below1
#print axioms OnBytes.Slice.fr_below3
#print axioms OnBytes.Slice.fr_below4
#print axioms OnBytes.Slice.fr_below5
#print axioms OnBytes.Slice.fr_below6
#print axioms OnBytes.Slice.fr_below7
#print axioms OnBytes.Slice.fr_below15
#print axioms OnBytes.Slice.fr_below16
#print axioms OnBytes.Slice.fr_below17
#print axioms OnBytes.Slice.fr_below18
#print axioms OnBytes.Slice.fr_below23
#print axioms OnBytes.Slice.fr_below24
#print axioms OnBytes.Slice.fr_below25
#print axioms OnBytes.Slice.fr_below26
#print axioms OnBytes.Slice.fr_below30
#print axioms OnBytes.Slice.fr_below31
#print axioms OnBytes.Slice.fr_below32
#print axioms OnBytes.Slice.fr_below33
#print axioms OnBytes.Slice.fr_below37
#print axioms OnBytes.Slice.fr_below38
#print axioms OnBytes.Slice.fr_below39
#print axioms OnBytes.Slice.fr_below40
#print axioms OnBytes.Slice.fr_smallAt5
#print axioms OnBytes.Slice.fr_smallAt4
#print axioms OnBytes.Slice.fr_smallAt3
#print axioms OnBytes.Slice.fr_smallAt2
#print axioms OnBytes.Slice.fr_smallAt
#print axioms OnBytes.Slice.fr_err_below

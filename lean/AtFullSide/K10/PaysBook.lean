-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysBook.lean: the closing of a segment (K10): at the book that the frame's maker returns at the written
description: what a closing's part spends, that no entry names a further part, and that the book's lending to the row of
one part returns where the part states the written lists. Statements with their proofs; the evaluations are in
PaysOk.lean, PaysByCarry.lean and PaysLong.lean.

Limits. That the maker returns is a premise. A lending that returns says that names, counts and cuts fit: nothing on what a
part does with the coins.
-/
import AtFullSide.K10.PaysOk
import AtFullSide.K10.PaysByCarry
import AtFullSide.K10.PaysLong

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First.Close (Par entries)
open Johnson.G (proofSendsFull)
open P2Law.ProofPlan (WP)

/-- Of the book's whole list and its short pieces a test that neither long list passes keeps the same entries. -/
theorem rawFilter_whole (t : Ahead → Bool) (hw : ∀ e ∈ rawWantsW.map (·.entry), t e = false)
    (hs : ∀ e ∈ rawSegW, t e = false) : rawAheadW.filter t = rawShortW.filter t := by
  have h1 : (rawWantsW.map (·.entry)).filter t = [] :=
    List.filter_eq_nil_iff.2 fun e he => by simp [hw e he]
  have h2 : rawSegW.filter t = [] := List.filter_eq_nil_iff.2 fun e he => by simp [hs e he]
  unfold rawAheadW rawShortW
  simp only [List.filter_append, h1, h2, List.nil_append, List.append_nil, List.filter_nil]

section
variable {B : ProverCoinCounts}

/-- The book's entries. -/
theorem close_ahead (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) : B.ahead = rawAheadW :=
  rawAhead_written B (rawWhole_is_raw hB)

/-- The book's rows of the first chain. -/
theorem close_rows (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) : B.first = rawRowsFirstW :=
  (rawBookRows_written _ B (rawWhole_is_raw hB)).1

/-- The eight tests, one by one. -/
theorem closeOk_open {P : Par} (hP : P ∈ parsW) :
    P.link < 25 ∧ closePlace P ∈ WP.first.blocksInOrder.map (·.place) ∧ dueAt rawRowsFirstW (closeAddr P) = ⟨0, 0⟩ ∧
      rawRowsFirstW.any (fun r => r.1.place == closePlace P && decide (1 ≤ r.1.part)) = false ∧
      (rawShortW.filter fun e => e.once && e.spender == closeAddr P).map Ahead.named = closeSpends P ∧
      rawShortW.any (fun e => e.spender.place == closePlace P && decide (1 ≤ e.spender.part)) = false ∧
      entries P ≠ [] ∧ cutOfNames .K10 ((entries P).map (·.name)) = [(entries P).length] := by
  have t := List.all_eq_true.1 closeOk_all P hP
  unfold closeOkB at t
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at t
  obtain ⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩, t8⟩ := t
  exact ⟨t1, List.contains_iff_mem.1 t2, t3, t4, t5, t6, t7, t8⟩

/-- **What the part at a closing spends.** -/
theorem close_spent (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {P : Par} (hP : P ∈ parsW) :
    (spentE B (closeAddr P)).map Ahead.named = closeSpends P := by
  have hw : ∀ e ∈ rawWantsW.map (·.entry), (e.once && e.spender == closeAddr P) = false := by
    intro e he
    have k : (e.spender.place.kind != .K10) = true := List.all_eq_true.1 wants_noClose e he
    cases hq : e.spender == closeAddr P with
    | false => simp
    | true =>
      rw [beq_iff_eq.1 hq] at k
      simp [closeAddr, closePlace] at k
  have hs : ∀ e ∈ rawSegW, (e.once && e.spender == closeAddr P) = false := by
    intro e he
    have k := List.all_eq_true.1 seg_noClose e he
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at k
    simp [k.1]
  unfold spentE
  rw [close_ahead hB, List.filter_filter, rawFilter_whole _ hw hs]
  exact (closeOk_open hP).2.2.2.2.1

/-- **No entry of the book names a part beyond the first at a closing's place.** -/
theorem close_beyond (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {P : Par} (hP : P ∈ parsW) :
    B.ahead.any (fun e => e.spender.place == closePlace P && decide (1 ≤ e.spender.part)) = false := by
  have h1 := (closeOk_open hP).2.2.2.2.2.1
  rw [close_ahead hB]
  have hall : rawAheadW.all (fun e => !(e.spender.place == closePlace P && decide (1 ≤ e.spender.part))) = true := by
    refine rawAll_whole _ (List.all_eq_true.2 fun e he => ?_) (List.all_eq_true.2 fun e he => ?_)
      (List.all_eq_true.2 fun e he => ?_)
    · have k : (e.spender.place.kind != .K10) = true := List.all_eq_true.1 wants_noClose e he
      cases hq : e.spender.place == closePlace P with
      | false => simp
      | true =>
        rw [beq_iff_eq.1 hq] at k
        simp [closePlace] at k
    · have k := List.all_eq_true.1 seg_noClose e he
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at k
      cases hq : e.spender.place == closePlace P with
      | false => simp
      | true =>
        have ep := beq_iff_eq.1 hq
        rcases k.2 with k2 | k2
        · exact absurd (by rw [ep]; rfl) k2
        · simp [k2]
    · cases hq : e.spender.place == closePlace P with
      | false => simp
      | true =>
        have k := List.any_eq_false.1 h1 e he
        rw [hq] at k
        simpa using k
  rw [List.any_eq_false]
  intro e he hh
  have hh' : (e.spender.place == closePlace P && decide (1 ≤ e.spender.part)) = true := hh
  have k : (!(e.spender.place == closePlace P && decide (1 ≤ e.spender.part))) = true :=
    List.all_eq_true.1 hall e he
  rw [hh'] at k
  exact absurd k (by decide)

/-- **The book's lending to the row of one part at a closing returns**, at a part that takes nothing, spends the fold's
run and carries the written list. -/
theorem close_lends {V W Y : Type} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {P : Par} (hP : P ∈ parsW) {p : Part V W Y}
    (h0 : p.takes = ⟨0, 0⟩) (h1 : p.spends = closeSpends P) (h2 : p.carries = closeCarries ⟨P, borneW P⟩)
    (k : Coins B) : ∃ c, lendRow B (B.rowsOf 0) (k.look 0) (closePlace P) [p] 0 = .ok c := by
  obtain ⟨-, hpl, hdue, -⟩ := closeOk_open hP
  have hd : p.takes = dueAt (B.rowsOf 0) (closeAddr P) := by
    show p.takes = dueAt B.first (closeAddr P)
    rw [close_rows hB, hdue, h0]
  have hc : (carryE B (closeAddr P)).map Ahead.named = p.carries := by
    obtain ⟨m0, hm, e⟩ := bookWhole_carries_named hB P2Law.ProofPlan.wp_placesOk (a := closeAddr P) hpl
    obtain rfl : sentFirstW = m0 := Except.ok.inj (sentIn_first_written.symm.trans hm)
    rw [e, h2]
    exact beq_iff_eq.1 (List.all_eq_true.1 closeCarry_by_triples P hP)
  obtain ⟨c, hl⟩ := lendPart_of_fit (rawWord_none B (rawWhole_is_raw hB)) P2Law.ProofPlan.wp_placesOk
    (Or.inl rfl) (a := closeAddr P) hpl hd ((close_spent hB hP).trans h1.symm) hc k
  refine ⟨(c, ()), ?_⟩
  have hl' : lendPart B (B.rowsOf 0) (k.look 0) ⟨closePlace P, 0⟩ p = .ok c := hl
  unfold lendRow
  rw [hl']
  rfl

end


end AtFullSide.K10

#print axioms AtFullSide.K10.rawFilter_whole
#print axioms AtFullSide.K10.close_ahead
#print axioms AtFullSide.K10.close_rows
#print axioms AtFullSide.K10.closeOk_open
#print axioms AtFullSide.K10.close_spent
#print axioms AtFullSide.K10.close_beyond
#print axioms AtFullSide.K10.close_lends

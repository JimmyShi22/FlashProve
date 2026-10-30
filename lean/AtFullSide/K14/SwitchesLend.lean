-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/SwitchesLend.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName (Honest/BookWhole.lean) LAYS:
WHATEVER BOOK bookWhole RETURNS THERE: AT THE FIRST PART OF EACH OF THE 25 WRITTEN PLACES OF THE
KIND "THE CODE SWITCH" (placesW, Honest/K2/Law/PlacesWritten.lean; 25: switchPlaces_count): THE
PUBLIC TEST lendsPart (Honest/Small/LendsRow.lean) ACCEPTS, IN THE FIRST CHAIN. No definition;
statements with their proofs.

What it is not.
  * lendsPart asks name, count and that the owners' cuts fit: it holds as well at a book that lends
    another owner's coins of that count. THIS SENTENCE GOES WITH EVERY CITATION OF THIS FILE.
    «Handed something» is not «handed its own coins, once»: that each run has the one owner and
    the one start that the sender's text lays is not said here. A BOOK's NUMBER IS A CLAIM ON A
    SENDER's TEXT: the book's own tests see entries, not texts.
  * WHETHER the part is handed something; never what, nor whose.
  * The part number 0 of each place (this kind's row has one part there); the chain number 0 alone.
  * THE SENDER THAT THE PART's TERM NAMES (K2.coreSender K2.freshTable) IS READ BY NONE OF THE
    STATEMENTS: lendsPart reads of a part its takes, spends and carries, and switchPart makes these
    of the sizes, the other messages, the fold's variables and the stated list alone. It stands in
    the term because the statement that calls this file has it.
  * AT WP. That any other description has this book, or that a maker's book is this one, is said
    elsewhere, not here.
  * placesW is another kind's closed term. That it is the plan's list of places: places_at_head
    (Honest/K2/Law/PlacesWritten.lean), under that file's premises.
  * KERNEL EVALUATIONS: they hold of the makers' texts as they lie beneath this file; the sendings
    are found by labels; THAT mergesByName's MERGES ARE THE FORMAT's IS A THEOREM NOWHERE.
  * THE TWO BENDS ARE TESTS OF THE WAY OF EVALUATING: that the Bool is not true whatever stands in
    it. Each follows from its fact: a count is not itself and one; a list is its own tail only
    where it is empty. What switchCarry_bent adds to the facts: no place states an empty list.
  * Names, numbers and addresses: public data alone. Nothing on soundness, completeness or hiding.

  switchPlaces_count   **placesW has 25 members**: SO NONE OF THE OTHERS HOLDS FOR WANT OF A CASE:
                  at an empty list all of them would hold, the two bends too
  switchThere_written, switchDue_written, switchNoFold_written, switchWants_written,
                  switchCarry_written **five closed facts, each one evaluation in Lean's kernel over
                  all places of placesW**: the place stands in WP's first chain; the part's own
                  count is the written table's; the place holds no fold; the part has no stretch TO
                  SPEND (of the stretches that spendingBook asks about none names it as spender;
                  what it carries is another matter: the fifth fact); what segmentCarriesAt
                  (Honest/BookCarryKit.lean) lays for the part at the written messages sentFirstW
                  is, by name and count and in order, what the part states as carried
  switchDue_bent, switchCarry_bent THEY CAN FAIL, AT EVERY PLACE OF placesW («any … = false»; 25 of
                  them: switchPlaces_count): at a count greater by one, and at the stated list less
                  its first member, the comparison rejects
  switch_three_at_written **at the book: the part's count is the table's; the book has no entry by
                  which it spends; the entries by which it carries have the names and counts that it
                  states, in the book's order**
  switch_lends_at_written   **lendsPart accepts**
  switch_lends_written   the same with no premise: bookWhole returns there

By what. The count: rawDue_of_written; nothing spent: rawSpentE_nil_of_wants
(AtFullSide/K14/RawAtSwitch24.lean). The carried: bookWhole_carries_named (Honest/BookCarryKit.lean)
at wp_placesOk (Johnson/AtFull/ProofPlan/At/PlacesOk.lean) and sentIn_first_written
(Honest/BookWritten/SentFirst.lean). From the three to the test: lendPart_of_fit
(Honest/BookLends.lean) at rawWord_none (AtFullSide/K14/BookWholeWritten.lean) through
rawWhole_is_raw (AtFullSide/K14/RawMineAtK13.lean), then lendPart_ok_iff and look_dueIs
(Honest/Small/LendsRow.lean), at the default coins. The return: bookWhole_returns_written
(AtFullSide/K14/BookWholeWritten.lean).
Homes. rawRowsFirstW, "the written table": AtFullSide/K14/RawBookRowsWritten.lean; rawNoFoldAt:
AtFullSide/K14/RawSpentWritten.lean; rawWantsAt: AtFullSide/K14/RawWantsAtSpenders.lean; sentFirstW:
Honest/BookWritten/SentFirst.lean; proofSendsFull, "the library's written sendings":
Johnson/G/SendsWritten.lean; dueAt: Honest/Frame.lean; spentE, carryE: Honest/Law/Rule/Cell.lean;
K2.switchPart: Honest/K2/Part.lean; K2.SwitchPlace and its carries: Honest/K2/Half.lean.
Kin. AtFullSide/K14/RawAtSwitch24.lean has the three at the place with link 24 in another way: a
written list of 178 runs, held against the chain of segments' 5,130 carrying entries.
OPTIONS ARE RAISED in front of the eight evaluations: maxRecDepth to 1000000 (no lower number was
tried) and maxHeartbeats lifted. The two over segmentCarriesAt first unfold the maker's reading of
labels by the library's splitOn_eq and slice_toNat?_eq (Johnson/Unfolds/). The file stands in this
side library because its first import does.
What is assumed. In switch_three_at_written and switch_lends_at_written: that bookWhole returns B
there, and that p is of placesW. In the others nothing.
-/
import AtFullSide.K14.RawAtSwitch24
import Johnson.Desc.ProofFile.Honest.BookCarryKit
import Johnson.Desc.ProofFile.Honest.BookLends
import Johnson.Desc.ProofFile.Honest.Small.LendsRow
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.AtFull.ProofPlan.At.PlacesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K2.Law (placesW)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-! ## 1 The count, five closed facts and two bends -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **THE WRITTEN LIST HAS 25 PLACES.** Without this every statement below could hold for want of a
case: "all" is true, "any" is false and "for every member" holds at an empty list. -/
theorem switchPlaces_count : placesW.length = 25 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Each written place stands in WP's first chain. -/
theorem switchThere_written :
    (placesW.all fun p => (WP.first.blocksInOrder.map (·.place)).contains p.place) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Each first part's own count is the written table's. -/
theorem switchDue_written : (placesW.all fun p => decide
    ((K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries).takes =
      dueAt rawRowsFirstW ⟨p.place, 0⟩)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- IT CAN FAIL, AT EVERY PLACE (25: switchPlaces_count): with the table's count of the extension
field greater by one no place passes. With the count that gives the weaker "all … = false" too: a
list with a member at which the test fails. It follows from switchDue_written: a test of the way of
evaluating. -/
theorem switchDue_bent : (placesW.any fun p => decide
    ((K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries).takes =
      ⟨(dueAt rawRowsFirstW ⟨p.place, 0⟩).f, (dueAt rawRowsFirstW ⟨p.place, 0⟩).e + 1⟩)) =
    false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No written place holds a fold. -/
theorem switchNoFold_written : (placesW.all fun p => rawNoFoldAt p.place) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No first part has a stretch to spend: of the stretches that spendingBook asks about none names
it as spender; and the list of these is there ("some []", not "none"). -/
theorem switchWants_written :
    (placesW.all fun p => rawWantsAt ⟨p.place, 0⟩ == some []) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **What segmentCarriesAt lays for each first part to carry is what the part states**, by name and
count, in order. (segmentCarriesAt is a second text of a part of the maker's segmentCarries, total,
[] where no fold is found; switch_three_at_written ties it to the book.) -/
theorem switchCarry_written : (placesW.all fun p =>
    (segmentCarriesAt (planOf WP.first.blocksInOrder) sentFirstW ⟨p.place, 0⟩).map Ahead.named ==
      p.carries) = true := by
  unfold segmentCarriesAt linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- IT CAN FAIL, AT EVERY PLACE (25: switchPlaces_count): at the stated list less its first member
no place passes. With the count that gives the weaker "all … = false" too. (So, with
switchCarry_written, no place states an empty list: there the two lists would be one.) -/
theorem switchCarry_bent : (placesW.any fun p =>
    (segmentCarriesAt (planOf WP.first.blocksInOrder) sentFirstW ⟨p.place, 0⟩).map Ahead.named ==
      p.carries.drop 1) = false := by
  unfold segmentCarriesAt linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-! ## 2 On the book -/

/-- **AT THE BOOK: THE THREE THAT lendPart_of_fit ASKS OF IT AT A SWITCH's FIRST PART.** -/
theorem switch_three_at_written {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B)
    {p : K2.SwitchPlace} (hp : p ∈ placesW) :
    (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries).takes =
        dueAt (B.rowsOf 0) ⟨p.place, 0⟩ ∧
      spentE B ⟨p.place, 0⟩ = [] ∧ (carryE B ⟨p.place, 0⟩).map Ahead.named = p.carries := by
  have h1 := of_decide_eq_true (List.all_eq_true.1 switchDue_written p hp)
  have h2 := List.all_eq_true.1 switchNoFold_written p hp
  have h3 := beq_iff_eq.1 (List.all_eq_true.1 switchWants_written p hp)
  have h4 := beq_iff_eq.1 (List.all_eq_true.1 switchCarry_written p hp)
  have h5 : p.place ∈ WP.first.blocksInOrder.map (·.place) :=
    List.contains_iff_mem.1 (List.all_eq_true.1 switchThere_written p hp)
  refine ⟨h1.trans (rawDue_of_written hB rfl).symm, rawSpentE_nil_of_wants hB h2 h3, ?_⟩
  obtain ⟨m0, hm, e⟩ := bookWhole_carries_named hB P2Law.ProofPlan.wp_placesOk
    (a := ⟨p.place, 0⟩) h5
  obtain rfl : sentFirstW = m0 := Except.ok.inj (sentIn_first_written.symm.trans hm)
  exact e.trans h4

/-- **THE PUBLIC TEST ON A SWITCH's FIRST PART ACCEPTS AT THE BOOK.** lendsPart asks name, count and
that the owners' cuts fit: it holds as well at a book that lends another owner's coins of that
count. -/
theorem switch_lends_at_written {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B)
    {p : K2.SwitchPlace} (hp : p ∈ placesW) :
    lendsPart B (B.rowsOf 0) (lookDue B 0) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
      true := by
  obtain ⟨hd, hs, hc⟩ := switch_three_at_written hB hp
  have h5 : p.place ∈ WP.first.blocksInOrder.map (·.place) :=
    List.contains_iff_mem.1 (List.all_eq_true.1 switchThere_written p hp)
  have hl := lendPart_of_fit (rawWord_none B (rawWhole_is_raw hB)) P2Law.ProofPlan.wp_placesOk
    (Or.inl rfl) (a := ⟨p.place, 0⟩) h5 hd (by rw [hs]; rfl) hc default
  have i := (lendPart_ok_iff B (B.rowsOf 0) ((default : Coins B).look 0) ⟨p.place, 0⟩
    (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries)).1 hl
  have e : (fun o => ((default : Coins B).look 0 o).1) = lookDue B 0 :=
    funext fun o => look_dueIs default 0 o
  rw [e] at i
  exact i

/-- The same with no premise: bookWhole returns there. -/
theorem switch_lends_written : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B ∧
    ∀ p ∈ placesW, lendsPart B (B.rowsOf 0) (lookDue B 0) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
      true := by
  obtain ⟨B, hB⟩ := bookWhole_returns_written
  exact ⟨B, hB, fun _ hp => switch_lends_at_written hB hp⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.switchPlaces_count
#print axioms AtFullSide.K14.switchThere_written
#print axioms AtFullSide.K14.switchDue_written
#print axioms AtFullSide.K14.switchDue_bent
#print axioms AtFullSide.K14.switchNoFold_written
#print axioms AtFullSide.K14.switchWants_written
#print axioms AtFullSide.K14.switchCarry_written
#print axioms AtFullSide.K14.switchCarry_bent
#print axioms AtFullSide.K14.switch_three_at_written
#print axioms AtFullSide.K14.switch_lends_at_written
#print axioms AtFullSide.K14.switch_lends_written

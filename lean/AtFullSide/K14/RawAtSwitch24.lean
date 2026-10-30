-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawAtSwitch24.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName (Honest/BookWhole.lean) GUESSES:
WHATEVER BOOK bookWhole RETURNS THERE: AT THE PART 0 OF THE PLACE ⟨1, some 24, 2, K2⟩: THE FIRST
CHAIN's TABLE OF ROWS HAS THE COUNT ⟨23217, 9086⟩ FOR IT; IT SPENDS NOTHING; AND WHAT IS CARRIED TO
IT IS, IN THE BOOK's OWN ORDER, A WRITTEN LIST OF 178 RUNS, EACH BY NAME AND COUNT. Five
definitions, four with code, one a written list; statements with their proofs.

  rawCarryNamed l a   of a list of entries: those that carry to the part a, each as the part states
                  it (Ahead.named, Honest/Frame.lean): name and count
  rawCarryNamed_append, rawCarryNamed_wants, rawFrontW, rawBackW, rawCarryNamed_whole   over the
                  written entries rawAheadW (AtFullSide/K14/RawAheadWritten.lean) it is three
                  shares, in the book's own order: the written pieces in front, the chain of
                  segments' carrying entries rawSegW, the written pieces behind; the stretches'
                  entries give nothing
  rawCarry_of_pieces, rawSpentE_nil_of_wants, rawDue_of_written   **the steps onto the book**,
                  general in the part
  rawDueW_atSwitch24, rawDueAtSwitch24   **dueAt (B.rowsOf 0) a = ⟨23217, 9086⟩**
  rawNoFoldAtSwitch24, rawWantsAtSwitch24, rawSpentEAtSwitch24   **spentE B a = []**: the place
                  holds no fold; the part has no stretch: an evaluation over the stretches
  rawSwitch24CarriesW, rawCarrySegAtSwitch24   **rawSegW's share is the written list**: ONE
                  EVALUATION IN LEAN's KERNEL over that piece. rawCarrySegAtSwitch24_bent: with the
                  first count greater by one the comparison rejects
  rawCarryFrontAtSwitch24, rawCarryBackAtSwitch24   the two other shares are empty
  rawCarryAtSwitch24   **(carryE B a).map Ahead.named = rawSwitch24CarriesW**

rawSegW is (segmentCarries …).toOption.getD []: at a rejection [] would stand there, and a statement
on all its members would be idle: the maker does not reject: rawSeg_returns, rawSeg_ok
(AtFullSide/K14/RawAheadWritten.lean); it has 5,130 members: rawSegW_length
(AtFullSide/K14/RawLengthsWritten.lean).
Homes. carryE, spentE: Honest/Law/Rule/Cell.lean; dueAt, lendPart, lendRow: Honest/Frame.lean. That
the part spends nothing rests on the frame's pick_whole (Honest/BookRowStretch.lean), through
rawSpentE_entries (AtFullSide/K14/RawMineAtK13.lean).
Kin. rawFrontW ++ rawBackW is rawShortW (AtFullSide/K14/RawEntriesKit.lean) cut in two.
rawSpentE_nil_of_wants follows also from rawSpent_of_wantsAt at the empty list
(AtFullSide/K14/RawSpentWritten.lean). rawDue_of_written is the general form of rawDueAtK13's step
(AtFullSide/K14/RawMineAtK13.lean).
The written list was typed off a print of Lean's evaluator; what holds it is the kernel's
evaluation.
OPTIONS ARE RAISED in front of the evaluations: maxRecDepth to 1000000 (no lower number was tried);
in front of the three long ones maxHeartbeats is lifted too. The two over rawSegW first unfold the
maker's reading of labels by the library's splitOn_eq and slice_toNat?_eq (Johnson/Unfolds/). The
file stands in this side library because its import does.
What is assumed. Nothing beyond each statement's own premise: that bookWhole returns B there. That
it does return: bookWhole_returns_written (AtFullSide/K14/BookWholeWritten.lean): of the makers'
texts as they lie beneath this file, and at mergesByName, a guess.
What is not claimed. That lendPart or lendRow returns at this part: these are three things that it
asks of the book; OF THE 178 ENTRIES' OWNERS AND STARTS NOTHING IS SAID: names and counts alone;
that each run is a message's whole stretch, and that none is lacking, is the maker's text, no
statement here. ONE PART OF ONE PLACE: nothing on the place's other parts, nor on the other
switches. what the part itself states (its takes, its carries) is another kind's. A BOOK's NUMBER IS
A CLAIM ON A SENDER's TEXT: the book's own tests see entries, not texts. THAT ANY DESCRIPTION BUT WP
HAS THESE VALUES; the sendings are found by labels that rest on one print; THE MERGES ARE A GUESS.
It holds of the makers' texts as they lie beneath this file. Names, numbers and addresses: nothing
on soundness, completeness or hiding.
-/
import AtFullSide.K14.RawMineAtK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-! ## 1 A small kit, general in the part -/

/-- Of a list of entries: those that carry to the part a, each as the part states it: name and
count. -/
def rawCarryNamed (l : List Ahead) (a : Addr) : List (String × Due) :=
  ((l.filter fun e => e.spender == a).filter fun e => !e.once).map Ahead.named

/-- It goes over "++". -/
theorem rawCarryNamed_append (l l' : List Ahead) (a : Addr) :
    rawCarryNamed (l ++ l') a = rawCarryNamed l a ++ rawCarryNamed l' a := by
  unfold rawCarryNamed
  rw [List.filter_append, List.filter_append, List.map_append]

/-- The stretches' entries all spend: none carries. -/
theorem rawCarryNamed_wants (a : Addr) : rawCarryNamed (rawWantsW.map (·.entry)) a = [] := by
  unfold rawCarryNamed
  refine List.map_eq_nil_iff.2 (List.filter_eq_nil_iff.2 fun e he hne => ?_)
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 (List.mem_filter.1 he).1
  cases hne

/-- rawAheadW's written pieces in front of the chain of segments' carrying entries. -/
def rawFrontW : List Ahead := foldsFirstW ++ foldsSharedW ++ [] ++ [splitEntryWritten]

/-- Its written pieces behind them. -/
def rawBackW : List Ahead :=
  rawCarriesFoldedW ++ rawCarriesOmegaW ++ rawCarriesWW ++ rawOwnCarryW

/-- **What is carried to a part, out of all the written entries, in the book's own order**: three
shares. -/
theorem rawCarryNamed_whole (a : Addr) : rawCarryNamed rawAheadW a =
    rawCarryNamed rawFrontW a ++ rawCarryNamed rawSegW a ++ rawCarryNamed rawBackW a := by
  unfold rawAheadW rawFrontW rawBackW
  simp only [rawCarryNamed_append, rawCarryNamed_wants, List.nil_append, List.append_assoc]

/-- **On the book**: whatever book bookWhole returns at WP: what is carried to a part, from the
three shares. Where rawSegW's share is [], quote it beside rawSeg_returns: at a rejection rawSegW
would be []. -/
theorem rawCarry_of_pieces {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) {a : Addr}
    {f s b : List (String × Due)} (hf : rawCarryNamed rawFrontW a = f)
    (hs : rawCarryNamed rawSegW a = s) (hb : rawCarryNamed rawBackW a = b) :
    (carryE B a).map Ahead.named = f ++ s ++ b := by
  have h : (carryE B a).map Ahead.named = rawCarryNamed rawAheadW a := by
    unfold carryE rawCarryNamed
    rw [rawAhead_written B (rawWhole_is_raw hB)]
  rw [h, rawCarryNamed_whole, hf, hs, hb]

/-- At a part of a place without a fold that has no stretch: it spends nothing. -/
theorem rawSpentE_nil_of_wants {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) {p : Place}
    (hp : rawNoFoldAt p = true) {j : Nat} (hw : rawWantsAt ⟨p, j⟩ = some []) :
    spentE B ⟨p, j⟩ = [] := by
  obtain ⟨a, ha, hs⟩ := rawSpentE_entries hB hp j
  have ht := Option.some.inj ((rawWantsAt_of_ok ha ⟨p, j⟩).symm.trans hw)
  rw [hs, List.map_eq_nil_iff.1 ht]
  rfl

/-- The first chain's table's count for a part, off the written rows. -/
theorem rawDue_of_written {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) {a : Addr} {d : Due}
    (h : dueAt rawRowsFirstW a = d) : dueAt (B.rowsOf 0) a = d := by
  have e : B.rowsOf 0 = rawRowsFirstW := (rawBookRows_written _ B (rawWhole_is_raw hB)).1
  rw [e]
  exact h

/-! ## 2 At the part 0 of the place ⟨1, some 24, 2, K2⟩ -/

set_option maxRecDepth 1000000 in
/-- The written rows' count for the part. -/
theorem rawDueW_atSwitch24 : dueAt rawRowsFirstW ⟨⟨1, some 24, 2, .K2⟩, 0⟩ = ⟨23217, 9086⟩ := by
  decide +kernel

/-- **THE FIRST CHAIN's TABLE's COUNT FOR THE PART.** -/
theorem rawDueAtSwitch24 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    dueAt (B.rowsOf 0) ⟨⟨1, some 24, 2, .K2⟩, 0⟩ = ⟨23217, 9086⟩ :=
  rawDue_of_written hB rawDueW_atSwitch24

set_option maxRecDepth 1000000 in
/-- The place holds no fold. -/
theorem rawNoFoldAtSwitch24 : rawNoFoldAt ⟨1, some 24, 2, .K2⟩ = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The part has no stretch. -/
theorem rawWantsAtSwitch24 : rawWantsAt ⟨⟨1, some 24, 2, .K2⟩, 0⟩ = some [] := by decide +kernel

/-- **THE PART SPENDS NOTHING.** -/
theorem rawSpentEAtSwitch24 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    spentE B ⟨⟨1, some 24, 2, .K2⟩, 0⟩ = [] :=
  rawSpentE_nil_of_wants hB rawNoFoldAtSwitch24 rawWantsAtSwitch24

/-- What is carried to the part, written: each run's name and count, in the book's own order. -/
def rawSwitch24CarriesW : List (String × Due) :=
  [("message 0 of 1.0.1.0 to 1.24.2.0: carried", ⟨23214, 8411⟩),
    ("message 1 of 1.0.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.0.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.0.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.0.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.0.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.1.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.1.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.1.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.1.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.1.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.1.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.1.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.2.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.2.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.2.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.2.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.2.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.2.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.2.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.2.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.3.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.3.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.3.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.3.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.3.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.3.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.3.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.4.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.4.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.4.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.4.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.4.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.4.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.4.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.4.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.5.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.5.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.5.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.5.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.5.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.5.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.5.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.6.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.6.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.6.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.6.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.6.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.6.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.6.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.6.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.7.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.7.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.7.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.7.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.7.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.7.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.7.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.8.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.8.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.8.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.8.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.8.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.8.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.8.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.8.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.9.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.9.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.9.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.9.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.9.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.9.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.9.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.10.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.10.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.10.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.10.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.10.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.10.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.10.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.10.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.11.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.11.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.11.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.11.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.11.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.11.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.11.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.12.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.12.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.12.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.12.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.12.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.12.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.12.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.12.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.13.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.13.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.13.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.13.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.13.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.13.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.13.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.14.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.14.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.14.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.14.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.14.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.14.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.14.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.14.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.15.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.15.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.15.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.15.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.15.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.15.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.15.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.16.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.16.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.16.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.16.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.16.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.16.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.16.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.16.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.17.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.17.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.17.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.17.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.17.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.17.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.17.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.18.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.18.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.18.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.18.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.18.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.18.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.18.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.18.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.19.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.19.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.19.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.19.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.19.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.19.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.19.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.20.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.20.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.20.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.20.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.20.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.20.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.20.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.20.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.21.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.21.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.21.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.21.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.21.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.21.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.21.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩),
    ("message 0 of 1.22.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.22.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 2 of 1.22.1.0 to 1.24.2.0: carried", ⟨22776, 8411⟩),
    ("message 3 of 1.22.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 4 of 1.22.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 5 of 1.22.1.0 to 1.24.2.0: carried", ⟨0, 236⟩),
    ("message 0 of 1.22.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.22.6.0 to 1.24.2.0: carried", ⟨6792, 0⟩),
    ("message 0 of 1.23.1.0 to 1.24.2.0: carried", ⟨0, 439⟩),
    ("message 1 of 1.23.1.0 to 1.24.2.0: carried", ⟨1974, 0⟩),
    ("message 2 of 1.23.1.0 to 1.24.2.0: carried", ⟨660, 0⟩),
    ("message 3 of 1.23.1.0 to 1.24.2.0: carried", ⟨9198, 8411⟩),
    ("message 4 of 1.23.1.0 to 1.24.2.0: carried", ⟨0, 234⟩),
    ("message 0 of 1.23.4.0 to 1.24.2.0: carried", ⟨0, 220⟩),
    ("message 0 of 1.23.6.0 to 1.24.2.0: carried", ⟨3069, 0⟩)]

/-- The same with the first count greater by one. -/
def rawSwitch24BentW : List (String × Due) :=
  ("message 0 of 1.0.1.0 to 1.24.2.0: carried", ⟨23215, 8411⟩) :: rawSwitch24CarriesW.tail

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The chain of segments' carrying entries' share is the written list**: an evaluation in Lean's
kernel. (rawSegW is what the maker returns: rawSeg_returns.) -/
theorem rawCarrySegAtSwitch24 :
    rawCarryNamed rawSegW ⟨⟨1, some 24, 2, .K2⟩, 0⟩ = rawSwitch24CarriesW := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The comparison can reject: the first member's count is bent: it may stop there: a test of the
way of evaluating, not of the rest of the list. -/
theorem rawCarrySegAtSwitch24_bent :
    decide (rawCarryNamed rawSegW ⟨⟨1, some 24, 2, .K2⟩, 0⟩ = rawSwitch24BentW) = false := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written pieces in front carry nothing to the part. -/
theorem rawCarryFrontAtSwitch24 : rawCarryNamed rawFrontW ⟨⟨1, some 24, 2, .K2⟩, 0⟩ = [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Nor do the written pieces behind. -/
theorem rawCarryBackAtSwitch24 : rawCarryNamed rawBackW ⟨⟨1, some 24, 2, .K2⟩, 0⟩ = [] := by
  decide +kernel

/-- **ALL THAT IS CARRIED TO THE PART, IN THE BOOK's OWN ORDER, BY NAME AND COUNT.** -/
theorem rawCarryAtSwitch24 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    (carryE B ⟨⟨1, some 24, 2, .K2⟩, 0⟩).map Ahead.named = rawSwitch24CarriesW := by
  have h := rawCarry_of_pieces hB rawCarryFrontAtSwitch24 rawCarrySegAtSwitch24
    rawCarryBackAtSwitch24
  rw [List.nil_append, List.append_nil] at h
  exact h

/-- The written list has 178 members. -/
theorem rawSwitch24Carries_length : rawSwitch24CarriesW.length = 178 := rfl

end AtFullSide.K14

#print axioms AtFullSide.K14.rawCarryNamed_append
#print axioms AtFullSide.K14.rawCarryNamed_wants
#print axioms AtFullSide.K14.rawCarryNamed_whole
#print axioms AtFullSide.K14.rawCarry_of_pieces
#print axioms AtFullSide.K14.rawSpentE_nil_of_wants
#print axioms AtFullSide.K14.rawDue_of_written
#print axioms AtFullSide.K14.rawDueW_atSwitch24
#print axioms AtFullSide.K14.rawDueAtSwitch24
#print axioms AtFullSide.K14.rawNoFoldAtSwitch24
#print axioms AtFullSide.K14.rawWantsAtSwitch24
#print axioms AtFullSide.K14.rawSpentEAtSwitch24
#print axioms AtFullSide.K14.rawCarrySegAtSwitch24
#print axioms AtFullSide.K14.rawCarrySegAtSwitch24_bent
#print axioms AtFullSide.K14.rawCarryFrontAtSwitch24
#print axioms AtFullSide.K14.rawCarryBackAtSwitch24
#print axioms AtFullSide.K14.rawCarryAtSwitch24
#print axioms AtFullSide.K14.rawSwitch24Carries_length

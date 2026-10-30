-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawMineAtK13.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName (Honest/BookWhole.lean) GUESSES:
WHATEVER BOOK bookWhole RETURNS THERE: OF ALL ITS ENTRIES JUST ONE NAMES THE PART 1 AT THE PLACE ⟨1,
none, 3, K13⟩ AS ITS SPENDER, A WRITTEN ENTRY THAT SPENDS, NAME AND ALL; NONE NAMES THE PART 0; NO
PART OF THAT PLACE CARRIES; AND THE FIRST CHAIN's TABLE OF ROWS HAS NO COUNT FOR THE TWO PARTS. Two
definitions with code; statements with their proofs.

  rawK13Entry     the one entry, written: its name by runName (Honest/ForKinds.lean)
  rawWhole_is_raw   the book that bookWhole returns is one that bookRaw returns: the frame's
                  ex_bindE (Honest/BookSharedKit.lean) and checked_ok (Honest/BookSharedLaw.lean)
  rawSpentE_entries   at a part of a place without a fold: what it spends is its stretches' entries,
                  WHOLE (Want.entry, Honest/BookEntries.lean): the frame's pick_whole
                  (Honest/BookRowStretch.lean), as in AtFullSide/K14/RawSpentWritten.lean
  rawSpentEAtK13_part1, rawSpentEAtK13_part0   **spentE at the part 1 is [rawK13Entry]; at the part
                  0 []**: BY CALLS: rawWantsAtK13_written (use, number, count), rawWants_msg
                  (AtFullSide/K14/RawWantsOnce.lean: the place has no link: so the message is the
                  index-mask message), rawSpentAtK13Place: nothing is evaluated for them here
  rawNoCarryAt p, rawNoCarry_wants, rawNoCarry_seg, rawNoCarry_short, rawNoCarry_all   **no entry of
                  the written entries rawAheadW (AtFullSide/K14/RawAheadWritten.lean) that carries
                  has its spender at K13's place**: piece by piece (rawAll_whole,
                  AtFullSide/K14/RawEntriesKit.lean): the stretches' entries all spend; the chain of
                  segments' carrying entries: ONE EVALUATION IN LEAN's KERNEL; the written pieces: a
                  small one. rawNoCarry_bent: at a place that holds a fold the test rejects
  rawCarryAtK13   **carryE (Honest/Law/Rule/Cell.lean) is empty at every part of that place**
  rawMineAtK13_part1, rawMineAtK13_part0   **so all the entries with these spenders**: what lendPart
                  (Honest/Frame.lean) calls "mine"
  rawDueW_atK13, rawDueAtK13   **dueAt (B.rowsOf 0) is ⟨0, 0⟩ at both parts**: by
                  rawBookRows_written (AtFullSide/K14/RawBookRowsWritten.lean) and a small
                  evaluation

OPTIONS ARE RAISED in front of the evaluations: maxRecDepth to 1000000 (no lower number was tried);
in front of the two over the chain of segments' entries maxHeartbeats is lifted too. These two first
unfold the maker's reading of labels by the library's splitOn_eq and slice_toNat?_eq
(Johnson/Unfolds/): left as it is, the kernel's evaluation sticks there (seen). The file stands in
this side library because its imports do.
rawSegW is (segmentCarries …).toOption.getD []: at a rejection [] would stand there, and a statement
on all its members would be idle: the maker does not reject: rawSeg_returns, rawSeg_ok
(AtFullSide/K14/RawAheadWritten.lean); it has 5,130 members: rawSegW_length
(AtFullSide/K14/RawLengthsWritten.lean).
What is assumed. Nothing beyond each statement's own premise: that bookWhole returns B there. That
it does return: bookWhole_returns_written (AtFullSide/K14/BookWholeWritten.lean): of the makers'
texts as they lie beneath this file, and at mergesByName, a guess.
What is not claimed. A BOOK's NUMBER IS A CLAIM ON A SENDER's TEXT: the book's own tests see
entries, not texts. That lendPart or lendRow returns at these parts: these are things that it asks.
THAT ANY DESCRIPTION BUT WP HAS THESE VALUES; the sendings are found by labels that rest on one
print; THE MERGES ARE A GUESS: that K13's part is a lone sumcheck is that guess's doing. Names,
numbers and addresses: nothing on soundness, completeness or hiding.
-/
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K14.RawSpentAtPlaces
import AtFullSide.K14.RawWantsOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The one entry that names K13's part 1 as its spender, written. -/
def rawK13Entry : Ahead :=
  ⟨runName indexMaskRun ⟨⟨1, none, 3, .K13⟩, 1⟩ "sum", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8660⟩,
    ⟨0, 37⟩, ⟨⟨1, none, 3, .K13⟩, 1⟩, true⟩

/-- The book that bookWhole returns is one that bookRaw returns. -/
theorem rawWhole_is_raw {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B := by
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := BookShared.ex_bindE hB
  obtain rfl := checked_ok hc
  exact hW

/-- **At a part of a place without a fold: what it spends is its stretches' entries, whole.** -/
theorem rawSpentE_entries {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) {p : Place}
    (hp : rawNoFoldAt p = true) (j : Nat) :
    ∃ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
      (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
        .ok a ∧
      spentE B ⟨p, j⟩ = ((a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
        ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
        fun w => w.spender == ⟨p, j⟩).map (·.entry) := by
  obtain ⟨b, hb, rfl, hF⟩ := rawNoFold_block hp
  obtain ⟨idx, a, hidx, ha, -, hpick⟩ := pick_whole hB P2Law.ProofPlan.wp_placesOk hb hF
  obtain rfl : rawIdxW = idx := Option.some.inj (rawIdx_written.symm.trans hidx)
  exact ⟨a, ha, hpick j⟩

/-- **ALL THAT K13's PART 1 SPENDS: THE ONE ENTRY, NAME AND ALL.** -/
theorem rawSpentEAtK13_part1 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    spentE B ⟨⟨1, none, 3, .K13⟩, 1⟩ = [rawK13Entry] := by
  obtain ⟨a, ha, hs⟩ := rawSpentE_entries hB rawNoFold_written.2 1
  have ht := Option.some.inj ((rawWantsAt_of_ok ha ⟨⟨1, none, 3, .K13⟩, 1⟩).symm.trans
    rawWantsAtK13_written)
  rw [hs]
  obtain ⟨w, hW, ht'⟩ := List.map_eq_singleton_iff.1 ht
  have hw : w ∈ ((a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
        ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
      fun w => w.spender == ⟨⟨1, none, 3, .K13⟩, 1⟩) := by
    rw [hW]
    exact List.mem_singleton.2 rfl
  obtain ⟨hmem, hsp⟩ := List.mem_filter.1 hw
  have hsp' : w.spender = ⟨⟨1, none, 3, .K13⟩, 1⟩ := beq_iff_eq.1 hsp
  have hmsg : w.msg = rawIdxW := by
    rcases rawWants_msg a ha w hmem with h | ⟨l, hl, -⟩
    · exact h
    · rw [hsp'] at hl
      cases hl
  have hu : w.use = "sum" := congrArg (·.1) ht'
  have hn : w.number = 13 := congrArg (·.2.2.2.1) ht'
  have hc : w.count = 37 := congrArg (·.2.2.2.2) ht'
  rw [hW]
  show [w.entry] = [rawK13Entry]
  unfold Want.entry
  rw [hsp', hmsg, hu, hn, hc]
  rfl

/-- The part 0 spends nothing. -/
theorem rawSpentEAtK13_part0 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    spentE B ⟨⟨1, none, 3, .K13⟩, 0⟩ = [] :=
  List.map_eq_nil_iff.1 (rawSpentAtK13Place hB 0)

/-- The test on an entry: it spends, or its spender does not stand at the place p. -/
def rawNoCarryAt (p : Place) (e : Ahead) : Bool := e.once || e.spender.place != p

/-- The stretches' entries all spend. -/
theorem rawNoCarry_wants (p : Place) :
    (rawWantsW.map (·.entry)).all (rawNoCarryAt p) = true := by
  rw [List.all_map]
  exact List.all_eq_true.2 fun _ _ => rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Of the chain of segments' carrying entries none has its spender at K13's place**: an
evaluation in Lean's kernel. Not idle: rawSegW is what the maker returns (rawSeg_returns) and has
5,130 members (rawSegW_length). -/
theorem rawNoCarry_seg : rawSegW.all (rawNoCarryAt ⟨1, none, 3, .K13⟩) = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The evaluation can fail: at a place of link 0 that holds a fold the test rejects. -/
theorem rawNoCarry_bent : rawSegW.all (rawNoCarryAt ⟨1, some 0, 11, .K10⟩) = false := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Nor has any of the written pieces' entries. -/
theorem rawNoCarry_short : rawShortW.all (rawNoCarryAt ⟨1, none, 3, .K13⟩) = true := by
  decide +kernel

/-- **NO ENTRY OF rawAheadW THAT CARRIES HAS ITS SPENDER AT K13's PLACE.** -/
theorem rawNoCarry_all : rawAheadW.all (rawNoCarryAt ⟨1, none, 3, .K13⟩) = true :=
  rawAll_whole _ (rawNoCarry_wants _) rawNoCarry_seg rawNoCarry_short

/-- **NO PART OF K13's PLACE CARRIES.** -/
theorem rawCarryAtK13 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (j : Nat) :
    carryE B ⟨⟨1, none, 3, .K13⟩, j⟩ = [] := by
  unfold carryE
  rw [rawAhead_written B (rawWhole_is_raw hB)]
  refine List.filter_eq_nil_iff.2 fun e he hne => ?_
  obtain ⟨hm, hs⟩ := List.mem_filter.1 he
  have hall : (e.once || e.spender.place != ⟨1, none, 3, .K13⟩) = true :=
    List.all_eq_true.1 rawNoCarry_all e hm
  have hsp : e.spender = ⟨⟨1, none, 3, .K13⟩, j⟩ := beq_iff_eq.1 hs
  cases ho : e.once with
  | true =>
    rw [ho] at hne
    cases hne
  | false =>
    rw [ho, hsp] at hall
    cases hall

/-- A list whose members that pass a test are l, and none of whose members fails it, is l. -/
theorem filter_whole {α : Type} (t : α → Bool) {L l : List α} (h1 : L.filter t = l)
    (h2 : (L.filter fun x => !t x) = []) : L = l := by
  rw [← h1]
  refine (List.filter_eq_self.2 fun x hx => ?_).symm
  cases ht : t x with
  | true => rfl
  | false =>
    exact absurd (List.mem_filter.2 ⟨hx, by rw [ht]; rfl⟩ : x ∈ L.filter fun x => !t x)
      (by rw [h2]; exact List.not_mem_nil)

/-- **ALL THE ENTRIES THAT NAME K13's PART 1 AS THEIR SPENDER.** -/
theorem rawMineAtK13_part1 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    (B.ahead.filter fun e => e.spender == ⟨⟨1, none, 3, .K13⟩, 1⟩) = [rawK13Entry] :=
  filter_whole (fun e : Ahead => e.once) (rawSpentEAtK13_part1 hB) (rawCarryAtK13 hB 1)

/-- **NONE NAMES THE PART 0.** -/
theorem rawMineAtK13_part0 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    (B.ahead.filter fun e => e.spender == ⟨⟨1, none, 3, .K13⟩, 0⟩) = [] :=
  filter_whole (fun e : Ahead => e.once) (rawSpentEAtK13_part0 hB) (rawCarryAtK13 hB 0)

set_option maxRecDepth 1000000 in
/-- The written rows of the first chain have no count for either part. -/
theorem rawDueW_atK13 : dueAt rawRowsFirstW ⟨⟨1, none, 3, .K13⟩, 0⟩ = ⟨0, 0⟩ ∧
    dueAt rawRowsFirstW ⟨⟨1, none, 3, .K13⟩, 1⟩ = ⟨0, 0⟩ := by decide +kernel

/-- **THE FIRST CHAIN's TABLE HAS NO COUNT FOR EITHER PART.** -/
theorem rawDueAtK13 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    dueAt (B.rowsOf 0) ⟨⟨1, none, 3, .K13⟩, 0⟩ = ⟨0, 0⟩ ∧
      dueAt (B.rowsOf 0) ⟨⟨1, none, 3, .K13⟩, 1⟩ = ⟨0, 0⟩ := by
  have h : B.rowsOf 0 = rawRowsFirstW := (rawBookRows_written _ B (rawWhole_is_raw hB)).1
  rw [h]
  exact rawDueW_atK13

end AtFullSide.K14

#print axioms AtFullSide.K14.rawWhole_is_raw
#print axioms AtFullSide.K14.rawSpentE_entries
#print axioms AtFullSide.K14.rawSpentEAtK13_part1
#print axioms AtFullSide.K14.rawSpentEAtK13_part0
#print axioms AtFullSide.K14.rawNoCarry_wants
#print axioms AtFullSide.K14.rawNoCarry_seg
#print axioms AtFullSide.K14.rawNoCarry_bent
#print axioms AtFullSide.K14.rawNoCarry_short
#print axioms AtFullSide.K14.rawNoCarry_all
#print axioms AtFullSide.K14.rawCarryAtK13
#print axioms AtFullSide.K14.filter_whole
#print axioms AtFullSide.K14.rawMineAtK13_part1
#print axioms AtFullSide.K14.rawMineAtK13_part0
#print axioms AtFullSide.K14.rawDueW_atK13
#print axioms AtFullSide.K14.rawDueAtK13

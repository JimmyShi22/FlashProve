-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/SegmentZeroAtWritten.lean: AT THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName
GUESSES: WHAT THE THREE PLACES OF THE FIRST SEGMENT THAT SPEND ARE HANDED OF THE SEGMENT's MASK
ROW, BY NUMBER: WHATEVER BOOK bookWhole RETURNS THERE, AND THERE IS ONE: ⟨1, some 0, 2, .K3⟩: one
stretch of the opening's sender's coins of the extension field, from 0, 1930 long · ⟨1, some 0, 3,
.K4⟩: ONE BLOCK, from 1930, 765 long, AND THEN THE MERGE's ONE ENTRY OF THE INDEX-MASK MESSAGE
(part 18; number 0; count 1) · ⟨1, some 0, 7, .K3⟩: one stretch, from 2696, 1363 long. AND THE
FRAME's OWN TEST wantsFree ON THE THREE BLOCKS: YES; WITH K4's START MOVED INTO K3's STRETCH: NO.
PUBLIC DATA ALONE: places, parts, numbers: where a run of coins begins, never what stands in it.
Two definitions (a written value; a written list with one letter); fourteen theorems. A TRIAL THAT
COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.

rowZeroW, rowZeroW_written link 0's mask row as an owner, written; it IS the first member of
another house's rawRowsW (AtFullSide/K14/RawFactsWritten.lean). k4RowOk our test mergeRowOk
(AtFullSide/K1/MergeRowAtWritten.lean) ACCEPTS K4's place with 19 parts, the merge at number 18,
the owner, 1930, 765, and the merge's entry's 0 and 1: one evaluation in Lean's kernel.
k4RowOk_bent_start, _bent_owner, _bent_merge THE EVALUATION CAN FAIL, THRICE: with 1931 for 1930 ·
with the address of the segment's next sending of the kind K1 for the owner · with 17 for 18: it
rejects. k4MergeRowAt WHAT K4's ROW SPENDS in whatever book bookWhole returns at WP: by
mergeRow_of_ok. k3RowOk, k3RowOk_bent, k3RowAt2, k3RowAt7 the like at K3's two places, by another
house's rawRowOk and rawRowStretch_of_ok (AtFullSide/K14/RawRowStretch.lean), CALLED: 135 parts · 0
· 1930; 113 parts · 2696 · 1363. segmentZero_closed THERE IS SUCH A BOOK: NO PREMISE: with
bookWhole_returns_written (AtFullSide/K14/BookWholeWritten.lean). segBlocksW, blocks_free the three
blocks as three stretches of rowZeroW: the frame's wantsFree
(Johnson/Desc/ProofFile/Honest/BookEntries.lean) accepts them: each within the 8191 free entries;
no two meet. twoSpenders_oneCoin, twoSpenders_share THE SIXTH TWIN: two spenders lent one coin
(K4's start moved into K3's stretch):
with 1929 for 1930 wantsFree REJECTS; and the frame's Ahead.shares
(Johnson/Desc/ProofFile/Honest/Frame.lean) says of the two entries: a coin in common: yes at 1929,
no at 1930.

THE NUMBER 2695 STANDS IN NO BLOCK (1930 + 765 = 2695; the next begins at 2696): after a merge the
mask row has a gap: the merge's end value's own number (BookMergeStretch.lean's head).

KIN. At all stretches of the written list another house has, as rows: within the free entries and
apart (rawWants_within, rawWants_apart: AtFullSide/K14/RawWantsApart.lean) and no coin in common
(rawWants_once_parts: AtFullSide/K14/RawWantsOnce.lean): blocks_free SAYS NOTHING NEW OF THE BOOK:
it is the honest side of the twin. K3's places: that house's k3Fits_closed
(AtFullSide/K14/RawK3Fits.lean) has the lookups' three tests there, stage by stage; k3RowAt2 |
k3RowAt7 have the row as one stretch.

Limits. segBlocksW's THREE ARE BLOCKS, NOT THE MAKER's OWN STRETCHES (163 · 16 · 141 of them, by a
probe): that the blocks are what the rows spend is k3RowAt2 · k4MergeRowAt · k3RowAt7. THAT ANY
DESCRIPTION BUT WP HAS THESE VALUES is not said; the sendings are found by labels that rest on one
print; THE MERGES ARE A GUESS (the limits of the files called). THE FULL SIZE ALONE. Evaluations in
Lean's kernel (decide +kernel): no compiled code; maxRecDepth is raised to 1000000 in front of them
(no lower number was tried). Nothing on a sender's text, on a run, or on what any coin is. Nothing
on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.MergeRowAtWritten
import AtFullSide.K14.RawRowStretch
import AtFullSide.K14.BookWholeWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest
open AtFullSide.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- Link 0's mask row as an owner, written. -/
def rowZeroW : MsgAt := ⟨maskRowRun, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨23214, 0⟩, 8191⟩

/-- It is the first member of rawRowsW. -/
theorem rowZeroW_written : rawRowsW.head? = some (0, rowZeroW) := by decide

set_option maxRecDepth 1000000 in
/-- **The test accepts K4's row.** -/
theorem k4RowOk :
    mergeRowOk ⟨1, some 0, 3, .K4⟩ 19 18 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 1930 765 0 1 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the first coin greater by one it rejects. -/
theorem k4RowOk_bent_start :
    mergeRowOk ⟨1, some 0, 3, .K4⟩ 19 18 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 1931 765 0 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- THE OWNER BENT: with the address of the segment's next sending of the kind K1 it rejects. -/
theorem k4RowOk_bent_owner :
    mergeRowOk ⟨1, some 0, 3, .K4⟩ 19 18 ⟨⟨1, some 0, 4, .K1⟩, 0⟩ 1930 765 0 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the part in front for the merge it rejects. -/
theorem k4RowOk_bent_merge :
    mergeRowOk ⟨1, some 0, 3, .K4⟩ 19 17 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 1930 765 0 1 = false := by
  decide +kernel

/-- **WHAT K4's ROW SPENDS IN WHATEVER BOOK bookWhole RETURNS AT WP.** -/
theorem k4MergeRowAt {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    ∃ es₁, rowEntries B ⟨1, some 0, 3, .K4⟩ 19 0 =
        es₁ ++ [(⟨⟨⟨1, some 0, 3, .K4⟩, 18⟩, "ends", rawIdxW, 0, 1⟩ : Want).entry] ∧
      oneStretch es₁ = some (⟨⟨1, some 0, 1, .K1⟩, 0⟩, 1930, 765) :=
  mergeRow_of_ok hB k4RowOk

set_option maxRecDepth 1000000 in
/-- Another house's test accepts K3's two rows. -/
theorem k3RowOk : rawRowOk ⟨1, some 0, 2, .K3⟩ 135 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 0 1930 = true ∧
    rawRowOk ⟨1, some 0, 7, .K3⟩ 113 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 2696 1363 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the first coin greater by one, at either, it rejects. -/
theorem k3RowOk_bent : rawRowOk ⟨1, some 0, 2, .K3⟩ 135 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 1 1930 = false ∧
    rawRowOk ⟨1, some 0, 7, .K3⟩ 113 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 2697 1363 = false := by
  decide +kernel

/-- What K3's row at piece 2 spends. -/
theorem k3RowAt2 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    oneStretch (rowEntries B ⟨1, some 0, 2, .K3⟩ 135 0) =
      some (⟨⟨1, some 0, 1, .K1⟩, 0⟩, 0, 1930) :=
  rawRowStretch_of_ok hB k3RowOk.1

/-- What K3's row at piece 7 spends. -/
theorem k3RowAt7 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    oneStretch (rowEntries B ⟨1, some 0, 7, .K3⟩ 113 0) =
      some (⟨⟨1, some 0, 1, .K1⟩, 0⟩, 2696, 1363) :=
  rawRowStretch_of_ok hB k3RowOk.2

/-- **THERE IS SUCH A BOOK: NO PREMISE.** -/
theorem segmentZero_closed :
    ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
        (mergesByName WP.first.blocksInOrder) = .ok B ∧
      oneStretch (rowEntries B ⟨1, some 0, 2, .K3⟩ 135 0) =
        some (⟨⟨1, some 0, 1, .K1⟩, 0⟩, 0, 1930) ∧
      (∃ es₁, rowEntries B ⟨1, some 0, 3, .K4⟩ 19 0 =
          es₁ ++ [(⟨⟨⟨1, some 0, 3, .K4⟩, 18⟩, "ends", rawIdxW, 0, 1⟩ : Want).entry] ∧
        oneStretch es₁ = some (⟨⟨1, some 0, 1, .K1⟩, 0⟩, 1930, 765)) ∧
      oneStretch (rowEntries B ⟨1, some 0, 7, .K3⟩ 113 0) =
        some (⟨⟨1, some 0, 1, .K1⟩, 0⟩, 2696, 1363) := by
  obtain ⟨B, hB⟩ := bookWhole_returns_written
  exact ⟨B, hB, k3RowAt2 hB, k4MergeRowAt hB, k3RowAt7 hB⟩

/-- The three blocks as stretches of link 0's mask row. s: where K4's begins. -/
def segBlocksW (s : Nat) : List Want :=
  [⟨⟨⟨1, some 0, 2, .K3⟩, 0⟩, "block", rowZeroW, 0, 1930⟩,
    ⟨⟨⟨1, some 0, 3, .K4⟩, 0⟩, "block", rowZeroW, s, 765⟩,
    ⟨⟨⟨1, some 0, 7, .K3⟩, 0⟩, "block", rowZeroW, 2696, 1363⟩]

/-- The frame's test accepts the three blocks: within the free entries; no two meet. -/
theorem blocks_free : wantsFree (segBlocksW 1930) = true := by decide +kernel

/-- **THE SIXTH TWIN: TWO SPENDERS LENT ONE COIN**: K4's start moved into K3's stretch: the frame's
test rejects. -/
theorem twoSpenders_oneCoin : wantsFree (segBlocksW 1929) = false := by decide +kernel

/-- The same by the two entries: a coin in common: yes at 1929; no at 1930. -/
theorem twoSpenders_share :
    ((segBlocksW 1929).map (·.entry)).head?.bind (fun a =>
      ((segBlocksW 1929).map (·.entry))[1]?.map fun b => a.shares b) = some true ∧
    ((segBlocksW 1930).map (·.entry)).head?.bind (fun a =>
      ((segBlocksW 1930).map (·.entry))[1]?.map fun b => a.shares b) = some false := by
  decide +kernel

end AtFullSide.K1

#print axioms AtFullSide.K1.rowZeroW
#print axioms AtFullSide.K1.rowZeroW_written
#print axioms AtFullSide.K1.k4RowOk
#print axioms AtFullSide.K1.k4RowOk_bent_start
#print axioms AtFullSide.K1.k4RowOk_bent_owner
#print axioms AtFullSide.K1.k4RowOk_bent_merge
#print axioms AtFullSide.K1.k4MergeRowAt
#print axioms AtFullSide.K1.k3RowOk
#print axioms AtFullSide.K1.k3RowOk_bent
#print axioms AtFullSide.K1.k3RowAt2
#print axioms AtFullSide.K1.k3RowAt7
#print axioms AtFullSide.K1.segmentZero_closed
#print axioms AtFullSide.K1.segBlocksW
#print axioms AtFullSide.K1.blocks_free
#print axioms AtFullSide.K1.twoSpenders_oneCoin
#print axioms AtFullSide.K1.twoSpenders_share

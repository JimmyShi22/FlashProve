-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawFactsWritten.lean: AT THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND THE LIBRARY's WRITTEN LIST OF THE FIRST CHAIN's SENDINGS
(proofSendsFull.1, Johnson/G/SendsWritten.lean): FOUR CLOSED FACTS ON THE FRAME's MAKERS OF THE BOOK
OF COINS, EACH BY AN EVALUATION IN LEAN's KERNEL: the index-mask message as an owner is a written
value; the first chain's links are 0 to 24; each link's mask row as an owner is a written value;
behind each of 26 written rounds a fold and a sending stand in the first chain. Five definitions
(four written values or terms, one test with code); statements with their proofs.

  rawLater        the second chain's rounds, as the makers are handed them (an abbreviation)
  rawIdxW, rawIdx_written   **ownerOf (Honest/BookEntries.lean) at "link 0, moment 0" and
                  isIndexMaskMsg yields rawIdxW**
  rawLinks_written   **the numbers place.link of the first chain's sub-protocols, without repeats,
                  are 0, …, 24**
  rawRowsW, rawRowsAre, rawRows_all, rawRows_written   **for each (n, m) of the 25 written pairs:
                  ownerOf at the label "link n, moment 0", as linksWants (Honest/BookAll.lean)
                  spells it, and isMaskRowMsg yields m**: one evaluation over all 25
  rawRows_some    so at every link of the first chain that owner is there: where it is lacking, and
                  there alone, linksWants returns nothing
  rawRowsW_numbers, rawRowsW_home, rawRowsW_owners, rawRowsW_free, rawRowsW_not_idx   of the 25
                  written values: their numbers are 0, …, 24; each one's owner stands at a place of
                  its own link; the 25 owners are all different; each has 8,191 free entries; none
                  is rawIdxW. THE LAST FOUR ARE CALLED BY NOTHING TODAY: they are premises of a law
                  on the makers of the stretches that is not typed
  rawFreshRounds, rawBehind_all, rawBehind_written   **behindFold (Honest/BookCarry.lean) in the
                  first chain's plan alone is some at each of the 26 written rounds**: one
                  evaluation. The 26 are meant as the rounds of the sendings "link n, moment 0", n
                  from 0 to 25: each that sending's number in Johnson/G/SendsWritten.lean less one
  THAT EACH EVALUATION CAN FAIL: rawIdx_bent, rawRows_bent: with one written number turned by one
                  the same test rejects · rawRow25_none: at the label "link 25, moment 0", which
                  the written list has, ownerOf with isMaskRowMsg yields none: that sending has no
                  mask row; no sub-protocol has the link 25 · rawLinks_not26 · rawBehind_none:
                  behind the round 48,290 (the chain's last sending) no fold with a sending behind
                  it stands in the first chain

OPTIONS ARE RAISED, each in front of one theorem: maxRecDepth to 1000000 (no lower number was
tried), and maxHeartbeats is lifted. Why (a reading, not shown): the first chain has 48,293 rounds;
the makers take a round's number off a walk along all rounds in front of it. In a trial the
evaluation at the link 24 ran out of the default 200,000 heartbeats; with these lifted, in a file of
the main library, Lean ended with "Stack overflow detected"; in this side library, whose files Lean
compiles with a larger stack (lakefile.toml), it went through. No other option is raised.
What is assumed. Nothing.
What is not claimed. THAT ANY DESCRIPTION BUT WP HAS THESE VALUES (WP.lean's own limit: that any
description has its rounds or its cut is no theorem there: its values were printed by Lean's
evaluator). EVERY FACT HERE FINDS A SENDING BY ITS LABEL, AND THE WRITTEN SENDINGS' LABELS REST ON
ONE PRINT of Lean's evaluator and on one test by it at every build (Johnson/G/SendsWritten.lean's
own limit). THAT rawFreshRounds ARE THE ROUNDS OF THE LINKS' FRESH TABLES: no theorem here says so.
That linksWants, spendingBook or bookRaw returns. That wantsFree accepts. Nothing on the book's own
tests. Counts and addresses: nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.AtFull.ProofPlan.WP
import Johnson.G.SendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The second chain's rounds: what the makers at the first chain are handed as "later". -/
abbrev rawLater : List Fmt.DeclaredRound := WP.second.blocksInOrder.flatMap (·.rounds)

/-! ## 1 The index-mask message -/

/-- The index-mask message as an owner, written. -/
def rawIdxW : MsgAt := ⟨indexMaskRun, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8647⟩, 255⟩

set_option maxRecDepth 1000000 in
/-- **The index-mask message as an owner, at WP and the written sendings.** -/
theorem rawIdx_written : ownerOf indexMaskRun WP.first.blocksInOrder proofSendsFull.1 rawLater
    "link 0, moment 0" isIndexMaskMsg = some rawIdxW := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluation can fail: with the free entries greater by one the test rejects. -/
theorem rawIdx_bent : decide (ownerOf indexMaskRun WP.first.blocksInOrder proofSendsFull.1 rawLater
    "link 0, moment 0" isIndexMaskMsg = some { rawIdxW with free := rawIdxW.free + 1 }) =
      false := by
  decide +kernel

/-! ## 2 The links -/

set_option maxRecDepth 1000000 in
/-- **The first chain's links are 0, …, 24.** -/
theorem rawLinks_written :
    (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups = List.range 25 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- They are not 0, …, 25, though the written sendings have a label "link 25, moment 0". -/
theorem rawLinks_not26 :
    decide ((WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups = List.range 26) = false := by
  decide +kernel

/-! ## 3 The 25 mask rows -/

/-- The links' mask rows as owners, written: each with its link's number. -/
def rawRowsW : List (Nat × MsgAt) := [
  (0, ⟨maskRowRun, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨23214, 0⟩, 8191⟩),
  (1, ⟨maskRowRun, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (2, ⟨maskRowRun, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (3, ⟨maskRowRun, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (4, ⟨maskRowRun, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (5, ⟨maskRowRun, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (6, ⟨maskRowRun, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (7, ⟨maskRowRun, ⟨⟨1, some 7, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (8, ⟨maskRowRun, ⟨⟨1, some 8, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (9, ⟨maskRowRun, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (10, ⟨maskRowRun, ⟨⟨1, some 10, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (11, ⟨maskRowRun, ⟨⟨1, some 11, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (12, ⟨maskRowRun, ⟨⟨1, some 12, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (13, ⟨maskRowRun, ⟨⟨1, some 13, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (14, ⟨maskRowRun, ⟨⟨1, some 14, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (15, ⟨maskRowRun, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (16, ⟨maskRowRun, ⟨⟨1, some 16, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (17, ⟨maskRowRun, ⟨⟨1, some 17, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (18, ⟨maskRowRun, ⟨⟨1, some 18, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (19, ⟨maskRowRun, ⟨⟨1, some 19, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (20, ⟨maskRowRun, ⟨⟨1, some 20, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (21, ⟨maskRowRun, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (22, ⟨maskRowRun, ⟨⟨1, some 22, 1, .K2⟩, 0⟩, ⟨23436, 439⟩, 8191⟩),
  (23, ⟨maskRowRun, ⟨⟨1, some 23, 1, .K2⟩, 0⟩, ⟨11832, 439⟩, 8191⟩),
  (24, ⟨maskRowRun, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 8191⟩)]

/-- The test that is evaluated: at each pair the maker yields the written value. -/
def rawRowsAre (l : List (Nat × MsgAt)) : Bool :=
  l.all fun x => decide (ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
    s!"link {x.1}, moment 0" isMaskRowMsg = some x.2)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **All 25, in one evaluation.** -/
theorem rawRows_all : rawRowsAre rawRowsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The evaluation can fail: with the last row's free entries smaller by one the test rejects. -/
theorem rawRows_bent : rawRowsAre (rawRowsW.map fun x =>
    if x.1 = 24 then (x.1, { x.2 with free := x.2.free - 1 }) else x) = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At the label "link 25, moment 0" there is no mask row. -/
theorem rawRow25_none : ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
    s!"link {25}, moment 0" isMaskRowMsg = none := by decide +kernel

/-- **Each link's mask row as an owner is the written value.** -/
theorem rawRows_written : ∀ x ∈ rawRowsW, ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
    s!"link {x.1}, moment 0" isMaskRowMsg = some x.2 :=
  fun x hx => of_decide_eq_true (List.all_eq_true.1 rawRows_all x hx)

/-- The written pairs' numbers are 0, …, 24. -/
theorem rawRowsW_numbers : rawRowsW.map (·.1) = List.range 25 := by decide

/-- **At every link of the first chain the mask row as an owner is there.** -/
theorem rawRows_some : ∀ n ∈ (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups,
    (ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      s!"link {n}, moment 0" isMaskRowMsg).isSome = true := by
  intro n hn
  rw [rawLinks_written, ← rawRowsW_numbers] at hn
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
  rw [rawRows_written x hx]
  rfl

/-- Each written row's owner stands at a place of its own link. -/
theorem rawRowsW_home : (rawRowsW.all fun x => x.2.owner.place.link == some x.1) = true := by decide

/-- The 25 owners are all different. -/
theorem rawRowsW_owners : (rawRowsW.map (·.2.owner)).Nodup := by decide

/-- Each written row has 8,191 free entries. -/
theorem rawRowsW_free : (rawRowsW.all fun x => x.2.free == 8191) = true := by decide

/-- No written row is the index-mask message. -/
theorem rawRowsW_not_idx : ∀ x ∈ rawRowsW, x.2 ≠ rawIdxW := by decide

/-! ## 4 Behind 26 rounds a fold and a sending stand in the first chain -/

/-- 26 rounds of the first chain, written. Meant: the rounds of the sendings "link n, moment 0", n
from 0 to 25: each that sending's number in Johnson/G/SendsWritten.lean less one; no theorem here
says so. -/
def rawFreshRounds : List Nat :=
  [0, 1980, 3859, 5837, 7716, 9694, 11573, 13551, 15430, 17408, 19287, 21265, 23144, 25122,
    27001, 28979, 30858, 32836, 34715, 36693, 38572, 40550, 42429, 44407, 46287, 48235]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **All 26, in one evaluation.** -/
theorem rawBehind_all :
    (rawFreshRounds.all fun i => (behindFold (planOf WP.first.blocksInOrder) i).isSome) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The evaluation can fail: behind the chain's last sending no fold with a sending behind it stands
in the first chain. -/
theorem rawBehind_none : behindFold (planOf WP.first.blocksInOrder) 48290 = none := by decide +kernel

/-- **Behind each of the written rounds: a fold, and a sending behind it, in the first chain's plan
alone.** -/
theorem rawBehind_written : ∀ i ∈ rawFreshRounds,
    (behindFold (planOf WP.first.blocksInOrder) i).isSome = true :=
  fun i hi => List.all_eq_true.1 rawBehind_all i hi

end AtFullSide.K14

#print axioms AtFullSide.K14.rawIdx_written
#print axioms AtFullSide.K14.rawIdx_bent
#print axioms AtFullSide.K14.rawLinks_written
#print axioms AtFullSide.K14.rawLinks_not26
#print axioms AtFullSide.K14.rawRows_all
#print axioms AtFullSide.K14.rawRows_bent
#print axioms AtFullSide.K14.rawRow25_none
#print axioms AtFullSide.K14.rawRows_written
#print axioms AtFullSide.K14.rawRowsW_numbers
#print axioms AtFullSide.K14.rawRows_some
#print axioms AtFullSide.K14.rawRowsW_home
#print axioms AtFullSide.K14.rawRowsW_owners
#print axioms AtFullSide.K14.rawRowsW_free
#print axioms AtFullSide.K14.rawRowsW_not_idx
#print axioms AtFullSide.K14.rawBehind_all
#print axioms AtFullSide.K14.rawBehind_none
#print axioms AtFullSide.K14.rawBehind_written

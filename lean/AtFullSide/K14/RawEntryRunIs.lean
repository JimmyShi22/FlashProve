-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawEntryRunIs.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName (Honest/BookWhole.lean) GUESSES:
WHATEVER BOOK bookWhole RETURNS THERE: THE PUBLIC TEST entryRunIs (Honest/Small/EntryRunIs.lean)
ACCEPTS THE ENTRIES BY WHICH THE PART 1 AT ⟨1, some 24, 9, K11⟩, THE PART 1 AT ⟨1, none, 3, K13⟩ AND
THE PARTS AT ⟨1, some 24, 4, K6⟩ SPEND COINS, POSITION BY POSITION, WITH WRITTEN OWNERS, STARTS AND
COUNTS. IMPLICATIONS: that bookWhole returns there is not shown here. No definition; statements with
their proofs; nothing is evaluated over the stretches here.

  rawEntryRunIsAtK11_sum, rawEntryRunIsAtK11_ends   **K11's part: at the position 0: owner
                  ⟨⟨1, some 24, 2, K2⟩, 0⟩, start ⟨23217, 3970⟩, count ⟨0, 38⟩; at 1: owner
                  ⟨⟨1, some 0, 1, K1⟩, 0⟩, start ⟨25848, 8659⟩, count ⟨0, 1⟩**
  rawEntryRunIsAtK13   **K13's part: at 0: ⟨⟨1, some 0, 1, K1⟩, 0⟩, ⟨25848, 8660⟩, ⟨0, 37⟩**
  rawEntryRunIsAtK6, rawEntryRunIsAtK6_ten   **K6's parts**: at every part j and position i: the
                  member number i of the written list's members with the part j; and the ten
                  written out
  entryRunIs_beyond_list, rawEntryRunIsAtK11_no_third, rawEntryRunIsAtK13_no_second   beyond a
                  list's length the test rejects whatever it is asked (kin: entryRunIs_gives,
                  Honest/Small/EntryRunIs.lean: a yes at i gives a member at i): K11's part has no
                  third such entry, K13's no second

Each yes is one call of entryRunIs_of_list (Honest/Small/EntryRunIsOfList.lean) at an equation of
lists: rawSpentAtK11_written, rawSpentAtK13_written (AtFullSide/K14/RawSpentWritten.lean),
rawSpentAtK6 (AtFullSide/K14/RawSpentAtPlaces.lean).
No option is raised. The file stands in this side library because its imports do.
What is assumed. Nothing.
What is not claimed. THAT bookWhole RETURNS AT WP. The test reads an entry's owner, start and count:
not its name, nor its spender. Nothing on entries that carry. THAT ANY DESCRIPTION BUT WP HAS THESE
VALUES; the sendings are found by labels that rest on one print; the merges are a guess (the limits
of AtFullSide/K14/RawSpentWritten.lean, all). Numbers and addresses: nothing on soundness,
completeness or hiding.
-/
import AtFullSide.K14.RawSpentAtPlaces
import Johnson.Desc.ProofFile.Honest.Small.EntryRunIsOfList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **K11's part, the position 0.** -/
theorem rawEntryRunIsAtK11_sum {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨⟨1, some 24, 9, .K11⟩, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩ ⟨23217, 3970⟩
      ⟨0, 38⟩ = true :=
  entryRunIs_of_list (rawSpentAtK11_written hB) rfl

/-- **K11's part, the position 1.** -/
theorem rawEntryRunIsAtK11_ends {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨⟨1, some 24, 9, .K11⟩, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨25848, 8659⟩
      ⟨0, 1⟩ = true :=
  entryRunIs_of_list (rawSpentAtK11_written hB) rfl

/-- **K13's part, the position 0.** -/
theorem rawEntryRunIsAtK13 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨⟨1, none, 3, .K13⟩, 1⟩) 0 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨25848, 8660⟩
      ⟨0, 37⟩ = true :=
  entryRunIs_of_list (rawSpentAtK13_written hB) rfl

/-- **K6's parts: at every part j and position i.** -/
theorem rawEntryRunIsAtK6 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (j i : Nat)
    {x : Nat × String × Addr × Due × Nat × Nat}
    (hx : (rawK6W.filter fun y => y.1 == j)[i]? = some x) :
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, j⟩) i x.2.2.1 (x.2.2.2.1.plus ⟨0, x.2.2.2.2.1⟩)
      ⟨0, x.2.2.2.2.2⟩ = true :=
  entryRunIs_of_list (rawSpentAtK6 hB j) (by rw [List.getElem?_map, hx]; rfl)

/-- **K6's ten, written out.** -/
theorem rawEntryRunIsAtK6_ten {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2434⟩ ⟨0, 9⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 2⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2443⟩ ⟨0, 49⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 2⟩) 1 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2492⟩ ⟨0, 2⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 4⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2494⟩ ⟨0, 7⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 5⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2501⟩ ⟨0, 24⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 5⟩) 1 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2525⟩ ⟨0, 4⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 6⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2529⟩ ⟨0, 24⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 6⟩) 1 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2553⟩ ⟨0, 2⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 7⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2555⟩ ⟨0, 50⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 7⟩) 1 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2605⟩ ⟨0, 2⟩ = true :=
  ⟨rawEntryRunIsAtK6 hB 1 0 rfl,
    rawEntryRunIsAtK6 hB 2 0 rfl,
    rawEntryRunIsAtK6 hB 2 1 rfl,
    rawEntryRunIsAtK6 hB 4 0 rfl,
    rawEntryRunIsAtK6 hB 5 0 rfl,
    rawEntryRunIsAtK6 hB 5 1 rfl,
    rawEntryRunIsAtK6 hB 6 0 rfl,
    rawEntryRunIsAtK6 hB 6 1 rfl,
    rawEntryRunIsAtK6 hB 7 0 rfl,
    rawEntryRunIsAtK6 hB 7 1 rfl⟩

/-- Beyond the length of the list of triples the test rejects, whatever it is asked. -/
theorem entryRunIs_beyond_list {es : List Ahead} {L : List (Addr × Due × Due)}
    (hL : (es.map fun e => (e.owner, e.start, e.count)) = L) {i : Nat} (hi : L.length ≤ i)
    (o : Addr) (st ct : Due) : entryRunIs es i o st ct = false := by
  have hl : es.length = L.length := by rw [← hL, List.length_map]
  unfold entryRunIs
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-- K11's part has no third entry by which it spends. -/
theorem rawEntryRunIsAtK11_no_third {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1
                  proofSendsFull.2.1 proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (o : Addr)
    (st ct : Due) :
    entryRunIs (spentE B ⟨⟨1, some 24, 9, .K11⟩, 1⟩) 2 o st ct = false :=
  entryRunIs_beyond_list (rawSpentAtK11_written hB) (Nat.le_refl 2) o st ct

/-- K13's part has no second. -/
theorem rawEntryRunIsAtK13_no_second {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1
                  proofSendsFull.2.1 proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (o : Addr)
    (st ct : Due) :
    entryRunIs (spentE B ⟨⟨1, none, 3, .K13⟩, 1⟩) 1 o st ct = false :=
  entryRunIs_beyond_list (rawSpentAtK13_written hB) (Nat.le_refl 1) o st ct

end AtFullSide.K14

#print axioms AtFullSide.K14.rawEntryRunIsAtK11_sum
#print axioms AtFullSide.K14.rawEntryRunIsAtK11_ends
#print axioms AtFullSide.K14.rawEntryRunIsAtK13
#print axioms AtFullSide.K14.rawEntryRunIsAtK6
#print axioms AtFullSide.K14.rawEntryRunIsAtK6_ten
#print axioms AtFullSide.K14.entryRunIs_beyond_list
#print axioms AtFullSide.K14.rawEntryRunIsAtK11_no_third
#print axioms AtFullSide.K14.rawEntryRunIsAtK13_no_second

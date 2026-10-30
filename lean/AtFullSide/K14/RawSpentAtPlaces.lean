-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawSpentAtPlaces.lean: AT THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName
(Honest/BookWhole.lean) GUESSES: OF THE STRETCHES THAT spendingBook ASKS wantsFree ABOUT, THOSE
WHOSE SPENDER STANDS AT THE PLACE ⟨1, some 24, 4, K6⟩ ARE TEN, AT ⟨1, some 24, 9, K11⟩ TWO, AT ⟨1,
none, 3, K13⟩ ONE, WITH WRITTEN PARTS, USES, OWNERS, BASES, NUMBERS AND COUNTS: each by one
evaluation in Lean's kernel; AND WHATEVER BOOK bookWhole RETURNS THERE: AT EVERY PART OF THESE THREE
PLACES ALL THE ENTRIES BY WHICH THE PART SPENDS COINS ARE THESE STRETCHES', AS OWNER, START AND
COUNT. The second half: IMPLICATIONS: that bookWhole returns there is not shown here. Five
definitions, one with code, four written lists; statements with their proofs.

  rawWantsAtPlace p   of the stretches a.1 ++ b.1, in spendingBook's own terms: those whose spender
                  stands at the place p, in the list's order, each as part, use, owner, base,
                  number, count
  rawK6W, rawK11W, rawK13W; rawWantsAtK6_written, rawWantsAtK11Place_written,
  rawWantsAtK13Place_written   **the ten, the two, the one**: so a part that no member names has no
                  stretch: at K11's and K13's places the part 0; at K6's the parts 0 and 3; at each
                  every part beyond. rawWantsAtK6_bent: the evaluation can fail
  rawWantsAt_of_place   from the stretches at a place to those of one of its parts (rawWantsAt,
                  AtFullSide/K14/RawWantsAtSpenders.lean): a filter by the part
  rawNoFoldAtK6   K6's place holds no round named "FOLD epsilon": an evaluation
  rawSpent_of_place   **the bridge at a place**: at every part j: what the part spends in the book,
                  as owner, start, count, is the written list's members with the part j
  rawSpentAtK6, rawSpentAtK11Place, rawSpentAtK13Place   **that at the three places, at every j**
  rawSpentAtK6_table   K6's parts 0 to 7, written out

OPTIONS ARE RAISED in front of the evaluations: maxRecDepth to 1000000 (no lower number was tried);
in front of the four over the stretches maxHeartbeats is lifted too, and synthInstance.maxSize is
1024: at its default Lean does not find that equality of lists of these six-fold tuples can be
decided (seen; at 1024 it does). This side library's files Lean compiles with a larger stack
(lakefile.toml).
Kin. rawWantsAtK11_written and rawWantsAtK13_written (AtFullSide/K14/RawWantsAtSpenders.lean) have
the part 1 of two other places; rawSpentAtK11_written and rawSpentAtK13_written
(AtFullSide/K14/RawSpentWritten.lean) have these on the book.
What is assumed. Nothing.
What is not claimed. THAT bookWhole RETURNS AT WP. An entry's name. Nothing on entries that carry.
THAT ANY DESCRIPTION BUT WP HAS THESE VALUES; the sendings are found by labels that rest on one
print; the merges are a guess (the limits of AtFullSide/K14/RawSpentWritten.lean, all). Numbers and
addresses: nothing on soundness, completeness or hiding.
-/
import AtFullSide.K14.RawSpentWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- Of the stretches that spendingBook asks wantsFree about: those whose spender stands at the place
p, in the list's order: part, use, owner, base, number, count. Nothing where linksWants rejects. -/
def rawWantsAtPlace (p : Place) : Option (List (Nat × String × Addr × Due × Nat × Nat)) :=
  match linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW (mergesByName WP.first.blocksInOrder).ends
      (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 with
  | .ok a => some (((a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
        fun w => w.spender.place == p).map fun w =>
          (w.spender.part, w.use, w.msg.owner, w.msg.base, w.number, w.count))
  | .error _ => none

/-- The ten stretches at K6's place in link 24, written. -/
def rawK6W : List (Nat × String × Addr × Due × Nat × Nat) :=
  [(1, "scalars", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 1995, 9),
    (2, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2004, 49),
    (2, "ends", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2053, 2),
    (4, "scalars", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2055, 7),
    (5, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2062, 24),
    (5, "ends", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2086, 4),
    (6, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2090, 24),
    (6, "ends", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2114, 2),
    (7, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2116, 50),
    (7, "ends", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2166, 2)]

/-- The same with the second stretch's number greater by one. -/
def rawK6Bent : List (Nat × String × Addr × Due × Nat × Nat) :=
  [(1, "scalars", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 1995, 9),
    (2, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2005, 49),
    (2, "ends", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2053, 2),
    (4, "scalars", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2055, 7),
    (5, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2062, 24),
    (5, "ends", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2086, 4),
    (6, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2090, 24),
    (6, "ends", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2114, 2),
    (7, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2116, 50),
    (7, "ends", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 2166, 2)]

/-- The two stretches at K11's place in link 24, written. -/
def rawK11W : List (Nat × String × Addr × Due × Nat × Nat) :=
  [(1, "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 3531, 38),
    (1, "ends", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8647⟩, 12, 1)]

/-- The one stretch at K13's place, written. -/
def rawK13W : List (Nat × String × Addr × Due × Nat × Nat) :=
  [(1, "sum", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8647⟩, 13, 37)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 1024 in
/-- **The ten stretches at the place ⟨1, some 24, 4, K6⟩.** -/
theorem rawWantsAtK6_written : rawWantsAtPlace ⟨1, some 24, 4, .K6⟩ = some rawK6W := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 1024 in
/-- The evaluation can fail: with the second number greater by one the comparison rejects. -/
theorem rawWantsAtK6_bent :
    decide (rawWantsAtPlace ⟨1, some 24, 4, .K6⟩ = some rawK6Bent) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 1024 in
/-- **The two stretches at the place ⟨1, some 24, 9, K11⟩.** -/
theorem rawWantsAtK11Place_written : rawWantsAtPlace ⟨1, some 24, 9, .K11⟩ = some rawK11W := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 1024 in
/-- **The one stretch at the place ⟨1, none, 3, K13⟩.** -/
theorem rawWantsAtK13Place_written : rawWantsAtPlace ⟨1, none, 3, .K13⟩ = some rawK13W := by
  decide +kernel

/-- An address is its place and its part. (The frame has the same sentence with the two clauses the
other way round: addr_beq, Honest/Law/RunAt.lean; it does not lie beneath this file.) -/
theorem spender_beq (sp p : Place) (sj j : Nat) :
    ((⟨sp, sj⟩ : Addr) == ⟨p, j⟩) = ((sj == j) && (sp == p)) := by
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq, Bool.and_eq_true, Addr.mk.injEq]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **From the stretches at a place to those of one of its parts.** -/
theorem rawWantsAt_of_place {p : Place} {L : List (Nat × String × Addr × Due × Nat × Nat)}
    (h : rawWantsAtPlace p = some L) (j : Nat) :
    rawWantsAt ⟨p, j⟩ = some ((L.filter fun x => x.1 == j).map (·.2)) := by
  unfold rawWantsAtPlace at h
  unfold rawWantsAt
  cases hl : linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
      (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 with
  | error e =>
    rw [hl] at h
    cases h
  | ok a =>
    rw [hl] at h
    obtain rfl := Option.some.inj h
    refine congrArg some ?_
    rw [List.filter_map, List.map_map, List.filter_filter]
    refine congrArg₂ List.map rfl (List.filter_congr fun w _ => ?_)
    exact spender_beq w.spender.place p w.spender.part j

set_option maxRecDepth 1000000 in
/-- K6's place holds no round named "FOLD epsilon". -/
theorem rawNoFoldAtK6 : rawNoFoldAt ⟨1, some 24, 4, .K6⟩ = true := by decide +kernel

/-- **THE BRIDGE AT A PLACE: WHATEVER BOOK bookWhole RETURNS AT WP: AT EVERY PART j.** -/
theorem rawSpent_of_place {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) {p : Place}
    (hp : rawNoFoldAt p = true) {L : List (Nat × String × Addr × Due × Nat × Nat)}
    (hL : rawWantsAtPlace p = some L) (j : Nat) :
    (spentE B ⟨p, j⟩).map (fun e => (e.owner, e.start, e.count)) =
      (L.filter fun x => x.1 == j).map fun x =>
        (x.2.2.1, x.2.2.2.1.plus ⟨0, x.2.2.2.2.1⟩, (⟨0, x.2.2.2.2.2⟩ : Due)) := by
  rw [rawSpent_of_wantsAt hB hp j (rawWantsAt_of_place hL j), List.map_map]
  rfl

/-- **ALL THAT EACH PART OF K6's PLACE SPENDS.** -/
theorem rawSpentAtK6 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (j : Nat) :
    (spentE B ⟨⟨1, some 24, 4, .K6⟩, j⟩).map (fun e => (e.owner, e.start, e.count)) =
      (rawK6W.filter fun x => x.1 == j).map fun x =>
        (x.2.2.1, x.2.2.2.1.plus ⟨0, x.2.2.2.2.1⟩, (⟨0, x.2.2.2.2.2⟩ : Due)) :=
  rawSpent_of_place hB rawNoFoldAtK6 rawWantsAtK6_written j

/-- **ALL THAT EACH PART OF K11's PLACE SPENDS.** -/
theorem rawSpentAtK11Place {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (j : Nat) :
    (spentE B ⟨⟨1, some 24, 9, .K11⟩, j⟩).map (fun e => (e.owner, e.start, e.count)) =
      (rawK11W.filter fun x => x.1 == j).map fun x =>
        (x.2.2.1, x.2.2.2.1.plus ⟨0, x.2.2.2.2.1⟩, (⟨0, x.2.2.2.2.2⟩ : Due)) :=
  rawSpent_of_place hB rawNoFold_written.1 rawWantsAtK11Place_written j

/-- **ALL THAT EACH PART OF K13's PLACE SPENDS.** -/
theorem rawSpentAtK13Place {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (j : Nat) :
    (spentE B ⟨⟨1, none, 3, .K13⟩, j⟩).map (fun e => (e.owner, e.start, e.count)) =
      (rawK13W.filter fun x => x.1 == j).map fun x =>
        (x.2.2.1, x.2.2.2.1.plus ⟨0, x.2.2.2.2.1⟩, (⟨0, x.2.2.2.2.2⟩ : Due)) :=
  rawSpent_of_place hB rawNoFold_written.2 rawWantsAtK13Place_written j

/-- K6's parts 0 to 7, written out. -/
theorem rawSpentAtK6_table : (List.range 8).map (fun j => (rawK6W.filter fun x => x.1 == j).map
      fun x => (x.2.2.1, x.2.2.2.1.plus ⟨0, x.2.2.2.2.1⟩, (⟨0, x.2.2.2.2.2⟩ : Due))) =
    [[], [(⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2434⟩, ⟨0, 9⟩)],
      [(⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2443⟩, ⟨0, 49⟩),
        (⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2492⟩, ⟨0, 2⟩)],
      [], [(⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2494⟩, ⟨0, 7⟩)],
      [(⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2501⟩, ⟨0, 24⟩),
        (⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2525⟩, ⟨0, 4⟩)],
      [(⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2529⟩, ⟨0, 24⟩),
        (⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2553⟩, ⟨0, 2⟩)],
      [(⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2555⟩, ⟨0, 50⟩),
        (⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 2605⟩, ⟨0, 2⟩)]] := by
  decide

end AtFullSide.K14

#print axioms AtFullSide.K14.rawWantsAtK6_written
#print axioms AtFullSide.K14.rawWantsAtK6_bent
#print axioms AtFullSide.K14.rawWantsAtK11Place_written
#print axioms AtFullSide.K14.rawWantsAtK13Place_written
#print axioms AtFullSide.K14.spender_beq
#print axioms AtFullSide.K14.rawWantsAt_of_place
#print axioms AtFullSide.K14.rawNoFoldAtK6
#print axioms AtFullSide.K14.rawSpent_of_place
#print axioms AtFullSide.K14.rawSpentAtK6
#print axioms AtFullSide.K14.rawSpentAtK11Place
#print axioms AtFullSide.K14.rawSpentAtK13Place
#print axioms AtFullSide.K14.rawSpentAtK6_table

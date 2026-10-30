-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawSpentWritten.lean: AT THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName
(Honest/BookWhole.lean) GUESSES: WHATEVER BOOK bookWhole RETURNS THERE: ALL THE ENTRIES BY WHICH THE
PART NUMBER 1 AT THE PLACE ⟨1, some 24, 9, K11⟩ SPENDS COINS ARE TWO, AND THOSE OF THE PART NUMBER 1
AT ⟨1, none, 3, K13⟩ ONE, WITH WRITTEN OWNERS, STARTS AND COUNTS. IMPLICATIONS: that bookWhole
returns there is not shown here. One definition with code; statements with their proofs.

  rawNoFoldAt p, rawNoFold_written   the first chain has a sub-protocol at the place p none of whose
                  rounds is named "FOLD epsilon": at these two places: an evaluation in Lean's
                  kernel. rawNoFold_bent: at a place that holds such a round, and at no place of
                  the chain, the test rejects: its no does not tell the one from the other
  rawNoFold_block   that, out of the Bool
  rawSpent_of_wantsAt   **the bridge, at every part of such a place**: the entries by which the part
                  spends (spentE, Honest/Law/Rule/Cell.lean), each as owner, start, count, are the
                  stretches of rawWantsAt (AtFullSide/K14/RawWantsAtSpenders.lean) there, each as
                  owner, base with the number added to its second number, ⟨0, count⟩: by the frame's
                  pick_whole (Honest/BookRowStretch.lean), the library's wp_placesOk
                  (Johnson/AtFull/ProofPlan/At/PlacesOk.lean), rawIdx_written and rawWantsAt_of_ok
  rawSpentAtK11_written   **K11's part: ⟨⟨1, some 24, 2, K2⟩, 0⟩, ⟨23217, 3970⟩, ⟨0, 38⟩; then
                  ⟨⟨1, some 0, 1, K1⟩, 0⟩, ⟨25848, 8659⟩, ⟨0, 1⟩**
  rawSpentAtK13_written   **K13's part: ⟨⟨1, some 0, 1, K1⟩, 0⟩, ⟨25848, 8660⟩, ⟨0, 37⟩**

One option is raised, in front of rawNoFold_written and rawNoFold_bent: maxRecDepth to 1000000 (no
lower number was tried). The file stands in this side library because its first import does; whether
its two evaluations want that library's larger stack (lakefile.toml) was not tried.
What is assumed. Nothing.
What is not claimed. THAT bookWhole RETURNS AT WP. AN ENTRY's NAME: rawWantsAt's tuples do not hold
the message's name, so of an entry these statements have owner, start and count (its spender and
that it spends are spentE's own). THE PART 0 OF THE TWO PLACES: AtFullSide/K14/RawSpentAtPlaces.lean
has every part. At a further place the bridge wants rawNoFoldAt there as well: an evaluation more.
Nothing on entries that carry. THAT ANY DESCRIPTION BUT WP HAS THESE VALUES; the sendings are found
by labels that rest on one print; the merges are a guess (the limits of
AtFullSide/K14/RawWantsAtSpenders.lean, all). Numbers and addresses: nothing on soundness,
completeness or hiding.
-/
import AtFullSide.K14.RawWantsAtSpenders
import Johnson.Desc.ProofFile.Honest.BookRowStretch
import Johnson.AtFull.ProofPlan.At.PlacesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The first chain has a sub-protocol at the place p none of whose rounds is named
"FOLD epsilon". -/
def rawNoFoldAt (p : Place) : Bool :=
  WP.first.blocksInOrder.any fun b => b.place == p && b.rounds.all fun r => r.entry.name != "FOLD epsilon"

set_option maxRecDepth 1000000 in
/-- At K11's place in link 24 and at K13's place. -/
theorem rawNoFold_written : rawNoFoldAt ⟨1, some 24, 9, .K11⟩ = true ∧
    rawNoFoldAt ⟨1, none, 3, .K13⟩ = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can reject: at a place of link 24 that holds such a round; and at no place of the
chain. -/
theorem rawNoFold_bent : rawNoFoldAt ⟨1, some 24, 13, .K10⟩ = false ∧
    rawNoFoldAt ⟨1, some 24, 99, .K10⟩ = false := by decide +kernel

/-- Out of the Bool. -/
theorem rawNoFold_block {p : Place} (h : rawNoFoldAt p = true) :
    ∃ b ∈ WP.first.blocksInOrder, b.place = p ∧ ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon" := by
  unfold rawNoFoldAt at h
  obtain ⟨b, hb, h1⟩ := List.any_eq_true.1 h
  obtain ⟨h2, h3⟩ := Bool.and_eq_true_iff.1 h1
  exact ⟨b, hb, beq_iff_eq.1 h2, fun r hr => bne_iff_ne.1 (List.all_eq_true.1 h3 r hr)⟩

/-- **THE BRIDGE: WHATEVER BOOK bookWhole RETURNS AT WP: WHAT A PART OF SUCH A PLACE SPENDS IS ITS
STRETCHES**, each as owner, start, count. -/
theorem rawSpent_of_wantsAt {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) {p : Place}
    (hp : rawNoFoldAt p = true) (j : Nat) {L : List (String × Addr × Due × Nat × Nat)}
    (hL : rawWantsAt ⟨p, j⟩ = some L) :
    (spentE B ⟨p, j⟩).map (fun e => (e.owner, e.start, e.count)) =
      L.map fun x => (x.2.1, x.2.2.1.plus ⟨0, x.2.2.2.1⟩, (⟨0, x.2.2.2.2⟩ : Due)) := by
  obtain ⟨b, hb, rfl, hF⟩ := rawNoFold_block hp
  obtain ⟨idx, a, hidx, ha, -, hpick⟩ := pick_whole hB P2Law.ProofPlan.wp_placesOk hb hF
  obtain rfl : rawIdxW = idx := Option.some.inj (rawIdx_written.symm.trans hidx)
  have hL' := Option.some.inj ((rawWantsAt_of_ok ha ⟨b.place, j⟩).symm.trans hL)
  have hs : spentE B ⟨b.place, j⟩ = BookRow.pick ⟨b.place, j⟩ B.ahead := rfl
  rw [hs, hpick j, ← hL', List.map_map, List.map_map]
  rfl

/-- **ALL THAT K11's PART SPENDS IN WHATEVER BOOK bookWhole RETURNS AT WP.** -/
theorem rawSpentAtK11_written {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    (spentE B ⟨⟨1, some 24, 9, .K11⟩, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 3970⟩, ⟨0, 38⟩),
        (⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8659⟩, ⟨0, 1⟩)] :=
  rawSpent_of_wantsAt hB rawNoFold_written.1 1 rawWantsAtK11_written

/-- **ALL THAT K13's PART SPENDS THERE.** -/
theorem rawSpentAtK13_written {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    (spentE B ⟨⟨1, none, 3, .K13⟩, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8660⟩, ⟨0, 37⟩)] :=
  rawSpent_of_wantsAt hB rawNoFold_written.2 1 rawWantsAtK13_written

end AtFullSide.K14

#print axioms AtFullSide.K14.rawNoFold_written
#print axioms AtFullSide.K14.rawNoFold_bent
#print axioms AtFullSide.K14.rawNoFold_block
#print axioms AtFullSide.K14.rawSpent_of_wantsAt
#print axioms AtFullSide.K14.rawSpentAtK11_written
#print axioms AtFullSide.K14.rawSpentAtK13_written

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawRowStretch.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName (Honest/BookWhole.lean) GUESSES:
WHATEVER BOOK bookWhole RETURNS THERE: WHAT THE ROW AT A PLACE OF A SEGMENT SPENDS IS ONE STRETCH
(oneStretch, rowEntries: Honest/BookStretch.lean) WITH A WRITTEN OWNER, FIRST COIN AND COUNT,
WHEREVER ONE PUBLIC TEST WITH CODE ACCEPTS THE PLACE WITH THESE NUMBERS; and the test accepts at
written tables of places: by evaluations in Lean's kernel. IMPLICATIONS: that bookWhole returns
there is not shown here. Four definitions, two with code, two written tables; statements with their
proofs.

  rawRowOk p n o st ct   **the test**: the first chain has a sub-protocol at the place p, of a link
                  l: none of its parts is among the merges' ends; none of its rounds is named
                  "FOLD epsilon"; planParts lays n parts for it; their own scalars add up to ct,
                  which is not 0; and rawRowsW (AtFullSide/K14/RawFactsWritten.lean) has at l a mask
                  row with the owner o, whose entries begin, in the second number, at st less the
                  own scalars of the segment's parts in front of p. It reads the description, the
                  merges and the written rows: NOT the stretches
  rawRowStretch_of_ok   **where it accepts: oneStretch (rowEntries B p n 0) = some (o, st, ct)**: by
                  the frame's bookWhole_row_stretch (Honest/BookRowStretch.lean), the library's
                  wp_placesOk (Johnson/AtFull/ProofPlan/At/PlacesOk.lean) and rawRows_written
  rawTableOk T, rawRowStretch_of_table   the test at every row of a table (place, parts, owner,
                  first coin, count); where it accepts, the equation at every row
  rawK5RowsW, rawK5Rows_ok, rawRowStretchAtK5   **K5's twelve places ⟨1, some l, 3, K5⟩, l = 1, 3,
                  …, 23: 13 parts; owner ⟨⟨1, some l, 1, K2⟩, 0⟩; first coin 2251; count 1072**: ONE
                  EVALUATION IN LEAN's KERNEL FOR ALL TWELVE. rawK5Rows_bent: with the first row's
                  first coin greater by one the test rejects
  rawRowOkAtK6, rawRowStretchAtK6   **K6's place ⟨1, some 24, 4, K6⟩: 8 parts; owner
                  ⟨⟨1, some 24, 2, K2⟩, 0⟩; first coin 2434; count 173**. rawRowOkAtK6_bent

OPTIONS ARE RAISED in front of the four evaluations: maxRecDepth to 1000000 (no lower number was
tried); in front of the two over the table maxHeartbeats is lifted too. This side library's files
Lean compiles with a larger stack (lakefile.toml).
What is assumed. Nothing.
What is not claimed. THAT bookWhole RETURNS AT WP. What each part of a row spends
(AtFullSide/K14/RawSpentAtPlaces.lean has that at three places). An entry's name. Nothing on entries
that carry. A row one of whose parts lays its end values under the index-mask message, or that holds
a fold, or that has no scalar of its own: the test rejects it, and the frame's law says nothing of
it. THAT ANY DESCRIPTION BUT WP HAS THESE VALUES; the sendings are found by labels that rest on one
print; the merges are a guess. Numbers and addresses: nothing on soundness, completeness or hiding.
-/
import AtFullSide.K14.RawFactsWritten
import Johnson.Desc.ProofFile.Honest.BookRowStretch
import Johnson.AtFull.ProofPlan.At.PlacesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The test on a place, a number of parts, an owner, a first coin and a count.** -/
def rawRowOk (p : Place) (n : Nat) (o : Addr) (st ct : Nat) : Bool :=
  match p.link with
  | none => false
  | some l =>
    WP.first.blocksInOrder.any fun b => b.place == p &&
      ((planParts b).all fun q => !(mergesByName WP.first.blocksInOrder).ends.contains q.addr) &&
      (b.rounds.all fun r => r.entry.name != "FOLD epsilon") &&
      ownScalarsOf (planParts b) != 0 && (planParts b).length == n &&
      ownScalarsOf (planParts b) == ct &&
      rawRowsW.any fun x => x.1 == l && x.2.owner == o &&
        x.2.base.e + ownScalarsOf (partsInFront WP.first.blocksInOrder l p) == st

/-- **WHERE THE TEST ACCEPTS: WHATEVER BOOK bookWhole RETURNS AT WP: WHAT THE ROW SPENDS IS ONE
STRETCH.** -/
theorem rawRowStretch_of_ok {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) {p : Place} {n : Nat} {o : Addr}
    {st ct : Nat} (h : rawRowOk p n o st ct = true) :
    oneStretch (rowEntries B p n 0) = some (o, st, ct) := by
  unfold rawRowOk at h
  cases hl : p.link with
  | none =>
    rw [hl] at h
    cases h
  | some l =>
    rw [hl] at h
    obtain ⟨b, hb, h1⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
    obtain ⟨⟨⟨⟨⟨⟨rfl, hM⟩, hF⟩, hs⟩, hn⟩, hc⟩, hr⟩ := h1
    obtain ⟨x, hx, h2⟩ := List.any_eq_true.1 hr
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨⟨e1, e2⟩, e3⟩ := h2
    obtain ⟨row, hrow, hst⟩ := bookWhole_row_stretch hB P2Law.ProofPlan.wp_placesOk hb hl
      (fun q hq hm => by
        have := List.all_eq_true.1 hM q hq
        rw [List.contains_iff_mem.2 hm] at this
        cases this)
      (fun r hr' => bne_iff_ne.1 (List.all_eq_true.1 hF r hr')) hs
    have hw := rawRows_written x hx
    rw [e1] at hw
    obtain rfl : x.2 = row := Option.some.inj (hw.symm.trans hrow)
    rw [← hn, hst, e2, e3, hc]

/-- The test at every row of a table: place, number of parts, owner, first coin, count. -/
def rawTableOk (T : List (Place × Nat × Addr × Nat × Nat)) : Bool :=
  T.all fun x => rawRowOk x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- Where it accepts: the equation at every row. -/
theorem rawRowStretch_of_table {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B)
    {T : List (Place × Nat × Addr × Nat × Nat)} (h : rawTableOk T = true) :
    ∀ x ∈ T, oneStretch (rowEntries B x.1 x.2.1 0) = some (x.2.2.1, x.2.2.2.1, x.2.2.2.2) :=
  fun x hx => rawRowStretch_of_ok hB (List.all_eq_true.1 h x hx)

/-- K5's twelve rows, written. -/
def rawK5RowsW : List (Place × Nat × Addr × Nat × Nat) :=
  [(⟨1, some 1, 3, .K5⟩, 13, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 3, 3, .K5⟩, 13, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 5, 3, .K5⟩, 13, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 7, 3, .K5⟩, 13, ⟨⟨1, some 7, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 9, 3, .K5⟩, 13, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 11, 3, .K5⟩, 13, ⟨⟨1, some 11, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 13, 3, .K5⟩, 13, ⟨⟨1, some 13, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 15, 3, .K5⟩, 13, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 17, 3, .K5⟩, 13, ⟨⟨1, some 17, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 19, 3, .K5⟩, 13, ⟨⟨1, some 19, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 21, 3, .K5⟩, 13, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, 2251, 1072),
    (⟨1, some 23, 3, .K5⟩, 13, ⟨⟨1, some 23, 1, .K2⟩, 0⟩, 2251, 1072)]

/-- The same with the first row's first coin greater by one. -/
def rawK5RowsBent : List (Place × Nat × Addr × Nat × Nat) :=
  (⟨1, some 1, 3, .K5⟩, 13, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, 2252, 1072) :: rawK5RowsW.tail

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The test accepts K5's twelve rows**: one evaluation in Lean's kernel. -/
theorem rawK5Rows_ok : rawTableOk rawK5RowsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The evaluation can fail. -/
theorem rawK5Rows_bent : rawTableOk rawK5RowsBent = false := by decide +kernel

/-- **WHAT EACH OF K5's TWELVE ROWS SPENDS IN WHATEVER BOOK bookWhole RETURNS AT WP.** -/
theorem rawRowStretchAtK5 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) (g : Nat) (hg : g < 12) :
    oneStretch (rowEntries B ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) =
      some (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩, 2251, 1072) := by
  have H := rawRowStretch_of_table hB rawK5Rows_ok
  have hm : ((⟨1, some (2 * g + 1), 3, .K5⟩ : Place), 13,
      (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩ : Addr), 2251, 1072) ∈ rawK5RowsW := by
    have : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 ∨
        g = 10 ∨ g = 11 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  exact H _ hm

set_option maxRecDepth 1000000 in
/-- The test accepts K6's row. -/
theorem rawRowOkAtK6 :
    rawRowOk ⟨1, some 24, 4, .K6⟩ 8 ⟨⟨1, some 24, 2, .K2⟩, 0⟩ 2434 173 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the first coin greater by one it rejects. -/
theorem rawRowOkAtK6_bent :
    rawRowOk ⟨1, some 24, 4, .K6⟩ 8 ⟨⟨1, some 24, 2, .K2⟩, 0⟩ 2435 173 = false := by
  decide +kernel

/-- **WHAT K6's ROW SPENDS IN WHATEVER BOOK bookWhole RETURNS AT WP.** -/
theorem rawRowStretchAtK6 {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    oneStretch (rowEntries B ⟨1, some 24, 4, .K6⟩ 8 0) =
      some (⟨⟨1, some 24, 2, .K2⟩, 0⟩, 2434, 173) :=
  rawRowStretch_of_ok hB rawRowOkAtK6

end AtFullSide.K14

#print axioms AtFullSide.K14.rawRowStretch_of_ok
#print axioms AtFullSide.K14.rawRowStretch_of_table
#print axioms AtFullSide.K14.rawK5Rows_ok
#print axioms AtFullSide.K14.rawK5Rows_bent
#print axioms AtFullSide.K14.rawRowStretchAtK5
#print axioms AtFullSide.K14.rawRowOkAtK6
#print axioms AtFullSide.K14.rawRowOkAtK6_bent
#print axioms AtFullSide.K14.rawRowStretchAtK6

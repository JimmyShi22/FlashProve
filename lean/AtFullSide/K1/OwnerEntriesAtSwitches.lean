-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/OwnerEntriesAtSwitches.lean: AT THE WRITTEN BOOK: ALL ENTRIES WHOSE OWNER IS THE CODE
SWITCH AT THE LINK 2 g, g = 1 … 11: AS SPENDER, START, COUNT AND MARK, IN THE BOOK's OWN ORDER,
AGAINST A WRITTEN LIST. THE WIDER SISTER OF AtFullSide/K1/RowTakersAtSwitches.lean, WHICH LISTS
THOSE THAT NAME A COIN OF THE MASK ROW: HERE NO TEST ON THE NUMBERS STANDS IN THE WALK. THE WRITTEN
BOOK's ENTRIES ALONE: which part is given which numbers of which owner, under which mark: never what
a coin is. Five theorems; no definition (the definitions: AtFullSide/K1/RowTakers/AllDefs.lean and
Defs.lean).
NO PROPERTY IS CLAIMED.

  owned_written   **ownedIn rawAheadW g = ownedListW g**, at 1 ≤ g ≤ 11: over ALL TEN PIECES of the
                  written book's entries (rawAheadW, AtFullSide/K14/RawAheadWritten.lean)
  owned_at        the same at B.ahead, at whatever book bookWhole returns at the written description
  owned_closed    **there is such a book**: no premise but 1 ≤ g ≤ 11
  owned_lengths   how many: 607 at g = 1, 24 fewer a group, 367 at g = 11

  row_part        the two written lists are tied: the members of ownedListW g that pass meetsRowT
                  are takersW g, in that order, at each of the eleven groups

WHAT THE LIST SHOWS. MARKED AS SPENT: the 319 entries of RowTakersAtSwitches.lean's list, and one
more, behind the row: 17 coins of the extension field from 8850 on, given to the part 0 of the place
of the kind K10 at the link 2 g. MARKED AS CARRIED: six pairs of start and count, the same at every
bearer; the bearers are carriersW's from its number 4 * (g - 1) on; the first bearer, which is the
spender of the 17, has the first five pairs alone. NOBODY ELSE IS GIVEN A COIN OF THAT OWNER BY AN
ENTRY.

By what. Piece by piece and one join: ownedWantsB (RowTakers/AllWants.lean), ownedSegB and
ownedShortB (RowTakers/AllSeg.lean), each with a twin that says no; bookWhole_returns_written_ahead
(AtFullSide/K14/BookWholeWritten.lean).

Who calls. Asked for by the authors of the kind K2, for a test on the book at the switch's own row,
which reads more of the owner's numbers than the mask row. Their caller is not typed yet.

Limits. RowTakersAtSwitches.lean's, all of them: A LISTING, NOT A SECOND SOURCE; a fact on written
values; the merges are mergesByName's; the full size alone; the owner's own use of its coins is by
no entry and is not seen here; that a part lays, spends or carries what the book's numbers say is
not said; that onlineProverFromPublicFiles returns this book is not said; it stands above Honest/Law/Rule/Real.lean. THAT
THE SIX PAIRS ARE THE SWITCH's SIX MESSAGES' RANGES IS NOT SAID HERE. EACH OF THE TWO EQUATIONS
RESTS ON CLOSED FACTS OF ITS OWN; row_part ties the two WRITTEN lists, not the two walks. Nothing on
soundness, on completeness or on what is hidden.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K1.RowTakers.AllWants
import AtFullSide.K1.RowTakers.AllSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open VerifiableInference.Desc (Place KindName)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **ALL ENTRIES OF THE WRITTEN BOOK OF THAT OWNER, IN THE BOOK's OWN ORDER.** -/
theorem owned_written {g : Nat} (h1 : 1 ≤ g) (h11 : g ≤ 11) :
    ownedIn rawAheadW g = ownedListW g := by
  obtain ⟨i, rfl⟩ : ∃ i, g = i + 1 := ⟨g - 1, by omega⟩
  have hi : i ∈ List.range 11 := List.mem_range.2 (by omega)
  have a := of_decide_eq_true (List.all_eq_true.1 ownedWantsB i hi)
  have b := of_decide_eq_true (List.all_eq_true.1 ownedSegB i hi)
  have c := List.all_eq_true.1 ownedShortB i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at c
  obtain ⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩ := c
  unfold rawAheadW ownedListW
  simp only [ownedIn_append, ownedIn_nil, a, b, c1, c2, c3, c4, c5, c6, c7, List.append_nil]

/-- The same at whatever book bookWhole returns at the written description. -/
theorem owned_at {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {g : Nat} (h1 : 1 ≤ g) (h11 : g ≤ 11) :
    ownedIn B.ahead g = ownedListW g := by
  obtain ⟨B', h', ha⟩ := bookWhole_returns_written_ahead
  rw [hB] at h'
  cases h'
  rw [ha]
  exact owned_written h1 h11

/-- **THERE IS SUCH A BOOK: NO PREMISE BUT 1 ≤ g ≤ 11.** -/
theorem owned_closed {g : Nat} (h1 : 1 ≤ g) (h11 : g ≤ 11) :
    ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
        (mergesByName WP.first.blocksInOrder) = .ok B ∧ ownedIn B.ahead g = ownedListW g := by
  obtain ⟨B, hB⟩ := bookWhole_returns_written
  exact ⟨B, hB, owned_at hB h1 h11⟩

/-- How many entries the written list has, group by group. -/
theorem owned_lengths : (List.range 11).map (fun i => (ownedListW (i + 1)).length) =
    [607, 583, 559, 535, 511, 487, 463, 439, 415, 391, 367] := by
  decide +kernel

/-- **The two written lists are tied**: the wider list's members that meet the row are the narrower
list. -/
theorem row_part : ((List.range 11).all fun i =>
    decide ((ownedListW (i + 1)).filter meetsRowT = takersW (i + 1))) = true := by
  decide +kernel

end AtFullSide.K1

#print axioms AtFullSide.K1.owned_written
#print axioms AtFullSide.K1.owned_at
#print axioms AtFullSide.K1.owned_closed
#print axioms AtFullSide.K1.owned_lengths
#print axioms AtFullSide.K1.row_part

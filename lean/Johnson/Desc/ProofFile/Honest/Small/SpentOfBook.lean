-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/SpentOfBook.lean: CONDITIONAL. One statement with its proof. NO
KIND IS NAMED. By the writers of the feed-forward layers' own rounds (sub-protocol K4). It stands
over Honest/Small/SpentOfWants.lean and Honest/BookMergeStretch.lean.

What is here. IN THE WHOLE BOOK OF COINS EACH PART OF A SUB-PROTOCOL IN A LINK OF THE FIRST CHAIN
HAS, TO SPEND, ENTRIES WITH THE NAMES AND COUNTS OF `partStates` (Honest/Small/SpentOfWants.lean).
`bookWhole_row_wants` (Honest/BookMergeStretch.lean) has the row's spending entries as the maker's
one list; `spent_named_of_wants` cuts that list part by part; the two owners' names are the two
that `ownerOf` was called with.

  `bookWhole_part_states`   **under `bookWhole_row_wants`' own five premises, and no other.**

Not shown here. THAT `bookWhole` RETURNS AT ANY FILES; that the description passes its test on
places. Which parts are merges is the free parameter M: nothing compares it with the format.
Nothing on a sub-protocol that holds a fold, or that stands in no link. The first chain alone.
Names and counts alone: which coins the entries name is not spoken of. Only the runs that are
spent. THAT ANY PART OF THE PROTOCOL STATES WHAT `partStates` SAYS. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Small.SpentOfWants
import Johnson.Desc.ProofFile.Honest.BookMergeStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi : Type}

/-- CONDITIONAL on h, hp, hb, hl and hF. **WHAT THE WHOLE BOOK HAS FOR PART NUMBER i OF THE
SUB-PROTOCOL b TO SPEND, AS NAMES AND COUNTS.** -/
theorem bookWhole_part_states {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l)
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") :
    ∀ (i : Nat) (q : PartAt), (planParts b)[i]? = some q →
      (spentE B ⟨b.place, i⟩).map Ahead.named =
        partStates maskRowRun indexMaskRun (M.ends.contains q.addr) q := by
  obtain ⟨row, idx, hr, hi, hE⟩ := bookWhole_row_wants h hp hb hl hF
  intro i q hq
  have e := spent_named_of_wants hE (planParts_addr b) i q hq
  rw [ownerOf_name hr, ownerOf_name hi] at e
  exact e

end ProofFile.Honest

#print axioms ProofFile.Honest.bookWhole_part_states

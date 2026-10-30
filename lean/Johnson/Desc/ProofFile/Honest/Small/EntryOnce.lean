-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Small/EntryOnce.lean: NO KIND IS NAMED. By the writers of the merge of
the claims on the weights (sub-protocol K11), at the home that the frame's authors named for it. THE
NUMBERS OF AN ENTRY's BLOCK LIE IN NO OTHER PART's SPENDING ENTRY, AT A BOOK THAT FAILS NONE OF ITS
OWN TESTS: the frame's authors' law on the book (`ProverCoinCounts.spentApart_parts`, `shares_false_iff`,
Honest/BookApart.lean, a file that is not in this library) in the letters of the public test
`entryRunIs` (EntryRunIs.lean of this folder). One lemma with its proof; no definition; none of the
library's goals. PUBLIC DATA ALONE: a description, a book, numbers.

  `entryRunIs_once`   general in the part's address a and the entry's number j: the book fails none
                      of its tests (`ProverCoinCounts.word` is none) · the test says yes at the part's spending
                      entries, at j, an owner o, a start st and a count ct. Then, of every spending
                      entry e' of every OTHER part a' that has the owner o: none of the numbers st.e
                      + i, i below ct.e, lies in its block of the extension field

WHAT IT IS NOT. SILENT AT a' = a: NOTHING ON ANOTHER SPENDING ENTRY OF THE SAME PART
(`ProverCoinCounts.spentApart` of the same file serves there). Under two premises on the book: that any book
meets them is not said here. Spending entries alone, but all of them, whichever maker's list they
come from; nothing on carrying entries. ENTRIES ARE HELD AGAINST ENTRIES: what the owner itself does
with these elements is not seen. The base field's half of the law is not drawn. It says which
entries of a book cover a number: nothing on how often a value stands in a message.

HERE THE TEST's COUNT IS SPENT: it says how far the block reaches.

How. `entryRunIs_gives` hands the entry e with its owner, start and count; it is a member of the
part's spending entries; `ProverCoinCounts.spentApart_parts` at the two addresses: e and e' share nothing;
`shares_false_iff`, at one owner, its half on the extension field, at the number st.e + i.

Limits. Calls and arithmetic. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Small.EntryRunIs
import Johnson.Desc.ProofFile.Honest.BookApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

/-- **No other part's spending entry covers a number of the entry's block.** -/
theorem entryRunIs_once {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts} (hW : B.word F = none) {a : Addr}
    {j : Nat} {o : Addr} {st ct : Due} (hE : entryRunIs (spentE B a) j o st ct = true) :
    ∀ a', a' ≠ a → ∀ e' ∈ spentE B a', e'.owner = o → ∀ i, i < ct.e →
      ¬ (e'.start.e ≤ st.e + i ∧ st.e + i < e'.start.e + e'.count.e) := by
  intro a' hne e' he' ho' i hi hb
  obtain ⟨e, he, ho, hst, hct⟩ := entryRunIs_gives hE
  have hm : e ∈ spentE B a := List.mem_of_getElem? he
  have hs := ProverCoinCounts.spentApart_parts hW hne.symm e hm e' he'
  have h2 := ((shares_false_iff e e').1 hs (ho.trans ho'.symm)).2
  refine h2 ⟨st.e + i, ⟨?_, ?_⟩, hb.1, hb.2⟩
  · rw [hst]
    exact Nat.le_add_right _ _
  · rw [hst, hct]
    exact Nat.add_lt_add_left hi _

end ProofFile.Honest

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.entryRunIs_once

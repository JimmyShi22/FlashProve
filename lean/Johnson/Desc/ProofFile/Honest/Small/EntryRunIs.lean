-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/EntryRunIs.lean: NO KIND IS NAMED. By the writers of the
switches (sub-protocol K2) and of the merge of the claims on the weights (K11), at the home that the
frame's authors named for it: beside the frame, over Honest/Law/Rule/Cell.lean alone. ONE SMALL
PUBLIC TEST ON A LIST OF THE BOOK's ENTRIES: THE ENTRY NUMBER i HAS A GIVEN OWNER, A GIVEN START AND
A GIVEN COUNT; WHAT ITS YES GIVES; AND THAT THE FRAME's TWO LISTS `spentE` AND `carryE`
(Honest/Law/Rule/Cell.lean) ARE THE LISTS THAT `lendPart` (Honest/Frame.lean) WALKS. Two definitions
(the test; a made-up entry for a control). Lemmas; none of the library's goals.

  `entryRunIs` es i o st ct   the test
  `entryRunIs_gives`          its yes: es[i]? = some e with e.owner = o, e.start = st, e.count = ct
  `entryRunIs_of`             the way back
  `spentE_is`, `carryE_is`    the two lists, written out as `lendPart` has them
  `entryRunIs_can_fail`       A CONTROL at a made-up list of one entry: yes at its own three; no at
                              another owner, another start, another count, and beyond the list

Why. `lend` (Honest/Frame.lean) holds of an entry its name and its count against what the part
states; the owner and the start are the book's word alone. A law that says WHICH of a sender's
elements a part is handed wants these two; the count is held here against a third source, the
sender's own.

WHAT IT IS NOT. A test on public data: the book. That any book passes it at any letters is not said
here.

NEAR. `lendsRuns` (LendsRow.lean of this folder): a test with code that mirrors what `lend` itself
holds of an entry: the name, the count, and that the cut lies within the owner's count. KIN, BY NAME
ALONE: `givesAll_carried`: a law whose premise ends in this test's three equations, over the
carrying entries. `oneStretch`: a test on a whole row's entries, which returns one owner with a
start and a count of the extension field; `entryRunIs_of_oneStretch` and `entryRunIs_of_row`
(Honest/BookStretchEntry.lean, which imports this file; this library may not hold it) tie the two at
a row of one entry.

Limits. An unfolding. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Cell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **A PUBLIC TEST**: the entry number i of the list has this owner, this start and this count. -/
def entryRunIs (es : List Ahead) (i : Nat) (o : Addr) (st ct : Due) : Bool :=
  (es[i]?).any fun e => e.owner == o && e.start == st && e.count == ct

/-- **What its yes gives.** -/
theorem entryRunIs_gives {es : List Ahead} {i : Nat} {o : Addr} {st ct : Due}
    (h : entryRunIs es i o st ct = true) :
    ∃ e, es[i]? = some e ∧ e.owner = o ∧ e.start = st ∧ e.count = ct := by
  unfold entryRunIs at h
  cases he : es[i]? with
  | none =>
    rw [he] at h
    simp only [Option.any_none, Bool.false_eq_true] at h
  | some e =>
    rw [he] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨e, rfl, h.1.1, h.1.2, h.2⟩

/-- The way back. -/
theorem entryRunIs_of {es : List Ahead} {i : Nat} {e : Ahead} (he : es[i]? = some e) :
    entryRunIs es i e.owner e.start e.count = true := by
  unfold entryRunIs
  rw [he]
  simp only [Option.any_some, beq_self_eq_true, Bool.and_self]

/-- The spending entries, as `lendPart` has them. -/
theorem spentE_is (Bk : ProverCoinCounts) (a : Addr) :
    spentE Bk a = (Bk.ahead.filter fun e => e.spender == a).filter (·.once) := rfl

/-- The carrying entries, as `lendPart` has them. -/
theorem carryE_is (Bk : ProverCoinCounts) (a : Addr) :
    carryE Bk a = (Bk.ahead.filter fun e => e.spender == a).filter (!·.once) := rfl

/-- For a control: a made-up entry. -/
def entryToy : Ahead :=
  ⟨"r", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨0, 3⟩, ⟨0, 2⟩, ⟨⟨1, some 0, 4, .K11⟩, 1⟩, true⟩

/-- **A control**, at the list of that one entry. -/
theorem entryRunIs_can_fail :
    entryRunIs [entryToy] 0 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨0, 3⟩ ⟨0, 2⟩ = true ∧
      entryRunIs [entryToy] 0 ⟨⟨1, some 0, 1, .K1⟩, 1⟩ ⟨0, 3⟩ ⟨0, 2⟩ = false ∧
      entryRunIs [entryToy] 0 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨0, 4⟩ ⟨0, 2⟩ = false ∧
      entryRunIs [entryToy] 0 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨0, 3⟩ ⟨0, 1⟩ = false ∧
      entryRunIs [entryToy] 1 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨0, 3⟩ ⟨0, 2⟩ = false := by
  decide

end ProofFile.Honest

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.entryRunIs
#print axioms ProofFile.Honest.entryRunIs_gives
#print axioms ProofFile.Honest.entryRunIs_of
#print axioms ProofFile.Honest.spentE_is
#print axioms ProofFile.Honest.carryE_is
#print axioms ProofFile.Honest.entryToy
#print axioms ProofFile.Honest.entryRunIs_can_fail

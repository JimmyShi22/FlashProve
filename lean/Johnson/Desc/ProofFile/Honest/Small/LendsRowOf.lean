-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/LendsRowOf.lean: CONDITIONAL. Two statements with their proofs.
NO KIND IS NAMED. By the writers of the feed-forward layers' own rounds (sub-protocol K4). It
stands over Honest/Small/LendsRow.lean and Honest/BookLends.lean.

What is here. THE BOOK LENDS A ROW OF PARTS WHERE EACH PART's THREE STATED LISTS ARE THE BOOK's.
`lendPart_of_fit` (Honest/BookLends.lean) has that for one part: under «the book passes its own
tests» (h) and the library's test on places (hp), at an address of the chain: where the part's
count is the book's row, and the names and counts of what it spends and carries are those of the
book's entries, in the book's order, `lendPart` returns at every run's coins. Here that is carried
from a part to a row, and to the Bool `lendsRow` (Honest/Small/LendsRow.lean).

  `lendRow_of_fit`   part by part, from part number j on: `lendRow` returns at every run's coins.
  `lendsRow_of_fit`   **the Bool is true**: no coin stands in the statement.

NO DEFINITION IS HERE: the three equations are written out in the premise, in `lendPart_of_fit`'s
own words. They are three of the four fields of `Fit` (Honest/Law/Rule/PartCell.lean); its field
row is not asked.

Not shown here. THAT ANY BOOK PASSES ITS TESTS; that hp holds; THAT THE THREE EQUATIONS HOLD AT ANY
PART OF THE PROTOCOL. What is lent is not described: only that something is. Nothing on the further
tests that `chainSteps` (Honest/Frame.lean) makes before it calls `lendRow`: the premise speaks of
the parts of the list alone, not of a row or an entry that the book has for a part beyond them. A
PART THAT STATES A RUN OF COUNT 0 MEETS THE SECOND OR THIRD EQUATION ONLY AT A BOOK THAT HAS AN
ENTRY OF COUNT 0 FOR IT. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Small.LendsRow
import Johnson.Desc.ProofFile.Honest.BookLends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)

variable {Xi V W Y : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- CONDITIONAL on h, hp, hch, ha and the three equations at each part. **Part by part, `lendRow`
returns, at every run's coins.** -/
theorem lendRow_of_fit (h : B.word F = none) (hp : F.placesOk = true) {ch : Nat}
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {a : Place} (ha : a ∈ placesAt F ch) (k : Coins B) :
    ∀ (ps : List (Part V W Y)) (j : Nat),
      (∀ i p, ps[i]? = some p → p.takes = dueAt (B.rowsOf ch) ⟨a, j + i⟩ ∧
        (spentE B ⟨a, j + i⟩).map Ahead.named = p.spends ∧
        (carryE B ⟨a, j + i⟩).map Ahead.named = p.carries) →
      ∃ c, lendRow B (B.rowsOf ch) (k.look ch) a ps j = .ok c
  | [], _, _ => ⟨(), rfl⟩
  | p :: ps, j, hf => by
    obtain ⟨h1, h2, h3⟩ := hf 0 p rfl
    obtain ⟨c, hc⟩ := lendPart_of_fit h hp hch (a := ⟨a, j⟩) ha h1 h2 h3 k
    obtain ⟨r, hr⟩ := lendRow_of_fit h hp hch ha k ps (j + 1) fun i q hq => by
      have e := hf (i + 1) q hq
      rw [show j + (i + 1) = j + 1 + i by omega] at e
      exact e
    refine ⟨(c, r), ?_⟩
    simp only [lendRow]
    rw [hc, hr]
    rfl

/-- CONDITIONAL on h, hp, hch, ha and hf. **THE BOOL IS TRUE.** No coin stands in the statement. -/
theorem lendsRow_of_fit (h : B.word F = none) (hp : F.placesOk = true) {ch : Nat}
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {a : Place} (ha : a ∈ placesAt F ch)
    (ps : List (Part V W Y))
    (hf : ∀ i p, ps[i]? = some p → p.takes = dueAt (B.rowsOf ch) ⟨a, i⟩ ∧
      (spentE B ⟨a, i⟩).map Ahead.named = p.spends ∧
      (carryE B ⟨a, i⟩).map Ahead.named = p.carries) :
    lendsRow B ch a ps = true :=
  (lendsRow_iff (default : Coins B) ch a ps).1
    (lendRow_of_fit h hp hch ha default ps 0 fun i p hq => by
      rw [Nat.zero_add]
      exact hf i p hq)

end ProofFile.Honest

#print axioms ProofFile.Honest.lendRow_of_fit
#print axioms ProofFile.Honest.lendsRow_of_fit

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PileReadsOut.lean: WHAT "all rows on the table are true" AT THE READER THROUGH
THE RECORD's OWN BOOK (`RowsTrue (rwBook arr mat x) x.2 w`: our layer's sentence at the items "every
pending row holds" and "the one claim holds") READS OF THE RECORD. Statements with their proofs.
Why. It is asked of each layer, for each item whose sentence it fills and which has no
part of the record of its own: the sentence at one record gives it at another wherever the two agree
in nine named fields (the statement, the book, the count of roots, the debt of rows, the mark, the
state of the calls, what the links left, the request's words, the link's number). A FIND: THESE NINE
DO NOT FIX OUR SENTENCE: the rows on the table (`S.rows`, Johnson/Desc/First/State.lean) are read
off the field "here": at the chain's end, where the record holds a linear claim, they are the one
row of that claim; elsewhere the pile. TWO RECORDS THAT AGREE IN THE NINE, ONE AT THE CHAIN's END
WITH A CLAIM AND ONE NOT, HAVE TWO LISTS OF ROWS.
  `rows_not_end`: where neither record stands at the chain's end and what the links left is the
  same, the rows on the table are the same.
  `pile_reads`: **one public part is not even asked: one statement, one book, the same rows on the
  table: one truth value**, at every witness. No string is read.
  `pile_reads_not_end`: so the nine give it WITH A TENTH CLAUSE: neither record stands at the
  chain's end.
What is not claimed. The term that is asked, in its own form (its definition is not used
here). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.ReaderByBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)

/-- Where a record does not stand at the chain's end the rows on the table are the pile. -/
theorem rows_pile {s : S} (h : ∀ a, s.here ≠ .mem a) : s.rows = s.out.pending := by
  unfold S.rows
  split
  · rename_i a hh
    exact absurd hh (h a)
  · rfl

theorem rows_not_end {s s' : S} (h : ∀ a, s.here ≠ .mem a) (h' : ∀ a, s'.here ≠ .mem a)
    (ho : s'.out = s.out) : s'.rows = s.rows := by
  rw [rows_pile h, rows_pile h', ho]

section
variable {Pp Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
  (mat : Cells → Fin nR → (Fin k → Bool) → GE)

/-- **What the sentence reads of the record.** -/
theorem pile_reads (z z' : Pp) (s s' : S) (hst : s'.st = s.st) (hbk : s'.book = s.book)
    (hr : s'.rows = s.rows) (w : Desc.Wit Cells Tok MsgT) :
    RowsTrue (rwBook arr mat (z', s')) s' w ↔ RowsTrue (rwBook arr mat (z, s)) s w := by
  have e : rwBook arr mat (z', s') w = rwBook arr mat (z, s) w := by
    unfold rwBook
    rw [hst, hbk]
  unfold RowsTrue
  rw [hr, e]

/-- With the tenth clause. -/
theorem pile_reads_not_end (z z' : Pp) (s s' : S) (hst : s'.st = s.st) (hbk : s'.book = s.book)
    (ho : s'.out = s.out) (h : ∀ a, s.here ≠ .mem a) (h' : ∀ a, s'.here ≠ .mem a)
    (w : Desc.Wit Cells Tok MsgT) :
    RowsTrue (rwBook arr mat (z', s')) s' w ↔ RowsTrue (rwBook arr mat (z, s)) s w :=
  pile_reads arr mat z z' s s' hst hbk (rows_not_end h h' ho) w

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.rows_not_end
#print axioms VerifiableInference.Desc.K13.Law.pile_reads
#print axioms VerifiableInference.Desc.K13.Law.pile_reads_not_end

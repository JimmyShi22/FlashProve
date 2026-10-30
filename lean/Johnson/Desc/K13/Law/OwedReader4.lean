-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedReader4.lean: A STATEMENT THAT IS OWED, WRITTEN AS A DEFINITION OF A
Prop: no proof stands here. It is one clause of what kind K13's law at the table of joints still
asks at W's commitment (`Others4.reader`, Johnson/Desc/K13/Law/FillFromSentences.lean), at the
reader through the record's own book (`rwBook`, Johnson/Desc/K13/Law/ReaderByBook.lean).
IN PLAIN WORDS. W's commitment sends one message and lays rows on the own group. It leaves the
rows on the table, the record's number of the index masks' message, that message's shape, its
place in the book and the tree there. So what the rows on the table behind the block say under the
reader at the record BEHIND, they say under the reader at the record IN FRONT.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.K13.Law.SeatedM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)

/-- **OWED.** x, x': the records in front of and behind a step of W's commitment. The four premises
are had from the promise in front. -/
def OwedReader4 : Prop :=
  ∀ {Pp Cl Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin k → Bool) → GE) (P : Where) (P' : K1.Par) (x x' : Pp × S)
    (w : Desc.Wit Cells Tok MsgT), StepM4 Cl P P' x x' →
    pileMasksC x.2 = true → x.2.out.indexMasks < x.2.st.oracles.size →
    x.2.book.place.size = x.2.st.oracles.size →
    (∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size) →
    RowsTrue (rwBook arr mat x') x'.2 w → RowsTrue (rwBook arr mat x) x'.2 w

end VerifiableInference.Desc.K13.Law

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedCutSame.lean: A STATEMENT THAT IS OWED, WRITTEN AS A DEFINITION OF A Prop:
no proof stands here.
IN PLAIN WORDS. Kind K13's reader of the rows on the table takes the mask entries off the words, CUT
TO THE TABLE: beyond a table's size it gives 0 (`maskCut`, Johnson/Desc/K13/Law/ReaderByBook.lean).
Other files' sentences read the words uncut (`witOf`, `maskOf`: Johnson/Desc/K13/Law/Eval.lean). OF
A ROW WHOSE MASK ENTRIES ALL LIE WITHIN THEIR TABLES THE TWO READERS SAY THE SAME (`Holds`,
Johnson/Desc/K13/Law/Means.lean): the matrix is one, and the row's mask form reads the entries that
the row names and no other.
Who spends it: the joints at which other files' sentence at the uncut reader meets "all rows on
the table are true" at ours.
What is not claimed. That any row's entries lie within their tables: THE VERIFIER's TEST ON THE
PENDING ROWS (`memberRowsFit`, OnBytes/Iop/Lin.lean) COMPARES AN ENTRY's MESSAGE, NOT ITS INDEX.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.K13.Law.Eval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words tableSize)

/-- **OWED.** The cut reader and the plain one say the same of a row whose mask entries lie within
their tables. -/
def OwedCutSame : Prop :=
  ∀ (st : Statement) (m : Words GE) {nR k : ℕ} (mat : Fin nR → (Fin k → Bool) → GE)
    (r : TensorRow), (∀ t ∈ r.masks, t.1.index < tableSize st t.1.oracle .mask) →
    (Holds ρg (⟨mat, maskCut st m⟩ : Wit GE nR k) r ↔ Holds ρg (witOf mat m) r)

end VerifiableInference.Desc.K13.Law

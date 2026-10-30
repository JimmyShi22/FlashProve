-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TableCol.lean: the column of a table that a proximity test's move
sends, as a view shows it, is the term's own column. The term is `testAll` (Test.lean in this
folder): its field `tr` (`BOut`, Johnson/Prover/Link/BodyAll.lean) is a list of families of columns;
a family is a function from a position to the column there, a list of words (`UInt64`). `msgAt`
(Parts.lean in this folder), the message that a round's move (`moveAt`) returns, builds its table
from the family at the round's number: each word is read as an element of the base field (`toF`,
OnBytes/Slice/Field.lean), and the table's width is the length of the column at position 0.
`Table.col` (the frame, Johnson/Desc/ProofFile/Honest/Frame.lean; by its docstring "the column at a
position, as a view shows it") writes a symbol of a table as words again (`ofF`). The second undoes
the first at a position where the column has that length and every word is the written form `ofF y`
of an element y. Two families are proved to be such, at every position and at every value of their
parameters: `aCol` and `freshCol`. Two definitions, and theorems with their proofs.

  `col_tableOf`: under the two hypotheses below, `(tableOf a col).col x = col x`: the table's column
    at the position x is the family's column there. For every number a, family col and position x
  `col_aCol`: `(tableOf a (aCol last next Q)).col x = aCol last next Q x`, at every value of the
    five variables. `aCol` (Johnson/Desc/K12/Honest/Stages.lean) is the written column of the tree
    that a switch sends (a switch leads from one stage of the test to the next): `lastCol`
    (Johnson/Prover/Link/BodyAll.lean) where `last` is true, else `stageColW`
    (Johnson/Prover/Link/SwitchCols.lean). No hypothesis
  `col_freshCol`: `(tableOf a (freshCol s P)).col x = freshCol s P x`, at every value of the four
    variables. `freshCol` (Test.lean) is the column, as words, of a tree that holds a fresh table
    and nothing else. No hypothesis
  `CanonW`: a definition, of a list of words: every word of it is `ofF y` for some element y of the
    base field
  `tableOf`: a definition, from a number a (the depth) and a family col: the table (`Table`,
    Frame.lean) with `logLength` a and `words` the length of `col 0`; entry k of its symbol at x is
    word number k of `col x`, read by `toF`, and 0 where the column has no such word
  `canonW_wordsOf`: where every element of a list is `ofE y` for some y of the extension field, the
    list's words (`wordsOf`, SwitchCols.lean) meet `CanonW`
  `canonW_aCol`, `canonW_freshCol`: the columns of `aCol` and of `freshCol` meet `CanonW`, at every
    position
  `length_aCol`: the column of `aCol` at a position x has the length of its column at position 0
  `length_words12`: `words12` (Johnson/Prover/Link/Base.lean) gives a list of 12 words

By what. `col_tableOf`: entry by entry, by `toF_ofF` (OnBytes/Slice/Field.lean: `toF (ofF x) = x`).
`canonW_freshCol`, and `canonW_aCol` where `last` is false: `canonW_wordsOf` with `mem_wr`
(SwitchCols.lean); `canonW_aCol` where `last` is true: by unfolding `lastCol`, `words12` and
`baseColW` (Base.lean). `length_aCol`: `length_stageColW` (Johnson/Prover/Link/HyStage.lean) and
`length_words12`. `col_aCol` and `col_freshCol` are `col_tableOf` at these; the second takes its
lengths from `length_freshCol` (FreshCols.lean in this folder).

Hypotheses. Of `col_tableOf`: `hl`: `col x` has the length of `col 0`; `hc`: `col x` meets
`CanonW`. The other theorems but `canonW_wordsOf` have none.

Limits. Outside the two hypotheses no equation is stated: `tableOf` cuts a longer column and fills a
shorter one with 0, and `toF` reduces a word from the prime on. The number a is a free parameter,
which `Table.col` does not read; x is any natural number, also from 2 ^ a on. That the table in a
message of `msgAt` is `tableOf` of the family that the term lists, and that every family that the
term lists meets the two hypotheses at every position, is stated in SentTables.lean in this folder
(`msgAt_tables`, `good_test`), not here. Nothing on which round sends which tree, on a decision, on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Desc.ProofFile.Honest.K12.FreshCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- Every word of the list is the written form `ofF y` of an element y of the base field. -/
def CanonW (l : List UInt64) : Prop := ∀ w ∈ l, ∃ y : Cb.Gl.F, w = ofF y

/-- The table built from a depth a and a family of columns col, by the expression that `msgAt`
(Parts.lean) has for its table: the width is the length of `col 0`; a missing word counts as 0. -/
def tableOf (a : ℕ) (col : ℕ → List UInt64) : Table :=
  ⟨a, (col 0).length, fun x k => toF ((col x).getD k.val 0)⟩

/-- **The table's column at x is `col x`**, where `col x` has the length of `col 0` (`hl`) and every
word of it is the written form of an element of the base field (`hc`). -/
theorem col_tableOf (a : ℕ) (col : ℕ → List UInt64) (x : ℕ)
    (hl : (col x).length = (col 0).length) (hc : CanonW (col x)) :
    (tableOf a col).col x = col x := by
  refine List.ext_getElem (by simp [Table.col, tableOf, hl]) fun i h1 h2 => ?_
  simp only [Table.col, tableOf, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ h2]
  obtain ⟨y, hy⟩ := hc _ (List.getElem_mem h2)
  rw [hy, toF_ofF]

theorem canonW_wordsOf (l : List Fmt.M1.E) (h : ∀ e ∈ l, ∃ y : GE, e = ofE y) :
    CanonW (wordsOf l) := fun w hw => by
  obtain ⟨e, he, hw'⟩ := List.mem_flatMap.1 hw
  obtain ⟨y, rfl⟩ := h e he
  simp only [words3, ofE, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with h | h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

theorem canonW_freshCol (s : Sg) (P : PS) (x : ℕ) : CanonW (freshCol s P x) :=
  canonW_wordsOf _ (mem_wr _ _)

theorem canonW_aCol (last : Bool) (next : Fmt.M1.Stage) (Q : PS) (x : ℕ) :
    CanonW (aCol last next Q x) := by
  unfold aCol
  cases last
  · refine canonW_wordsOf _ fun e he => ?_
    simp only [List.mem_append] at he
    rcases he with he | he | he <;> exact mem_wr _ _ e he
  · intro w hw
    simp only [if_true, lastCol, words12, baseColW, ofE, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h | h | h | h <;> exact ⟨_, h⟩

theorem length_words12 (o : Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E) :
    (words12 o).length = 12 := rfl

theorem length_aCol (last : Bool) (next : Fmt.M1.Stage) (Q : PS) (x : ℕ) :
    (aCol last next Q x).length = (aCol last next Q 0).length := by
  unfold aCol
  cases last
  · simp only [Bool.false_eq_true, if_false, length_stageColW]
  · simp only [if_true, lastCol, length_words12]

/-- **The same for the tree that a switch sends** (`aCol`, Johnson/Desc/K12/Honest/Stages.lean), at
every position. No hypothesis. -/
theorem col_aCol (a : ℕ) (last : Bool) (next : Fmt.M1.Stage) (Q : PS) (x : ℕ) :
    (tableOf a (aCol last next Q)).col x = aCol last next Q x :=
  col_tableOf a _ x (length_aCol last next Q x) (canonW_aCol last next Q x)

/-- **The same for a tree that holds a fresh table and nothing else** (`freshCol`, Test.lean), at
every position. No hypothesis. -/
theorem col_freshCol (a : ℕ) (s : Sg) (P : PS) (x : ℕ) :
    (tableOf a (freshCol s P)).col x = freshCol s P x :=
  col_tableOf a _ x (by rw [length_freshCol, length_freshCol]) (canonW_freshCol s P x)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.col_tableOf
#print axioms ProofFile.Honest.K12.canonW_wordsOf
#print axioms ProofFile.Honest.K12.canonW_freshCol
#print axioms ProofFile.Honest.K12.canonW_aCol
#print axioms ProofFile.Honest.K12.length_words12
#print axioms ProofFile.Honest.K12.length_aCol
#print axioms ProofFile.Honest.K12.col_aCol
#print axioms ProofFile.Honest.K12.col_freshCol
#print axioms ProofFile.Honest.K12.CanonW
#print axioms ProofFile.Honest.K12.tableOf

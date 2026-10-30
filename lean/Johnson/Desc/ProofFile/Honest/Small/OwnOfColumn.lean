-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Small/OwnOfColumn.lean: THE LIBRARY's INTEGERS BEHIND A SUB-PROOF's
COMMITTED SYMBOLS (`Meaning.ownOf`, Johnson/Goal/Meaning/HidOwn.lean), COLUMN BY COLUMN. Of no kind.
No definition; one theorem.

  `ownOf_of_column`   where ONE column's symbols are the packing of small integers, ownOf reads
                      these integers back in that column, whatever the other columns' symbols are

Why. ownOf is made of `Cb.Pv.Tail.cellsOf` (Cb/Pv/Tail/Unique.lean), which chooses column by column.
Two of the library's laws on it (`ownOf_unique`; `cellsOf_of_packs`, Cb/Pv/Tail/Base.lean) ask the
packing of ALL columns of ALL matrices of the sub-proof; a third speaks column by column, at one set
of letters (see By). Whoever knows some matrices' symbols alone (a matrix may be borrowed, and its
symbols lie in another sender's message), at other letters, wants this form.

By. `packs_unique`, `packs_cellsOf` (Cb/Pv/Tail/Unique.lean), at one column. THE LIBRARY HAS THIS
SENTENCE ALREADY AT ONE SET OF LETTERS: `VerifiableInference.Desc.Kinds.Head.Law.own_of_packs`
(Johnson/Desc/Kinds/Law/FourRunsTie.lean): at segment 24, the library's own sizes and the symbols
read in the stated data (`symD`). The proof here is that proof, line for line, with the sizes, the
symbols and the sub-proof's number as letters: for symbols that are read elsewhere.

What it is not.
  * That any symbols are a packing of small integers is a hypothesis (h1, h2).
  * The WHOLE column is asked: every row of cells of the size, and every row of symbols.
  * hu: the size's three inequalities, at the field's characteristic: a hypothesis.
  * ownOf is found by choice: no program is given.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Goal.Meaning.HidOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small

open Cb.Pv.Tail (Size Syms Packs symL cellsOf packs_unique packs_cellsOf)

/-- GENERAL. **THE LIBRARY's INTEGERS BEHIND THE SYMBOLS, COLUMN BY COLUMN.** -/
theorem ownOf_of_column {s : ℕ → Size} {y : ∀ k, Syms Cb.Gl.E (s k)} {k : ℕ} (p : ℕ)
    [CharP Cb.Gl.E p] (hu : (s k).Uniq p) (μ : Fin (s k).NM) (c : Fin ((s k).k μ))
    {a : Fin ((s k).m μ) → ℤ} (h1 : ∀ i, |a i| < 2 * ((s k).beta : ℤ))
    (h2 : ∀ i', y k μ i' c = ((Alg.pack ((s k).rad : ℤ) a i' : ℤ) : Cb.Gl.E))
    (r : Fin ((s k).m μ)) : Meaning.ownOf s y k μ.val r.val c.val = a r := by
  have ha : Packs (symL Cb.Gl.E (s k)) (y k) μ c a := ⟨h1, h2⟩
  have e : a = cellsOf (symL Cb.Gl.E (s k)) (y k) μ c :=
    packs_unique (symL Cb.Gl.E (s k)) p hu (fun _ => rfl) ha
      (packs_cellsOf (symL Cb.Gl.E (s k)) ⟨_, ha⟩)
  unfold Meaning.ownOf OnBytes.Road.Rows.Norms.mzTot
  rw [dif_pos μ.isLt, dif_pos c.isLt, dif_pos r.isLt]
  exact (congrFun e r).symm

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.ownOf_of_column

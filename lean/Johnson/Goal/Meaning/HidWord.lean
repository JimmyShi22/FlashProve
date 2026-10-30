-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidWord.lean: the 24 equations "reader and owner read one array", at the lists
behind the committed symbols, from a plainer premise: reader and owner have the same symbols.

OneWord (Johnson/Goal/Meaning/HidOwn.lean) and HeadWord (Johnson/Goal/Meaning/HidHead.lean) are
equations of integer matrices (13 of the 24 within a fence; here all 24 come out at all rows and
columns). At seen := ownOf s y these matrices are made of the sub-proofs' committed symbols, column
by column: the cells of a column are a function of that column's symbols, of its number of rows, of
the radix and of the shift (cellsOf, Cb/Pv/Tail/Unique.lean). So if a reader's entry and its owner's
entry have the same sizes and the same symbols, they have the same cells. THE EQUATIONS need no
probability, no smallness (Base) and no uniqueness (Size.Uniq): where the symbols are the packing of
nothing small, both sides are 0. (To carry the library's records to ownOf one does need them:
attOrd_ownOf wants the law at mzAt y, so Base; layerOrd_ownOf wants Size.Uniq:
Johnson/Goal/Meaning/HidLaws.lean.)

Main names:
  colOf m rad beta col   the cells behind one column of symbols: cellsOf without a signature.
  symTot y   the symbols as a function on all numbers (matrix, row of symbols, column); 0 out of
    range.
  SameArr s y a s' y' a'   entry a of (s, y) and entry a' of (s', y'): both are entries, with the
    same rows, columns, radix and shift, and the same symbols.
  mzTot_same   then the total integer matrices behind them are equal at all rows and columns.
  oneWord_ownOf, headWord_ownOf   SameArr at the 23 and at the 24th pair gives OneWord and HeadWord
    at ownOf s y.
  maOf_ownOf, mgOf_ownOf   under SameArr hidOf's lists at ownOf ARE the sub-proofs' own lists, as
    functions: for a caller that comes one clause at a time, or with an equation at all names.

What is not claimed. SameArr at any pair: that a sub-proof which borrows an array reads the owner's
committed symbols is a matter of the link's frame. The verifier's plans mark a borrowed entry (kind
1) and give it its owner's label (Johnson/Goal/Meaning/HidOwn.lean: maOf_plan); that the symbols y k
of a signature are laid by these labels is typed nowhere. The program does not import this file.

-/
import Johnson.Goal.Meaning.HidHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Layer (Lay matIx)
open Cb.Pv.Tail (Size Syms)

open Classical in
/-- The cells behind one column of symbols: small integers with that packing; 0 if there are none.
-/
noncomputable def colOf (m rad beta : ℕ) (col : Fin (Alg.symRows m) → Cb.Gl.E) : Fin m → ℤ :=
  if h : ∃ a : Fin m → ℤ, Alg.Small (beta : ℤ) a ∧
      ∀ i', col i' = ((Alg.pack (rad : ℤ) a i' : ℤ) : Cb.Gl.E) then h.choose else fun _ => 0

/-- It is the library's cellsOf, column by column. -/
theorem mzAt_colOf {s : Size} (y : Syms Cb.Gl.E s) (μ : Fin s.NM) (c : Fin (s.k μ)) :
    Rows.mzAt y μ c = colOf (s.m μ) s.rad s.beta fun i' => y μ i' c := rfl

/-- The same on all numbers: a column of symbols on all numbers, a row on all numbers. -/
noncomputable def colTot (m rad beta : ℕ) (col : ℕ → Cb.Gl.E) : ℕ → ℤ := fun r =>
  if hr : r < m then colOf m rad beta (fun i' => col i'.val) ⟨r, hr⟩ else 0

/-- The symbols on all numbers: matrix, row of symbols, column; 0 out of range. -/
def symTot {s : Size} (y : Syms Cb.Gl.E s) : ℕ → ℕ → ℕ → Cb.Gl.E := fun a i c =>
  if h : a < s.NM then
    if hi : i < Alg.symRows (s.m a) then
      if hc : c < s.k a then y ⟨a, h⟩ ⟨i, hi⟩ ⟨c, hc⟩ else 0
    else 0
  else 0

/-- A column of the total integer matrices, from the total symbols. -/
theorem mzTot_colTot {s : Size} (y : Syms Cb.Gl.E s) {a c : ℕ} (h : a < s.NM) (hc : c < s.k a)
    (r : ℕ) :
    mzTot (Rows.mzAt y) a r c = colTot (s.m a) s.rad s.beta (fun i => symTot y a i c) r := by
  have e : (fun i' : Fin (Alg.symRows (s.m a)) => symTot y a i'.val c) =
      fun i' => y ⟨a, h⟩ i' ⟨c, hc⟩ := funext fun i' => by
    unfold symTot
    rw [dif_pos h, dif_pos i'.isLt, dif_pos hc]
  unfold mzTot colTot
  rw [dif_pos h, dif_pos hc]
  by_cases hr : r < s.m a
  · rw [dif_pos hr, dif_pos hr, e]
    rfl
  · rw [dif_neg hr, dif_neg hr]

/-- **Two entries with the same sizes and the same symbols.** -/
structure SameArr (s : Size) (y : Syms Cb.Gl.E s) (a : ℕ) (s' : Size) (y' : Syms Cb.Gl.E s')
    (a' : ℕ) : Prop where
  /-- both are entries of their lists -/
  here : a < s.NM
  there : a' < s'.NM
  /-- the same rows of cells and the same columns -/
  m : s.m a = s'.m a'
  k : s.k a = s'.k a'
  /-- the same radix of the packing and the same shift -/
  rad : s.rad = s'.rad
  beta : s.beta = s'.beta
  /-- the same symbols -/
  sym : ∀ i c, symTot y a i c = symTot y' a' i c

/-- **The same symbols: the same cells**, at all rows and columns. -/
theorem mzTot_same {s : Size} {y : Syms Cb.Gl.E s} {a : ℕ} {s' : Size} {y' : Syms Cb.Gl.E s'}
    {a' : ℕ} (A : SameArr s y a s' y' a') (r c : ℕ) :
    mzTot (Rows.mzAt y) a r c = mzTot (Rows.mzAt y') a' r c := by
  by_cases hc : c < s.k a
  · rw [mzTot_colTot y A.here hc r, mzTot_colTot y' A.there (A.k ▸ hc) r, A.m, A.rad, A.beta,
      show (fun i => symTot y a i c) = fun i => symTot y' a' i c from funext fun i => A.sym i c]
  · have hc' : ¬ c < s'.k a' := A.k ▸ hc
    unfold mzTot
    rw [dif_pos A.here, dif_pos A.there, dif_neg hc, dif_neg hc']

section
variable {X : Model.Verify.Public} {s : ℕ → Size} {y : ∀ k, Syms Cb.Gl.E (s k)}

/-- **The 23 equations at the lists behind the committed symbols**, from the same sizes and the same
symbols at reader and owner. -/
theorem oneWord_ownOf
    (ff : ∀ g, 0 < g → g < 12 → SameArr (s (2 * g)) (y (2 * g)) (matIx X.y).iXI
      (s (2 * (g - 1))) (y (2 * (g - 1))) (matIx X.y).iXO)
    (att : ∀ g < 12, SameArr (s (2 * g + 1)) (y (2 * g + 1)) ((Hd.shapeA X g).cf.NAs + 3)
      (s (2 * g)) (y (2 * g)) (matIx X.y).iQA) : OneWord X (ownOf s y) :=
  OneWord.of_all (fun g h0 hg r c => mzTot_same (ff g h0 hg) r c)
    fun g hg r c => mzTot_same (att g hg) r c

/-- **At the lists behind the committed symbols hidOf's list of an attention sub-proof IS that
sub-proof's own list**, as functions, at all numbers, rows and columns: so each clause, and any
equation at all names, goes over by rewriting. -/
theorem maOf_ownOf {g : ℕ}
    (att : SameArr (s (2 * g + 1)) (y (2 * g + 1)) ((Hd.shapeA X g).cf.NAs + 3)
      (s (2 * g)) (y (2 * g)) (matIx X.y).iQA) :
    maOf X (ownOf s y) g = ownOf s y (2 * g + 1) :=
  maOf_of_all fun r c => mzTot_same att r c

/-- The same for a group of layers. -/
theorem mgOf_ownOf {g : ℕ}
    (ff : 0 < g → SameArr (s (2 * g)) (y (2 * g)) (matIx X.y).iXI
      (s (2 * (g - 1))) (y (2 * (g - 1))) (matIx X.y).iXO) :
    mgOf X.y (ownOf s y) g = ownOf s y (2 * g) := by
  funext a r c
  unfold mgOf
  by_cases h : a = (matIx X.y).iXI ∧ 0 < g
  · rw [if_pos h, h.1]
    exact (mzTot_same (ff h.2) r c).symm
  · rw [if_neg h]

/-- **The 24th.** -/
theorem headWord_ownOf
    (hd : SameArr (s 24) (y 24) (X.hS.NHf + 3) (s 22) (y 22) (matIx X.y).iXO) :
    HeadWord X (ownOf s y) := fun r _ c _ => mzTot_same hd r c

end

end Meaning

#print axioms Meaning.mzAt_colOf
#print axioms Meaning.mzTot_colTot
#print axioms Meaning.mzTot_same
#print axioms Meaning.oneWord_ownOf
#print axioms Meaning.maOf_ownOf
#print axioms Meaning.mgOf_ownOf
#print axioms Meaning.headWord_ownOf

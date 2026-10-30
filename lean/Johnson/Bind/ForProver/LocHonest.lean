-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/LocHonest.lean: AT A CODE OF AT MOST 2^32 POSITIONS THE FOLD OF THE ENCODED
INDEX'S COLUMN AT A POSITION IS THE FOLDED ROW'S SYMBOL THERE, IN THE LIBRARY'S OWN EQUATION FOR THE
CONSTRAINT (loc_x) of the linear claim's shared rounds (the shared chain) (`Desc.K14.Law.LocEq`,
Johnson/Desc/K14/Law/LawRL.lean): it holds between the column that `encAt` gives
(Johnson/Bind/ForProver/Enc.lean) and the fold of the rows before encoding (`rowLaidE`,
Johnson/Bind/ForProver/K14Rows.lean). Statements and proofs.

Why. In the shared rounds the verifier reads columns of the committed table at sampled positions and
asks that the programs' generator row at the position, applied to the folded row, gives the fold of
the column. `LocEq` is the library's proposition of what that constraint says of words; what ties it
to the verifier's own row is the library's theorem `locMeansW` (Johnson/Desc/K14/Law/MeansLoc.lean).
`LocEq`'s left side bears a name in the library: `genK` (Johnson/Desc/K14/Law/NearRows.lean). An
honest side sends the fold of the rows before encoding; a run reads the columns after encoding. That
the two meet the equation is one of the things that a proof of an honest side's passing that round
would need; no such proof is here.

Main names (namespace `Bind.ForProver`). The three in bold stand at the reading
`OnBytes.Model.Reading.gl` of the programs' elements, at a code of at most 2^32 positions (ha) and a
position that the code has (hx; where a column is given, hc, it follows from that).
  `gl_eOfF`: an element of the base field as the programs' element, read, is its cast.
  `getD_map_ofF`: entry r of a column written as words is the word of the column's entry r.
  `word_is_symF`: the word that `encAt`'s column holds for a row is the format's own symbol
    (`Fmt.M1.symF`) of that row's message and tail, as the stand-in committer on byte strings lays
    them (`Bind.Twin.commitW`, Johnson/Bind/Twin.lean).
  **`symbol_is_generatorRow`**: row by row: that word, read, is `genK` at the row before encoding:
    the programs' generator row applied to it. Over the library's `symF_genK`
    (Johnson/Desc/K14/Law/TabsOne.lean).
  **`locEq_laid`**: at every function ω of coefficients: `LocEq` holds between the column and the
    fold of the rows. (The library calls the fold's coefficients `weights`,
    Johnson/Desc/K14/Text.lean; they are not the model's.)
  `gl_uAtE_below`: below `entries` the folded row of the shared rounds' honest side, read, is the
    sum.
  **`locEq_uAtE`**: where the test `rowsFit` passes: `LocEq` holds between the column and the folded
    row that the honest side of the shared rounds lays (`Desc.K14.Honest.uAtE` at
    `ProofFile.Honest.K14.rowsOf`), at the coefficients eq(gamma, r).

Limits. NOT THE DESCRIPTION'S CONSTRAINT AT A STATE OF A RUN (`Desc.K14.Law.LocAt`): that a state's
coefficients are these, that the words of the sent table at the folded row's places are `uAtE`, and
that the columns handed are `encAt`'s is not said here (Johnson/Bind/ForProver/JoinsLoc.lean has one
half of the last: the column as words). At the reading `Reading.gl` and at no other. Nothing on the
equation or on `genK` at a code of more than 2^32 positions. Nothing on the other constraints of
these rounds, on a proximity test, or on the law of any coin. No completeness of any protocol, no
index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.JoinsK14
import Johnson.Bind.ForProver.K14Folds
import Johnson.Bind.Digits
import Johnson.Desc.K14.Law.NearRows
import Johnson.Desc.K14.Law.TabsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E zeroE generatorAt)
open OnBytes.Params (LinShape FoldeqShape)
open OnBytes.Model (Reading)
open OnBytes.Slice (toF ofF toF_ofF)
open ProofFile.Honest (TableRand eOfF)
open Desc.K14.Law (LocEq genK)

/-- An element of the base field as the programs' element, read, is its cast. -/
theorem gl_eOfF (y : Cb.Gl.F) : Reading.gl.val (eOfF y) = algebraMap Cb.Gl.F Cb.Gl.E y := by
  show Reading.gl.val (OnBytes.ofF (ofF y)) = _
  rw [Desc.K14.Law.gl_ofF, toF_ofF]

/-- Entry r of a column written as words, with the filler 0. -/
theorem getD_map_ofF (col : List Cb.Gl.F) (r : ℕ) :
    (col.map ofF).getD r 0 = ofF (col.getD r 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases col[r]? with
  | none => exact Bind.Column.ofF_zero.symm
  | some y => rfl

section
variable (S : LinShape) (ha : S.fold.index.code.logN ≤ 32) (x : ℕ)
  (hx : x < 2 ^ S.fold.index.code.logN) (w : ProofFile.Honest.Weights) (ρ : TableRand)
  (col : List Cb.Gl.F)
  (hc : encAt (shapeOfIndex S.fold.index) (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ x =
    some col)
include hx hc

/-- The word in the column is the format's own symbol of that row's message and tail. -/
theorem word_is_symF (b : ℕ) (hb : b < 2 ^ S.fold.index.v) :
    ofF (col.getD b 0) =
      Fmt.M1.symF (OnBytes.Slice.codeOf S.fold.index.code) x
        (Bind.Twin.message (shapeOfIndex S.fold.index)
          (tableOfRand (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ) b)
        (Bind.Twin.tailOf (shapeOfIndex S.fold.index)
          (tableOfRand (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ) b) := by
  have hb' : b < (shapeOfIndex S.fold.index).rows := hb
  have hw := encAt_words (shapeOfIndex S.fold.index)
    (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ x hx
  rw [hc, Bind.Twin.columnOf_laid] at hw
  have hw' : col.map ofF = (List.range (shapeOfIndex S.fold.index).rows).map fun b =>
      Fmt.M1.symF (shapeOfIndex S.fold.index).code x
        (Bind.Twin.message (shapeOfIndex S.fold.index)
          (tableOfRand (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ) b)
        (Bind.Twin.tailOf (shapeOfIndex S.fold.index)
          (tableOfRand (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ) b) :=
    Option.some.inj hw
  rw [← getD_map_ofF, hw', getD_map_range _ _ _ _ hb']
  rfl

include ha

/-- **At a code of at most 2^32 positions, row by row: the word in `encAt`'s column, read, is the
programs' generator row applied to the row before encoding.** -/
theorem symbol_is_generatorRow (b : ℕ) (hb : b < 2 ^ S.fold.index.v) :
    Reading.gl.val (OnBytes.ofF (ofF (col.getD b 0))) =
      genK Reading.gl S.fold x (fun k => Reading.gl.val (rowLaidE S w ρ b k)) := by
  rw [word_is_symF S x hx w ρ col hc b hb]
  refine Desc.K14.Law.symF_genK S.fold ha x hx _ _ _ (fun j hj => ?_) fun q hq => ?_
  · rw [rowLaidE_message S w ρ b j hj, gl_eOfF]
  · rw [rowLaidE_tail S w ρ b q hq, gl_eOfF]

/-- **(loc_x)'s equation, at a code of at most 2^32 positions and every function of coefficients**:
between the column and the fold of the rows before encoding. -/
theorem locEq_laid (ω : ℕ → Cb.Gl.E) :
    LocEq Reading.gl S.fold (generatorAt S.fold.index.code x) ω (2 ^ S.fold.index.v)
      (fun r => Reading.gl.val (OnBytes.ofF (ofF (col.getD r 0))))
      (fun k => ∑ r ∈ Finset.range (2 ^ S.fold.index.v),
        ω r * Reading.gl.val (rowLaidE S w ρ r k)) := by
  show genK Reading.gl S.fold x (fun k => ∑ r ∈ Finset.range (2 ^ S.fold.index.v),
    ω r * Reading.gl.val (rowLaidE S w ρ r k)) = _
  rw [Desc.K14.Law.genK_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  exact congrArg (ω r * ·)
    (symbol_is_generatorRow S ha x hx w ρ col hc r (Finset.mem_range.1 hr)).symm

end

/-- Below `entries` the folded row, read, is the sum of the coefficients times the rows. -/
theorem gl_uAtE_below (S : LinShape) (psi : List E) (R : ℕ → ℕ → E) (k : ℕ)
    (hk : k < S.fold.entries) :
    Reading.gl.val (Desc.K14.Honest.uAtE S psi R k) =
      ∑ r ∈ Finset.range (2 ^ S.fold.index.v),
        Reading.gl.val (Desc.K14.Law.eqE (psi.drop S.kLo) r) * Reading.gl.val (R r k) := by
  show Reading.gl.val (Desc.K14.Honest.uHonE S.fold (psi.drop S.kLo) R k) = _
  unfold Desc.K14.Honest.uHonE Desc.K14.Honest.foldRowsE
  rw [if_pos hk, Desc.K14.Law.val_sumE]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Reading.gl.mul]

/-- **(loc_x)'s equation, in the terms of the shared rounds' honest side**: between the column and
the folded row that it lays, at the coefficients eq(gamma, r). -/
theorem locEq_uAtE (S : LinShape) (ha : S.fold.index.code.logN ≤ 32) (x : ℕ)
    (hx : x < 2 ^ S.fold.index.code.logN) (w : ProofFile.Honest.Weights) (ρ : TableRand)
    (col : List Cb.Gl.F)
    (hc : encAt (shapeOfIndex S.fold.index) (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ
      x = some col)
    (hfit : rowsFit (shapeOfIndex S.fold.index) S.kLo S.matrixRows = true) (psi : List E) :
    LocEq Reading.gl S.fold (generatorAt S.fold.index.code x)
      (fun r => Reading.gl.val (Desc.K14.Law.eqE (psi.drop S.kLo) r)) (2 ^ S.fold.index.v)
      (fun r => Reading.gl.val (OnBytes.ofF (ofF (col.getD r 0))))
      (fun k => Reading.gl.val
        (Desc.K14.Honest.uAtE S psi (ProofFile.Honest.K14.rowsOf S w ⟨ρ.pad, ρ.tail⟩) k)) := by
  have htf : S.fold.index.code.ell ≤ S.fold.tailFirst := ell_le_tailFirst S.fold
  have h := locEq_laid S ha x hx w ρ col hc
    fun r => Reading.gl.val (Desc.K14.Law.eqE (psi.drop S.kLo) r)
  rw [uAtE_eq S w ρ hfit psi]
  refine Eq.trans (Desc.K14.Law.genK_congr Reading.gl S.fold x _ _ (fun j hj => ?_)
    fun q hq => ?_) h
  · exact gl_uAtE_below S psi _ j (Nat.lt_of_lt_of_le hj (Nat.le_trans htf (Nat.le_add_right _ _)))
  · exact gl_uAtE_below S psi _ _ (Nat.add_lt_add_left hq _)

end Bind.ForProver

#print axioms Bind.ForProver.gl_eOfF
#print axioms Bind.ForProver.getD_map_ofF
#print axioms Bind.ForProver.word_is_symF
#print axioms Bind.ForProver.symbol_is_generatorRow
#print axioms Bind.ForProver.locEq_laid
#print axioms Bind.ForProver.gl_uAtE_below
#print axioms Bind.ForProver.locEq_uAtE

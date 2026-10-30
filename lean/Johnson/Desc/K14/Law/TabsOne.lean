--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/TabsOne.lean: READ, THE TWO TABLES ARE ONE: the library's stored table of
messages and tails (honestTab, OnBytes/Slice/Honest.lean) and this kind's table of rows before
encoding (tabOfRows, Johnson/Desc/K14/Law/TabOfRows.lean).

  symF_genK        the format's own symbol of a message and a tail (Fmt.M1.symF), read, is genK: the
                   program's row at the position applied to the full message.
  honestCols       the library's table as columns by the position's number. It has code.
  msgOf, tlOf      row n's message and tail, out of rows given by numbers.
  honestCols_col   its columns are the code's symbols of the rows: in the form in which this kind's
                   laws at such a table take it.
  tabs_one         tabF of the one is tabF of the other.

Sg is any record of sizes of the library's (Sz, OnBytes/Slice/LinkAt.lean) with this shape's table
code and number of row variables; its radii and its other fields are not read.

Why. The library's guard honest_decodes (OnBytes/K/Oracle/Decodes.lean) speaks of honestTab; this
kind's laws at a table of code words spoke of tabOfRows, which has no code. Whoever shows that a
border's whole promise can be met needs both at one table.

What is not claimed. That either table is the one beneath a key's root. Equality of the two tables'
words: tabOfRows writes each symbol as the base field's reduced word; that Fmt.M1.symF's words are
reduced is not used. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.TabOfRows
import OnBytes.Slice.Honest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- **The format's own symbol of a message and a tail, read, is genK**: the program's row at the
position applied to a full message U whose entries are the message's and, from tailFirst on, the
tail's. -/
theorem symF_genK (S : FoldeqShape) (ha : S.index.code.logN ≤ 32) (x : Nat)
    (hx : x < 2 ^ S.index.code.logN) (m rho : List UInt64) (U : Nat → Cb.Gl.E)
    (hm : ∀ j < S.index.code.ell, U j = algebraMap Cb.Gl.F Cb.Gl.E (toF (m.getD j 0)))
    (ht : ∀ q < S.index.code.r,
      U (S.tailFirst + q) = algebraMap Cb.Gl.F Cb.Gl.E (toF (rho.getD q 0))) :
    OnBytes.Model.Reading.gl.val (OnBytes.ofF (Fmt.M1.symF (codeOf S.index.code) x m rho)) =
      genK OnBytes.Model.Reading.gl S x U := by
  rw [← genMatrix_mulVec OnBytes.Model.Reading.gl S ⟨x, hx⟩ U, ← mulVec_tie S ha U ⟨x, hx⟩, gl_ofF,
    toF_symF, map_add, map_sum, map_sum]
  show _ = ∑ k : Fin (S.index.code.r + S.index.code.ell),
    genOf (codeOf S.index.code) ⟨x, hx⟩ k * full2 S U k
  rw [Fin.sum_univ_add]
  show (∑ q ∈ Finset.range S.index.code.r, _) + (∑ j ∈ Finset.range S.index.code.ell, _) = _
  rw [Finset.sum_range, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    show _ = algebraMap Cb.Gl.F Cb.Gl.E (ptOf S.index.code.logN ⟨x, hx⟩ ^ q.val) *
      full2 S U (Fin.castAdd _ q)
    unfold full2
    rw [Fin.addCases_left, ht q.val q.isLt, map_mul]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    show _ = algebraMap Cb.Gl.F Cb.Gl.E
        (ptOf S.index.code.logN ⟨x, hx⟩ ^ (S.index.code.r + j.val)) *
      full2 S U (Fin.natAdd _ j)
    unfold full2
    rw [Fin.addCases_right, hm j.val j.isLt, map_mul]
    rfl

/-- The library's stored table of messages and tails (honestTab, OnBytes/Slice/Honest.lean), as
columns by the position's number; empty beyond the table's end. -/
def honestCols (Sg : Sz) (msg tl : Nat → List UInt64) (x : Nat) : List UInt64 :=
  if h : x < 2 ^ Sg.P.T.a then (honestTab Sg msg tl ⟨x, h⟩).2 else []

/-- Row n's message and tail, out of rows before encoding given by numbers. -/
def msgOf (S : FoldeqShape) (RwF : Nat → Nat → UInt64) (n : Nat) : List UInt64 :=
  (List.range S.index.code.ell).map (RwF n)

/-- See msgOf. -/
def tlOf (S : FoldeqShape) (RwF : Nat → Nat → UInt64) (n : Nat) : List UInt64 :=
  (List.range S.index.code.r).map fun q => RwF n (S.tailFirst + q)

/-- **The library's table's columns are the code's symbols of the rows**: in the form in which this
kind's laws at such a table take it (htab_of_cols, nearAt_of_foldRowsB). Sg: any sizes of the
library's with this shape's table code and number of row variables. -/
theorem honestCols_col (Sg : Sz) (S : FoldeqShape) (hT : Sg.P.T = codeOf S.index.code)
    (hv : Sg.P.v = S.index.v) (ha : S.index.code.logN ≤ 32) (RwF : Nat → Nat → UInt64) (x : Nat)
    (hx : x < 2 ^ S.index.code.logN) (n : Nat) (hn : n < 2 ^ S.index.v) :
    OnBytes.Model.Reading.gl.val (OnBytes.ofF
        ((honestCols Sg (msgOf S RwF) (tlOf S RwF) x).toArray.getD n 0)) =
      genK OnBytes.Model.Reading.gl S x
        (fun k => OnBytes.Model.Reading.gl.val (OnBytes.ofF (RwF n k))) := by
  have hx' : x < 2 ^ Sg.P.T.a := by rw [hT]; exact hx
  have hn' : n < 2 ^ Sg.P.v := by rw [hv]; exact hn
  have e : (honestCols Sg (msgOf S RwF) (tlOf S RwF) x).toArray.getD n 0 =
      Fmt.M1.symF (codeOf S.index.code) x (msgOf S RwF n) (tlOf S RwF n) := by
    unfold honestCols honestTab
    rw [dif_pos hx', ← hT]
    simp [Array.getD, hn']
  rw [e]
  refine symF_genK S ha x hx _ _ _ (fun j hj => ?_) fun q hq => ?_
  · rw [gl_ofF]
    unfold msgOf
    simp [List.getD, hj]
  · rw [gl_ofF]
    unfold tlOf
    simp [List.getD, hq]

/-- **READ, THE TWO TABLES ARE ONE.** -/
theorem tabs_one (Sg : Sz) (S : FoldeqShape) (hT : Sg.P.T = codeOf S.index.code)
    (hv : Sg.P.v = S.index.v) (ha : S.index.code.logN ≤ 32) (RwF : Nat → Nat → UInt64) :
    tabF OnBytes.Model.Reading.gl S.index (honestCols Sg (msgOf S RwF) (tlOf S RwF)) =
      tabF OnBytes.Model.Reading.gl S.index (tabOfRows S RwF) := by
  funext b x
  unfold tabF
  rw [honestCols_col Sg S hT hv ha RwF x.val x.isLt _ (numOf_lt _ b),
    tabOfRows_col S RwF x.val _ (numOf_lt _ b)]

end Desc.K14.Law

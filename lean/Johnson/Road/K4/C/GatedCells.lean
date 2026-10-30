-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/GatedCells.lean: CONDITIONAL.

Not shown here. THAT THE MATRICES Mm HOLD THE INPUT's CELLS: CellsAre is a hypothesis. That the
plan's list of matrices is laid as the layout says (MatsLaid) and that the two tensors' features lie
inside their matrix (GatedIn): public hypotheses, for which no law stands. That they can hold
together: no example is known. Of the structure Fits the ties of the cells' names alone are read, no
entry of its world. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The hypothesis `TensorIs` (C/Gated.lean) for the two tensors of the gated products: the input's
tensor, read into the field, is the library's value of the array at the cells of Mm.

  `GatedIn y`   the features of both limbs of the tensors "s" and "u", at every layer of the group
      and every hidden unit, lie inside their matrix. Public.
  `tensor_is`   TensorIs for a tensor of two limbs on the first matrix, whose cells' names are tied.
  `gated_tensors`   the layout has the two tensors, and TensorIs holds of both.
-/
import Johnson.Road.K4.C.Gated
import Johnson.Road.K4.C.Feats
import Johnson.Road.K4.C.Fold
import Johnson.Road.K4.ReadsThere2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr val)
open OnBytes.Desc.First.K4.Honest

/-- **The features of the two tensors lie inside their matrix.** Public. This defines a hypothesis;
the definition claims nothing. -/
structure GatedIn (y : Lay) : Prop where
  s : ∀ X, y.T_ "s" = some X → ∀ l, l < 2 → ∀ ix, ix < y.Lam → ∀ j, j < y.h.f →
    InMat y 0 (tenCell X.place l ix j)
  u : ∀ X, y.T_ "u" = some X → ∀ l, l < 2 → ∀ ix, ix < y.Lam → ∀ j, j < y.h.f →
    InMat y 0 (tenCell X.place l ix j)

variable {Q : K4Pub} {w : K4In} {Mm : Mats Cb.Gl.E} {t : Cell → Cb.Gl.E}

/-- **A tensor of two limbs on the first matrix reads as the library's value.** CONDITIONAL: on
every hypothesis named. -/
theorem tensor_is {A : Arr} {X : Ten} (T : Tied (cellsAt Q.P.y Mm) t A X.mat X.place)
    (hn : X.nl = 2) (hc : A.nCell = 2) (ho : A.off = 0) (hm : X.mat = 0) (C : CellsAre Q w Mm)
    (L : MatsLaid Q)
    (hin : ∀ l, l < 2 → ∀ ix, ix < Q.P.y.Lam → ∀ j, j < Q.P.y.h.f →
      InMat Q.P.y 0 (tenCell X.place l ix j)) : TensorIs Q w t A X := by
  intro ix j i hix hj hi
  have lim : ∀ l, l < 2 → Reading.gl.val (ofF (limbAt Q.P.y w.cell X l ix j i)) =
      t ⟨A, l, ix, j, i⟩ := by
    intro l hl
    rw [T.2 l ix j i, hm]
    show Reading.gl.val (ofF (featCell Q.P.y w.cell X.mat (tenCell X.place l ix j) i)) = _
    rw [hm]
    exact feat_read C L (kind := 0) (hin l hl ix hix j hj) hi
  unfold tensorAt Inst.Model.FFSeg.val
  rw [gl_foldl_maddS, hn, hc, ho, Reading.gl.zero]
  show 0 + ([0, 1].map fun x => Reading.gl.val (ofF (limbAt Q.P.y w.cell X x ix j i)) *
    Reading.gl.val (ofNat (256 ^ x))).sum = _
  rw [List.map_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_cons, List.sum_nil,
    lim 0 (by decide), lim 1 (by decide), gl_numerals.ofNat, gl_numerals.ofNat,
    sum_range_succ, sum_range_succ, sum_range_zero]
  push_cast
  ring

/-- **The two tensors of the gated products.** CONDITIONAL: on every hypothesis named. -/
theorem gated_tensors [scl : Scl] {W : World Cb.Gl.E} {v : Env} {D : Dim}
    {low u : ℕ → Cb.Gl.E} (F : Fits Reading.gl W v D (cellsAt v.y Mm) t low u)
    (hy : Q.P.y = v.y) (La : Laid v.y) (S : Switches v.y.h) (C : CellsAre Q w Mm)
    (L : MatsLaid Q) (I : GatedIn Q.P.y) :
    ∃ ts tu, Q.P.y.T_ "s" = some ts ∧ Q.P.y.T_ "u" = some tu ∧ TensorIs Q w t .sl ts ∧
      TensorIs Q w t .up tu := by
  obtain ⟨tS, _, hS, tiedS, _, _⟩ := F.long .sl rfl
  obtain ⟨tU, _, hU, tiedU, _, _⟩ := F.long .up rfl
  have hts := tensorAt_T hS
  have htu := tensorAt_T hU
  obtain ⟨mS, nS⟩ := ten_facts La S .sl rfl hts
  obtain ⟨mU, nU⟩ := ten_facts La S .up rfl htu
  rw [← hy] at hts htu tiedS tiedU
  exact ⟨tS, tU, hts, htu,
    tensor_is tiedS nS rfl rfl mS C L (I.s tS hts),
    tensor_is tiedU nU rfl rfl mU C L (I.u tU htu)⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.tensor_is
#print axioms OnBytes.Road.K4.C.gated_tensors

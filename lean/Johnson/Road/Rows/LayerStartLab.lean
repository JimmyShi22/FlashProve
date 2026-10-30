-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerStartLab.lean: the record "a group of layers is in order" at matrices that
are named by labels, from the record at matrices that are numbered as the group's list numbers them.

Johnson/Road/Rows/LayerStart.lean gives LayerOrd at the matrices mzTot Mz, numbered as a sub-proof's
list numbers its arrays. The statement on all links (Ords in Johnson/Road/Lane5Top.lean) asks
LayerOrd at mzA y Ma g: matrices Ma that are named by labels, read through the labels labA y g of
group g (Johnson/Road/FormsKeysDictA.lean). This file lays numbered matrices under the labels.

Main definitions: numA y g (the number in the list of group g that has a label), labZ y g Mz (the
numbered matrices Mz under the labels of group g).
Main theorems: numA_labA (numA undoes labA, if the number of the stream that goes out is below 256),
mzA_labZ (read back through the labels, labZ y g Mz is Mz), layer_start_lab.

What is not claimed. That the matrices which different links lay under one label agree
(Hd.LabelsAgree) is not touched: labZ is one link's. The premises of layer_start_base stay. That the
sizes s of the signature are those of the layout yl (numbers of matrices, rows, columns) is not
said: where they fall short the record speaks of the 0 of mzTot. The program does not import this
file.


-/
import Johnson.Road.FormsKeysDictA
import Johnson.Road.Rows.LayerStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows.Norms

open Cb.Pv.Tail
open OnBytes.Model.Layer (Lay Scales matIx)
open Inst.Model (Mat)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (dJ d10)

/-- The number in the list of group g that has the label lab. -/
def numA (y : Lay) (g lab : ℕ) : ℕ :=
  if lab = g * 256 + (matIx y).iXO ∧ g ≠ 0 then (matIx y).iXI else lab - (1 + g) * 256

/-- numA undoes labA. -/
theorem numA_labA (y : Lay) (g n : ℕ) (h : (matIx y).iXO < 256) : numA y g (labA y g n) = n := by
  unfold numA labA
  by_cases h1 : n = (matIx y).iXI ∧ g ≠ 0
  · rw [if_pos h1, if_pos ⟨rfl, h1.2⟩]
    exact h1.1.symm
  · rw [if_neg h1, if_neg (fun hh => by omega)]
    omega

/-- Numbered matrices under the labels of group g. -/
def labZ (y : Lay) (g : ℕ) (Mz : Mats ℤ) : ℕ → ℕ → ℕ → ℤ := fun lab r c => Mz (numA y g lab) r c

/-- Read back through the labels they are the numbered matrices. -/
theorem mzA_labZ (y : Lay) (g : ℕ) (Mz : Mats ℤ) (h : (matIx y).iXO < 256) :
    mzA y (labZ y g Mz) g = Mz := by
  funext n r c
  show Mz (numA y g (labA y g n)) r c = Mz n r c
  rw [numA_labA y g n h]

variable {s : Size}

/-- The record at matrices that are named by labels. -/
theorem layer_start_lab {Jr : Type} (h : Model.Layer.Shape) (sc : Scales) (yl : Lay) (g : ℕ)
    (Wi : Mat) (x : Cm.Seg.XI) {y : Syms Cb.Gl.E s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (hB : BaseAt y Mz)
    (hβ : 2 * (s.beta : ℤ) ≤ 2 ^ 18) (raw : Jr → Cb.Gl.E) (hXO : (matIx yl).iXO < 256)
    (hOwn : ∀ k ν, k < 17 → ν < DF.nNu → ∀ i, i < 2 ^ DF.lT →
      dJ (scl := sclOf h sc g 4) DF (rdAt yl (Sum.elim raw (cellValS y))) k ν i = 0)
    (hHot : ∀ l, l < DF.ne → ∀ i, i < 2 ^ DF.lT →
      d10 DF (rdAt yl (Sum.elim raw (cellValS y))) l i = 0)
    (hE : EmbField h sc yl g (mzTot Mz) Wi x) (hK : KeyField h sc yl g (mzTot Mz) Wi) :
    LayerOrd h sc yl g (mzA yl (labZ yl g (mzTot Mz)) g) Wi x := by
  rw [mzA_labZ yl g (mzTot Mz) hXO]
  exact layer_start_base h sc yl g Wi x hB hβ raw hOwn hHot hE hK

end OnBytes.Road.Rows.Norms

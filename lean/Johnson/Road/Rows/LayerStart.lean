-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerStart.lean: the record "a group of layers is in order" at the integers behind
the committed symbols, from claims on the cells that are read off the committed messages.

Cb/Pv/Tail/Base.lean says what stands behind committed symbols y: small integers Mz, by matrix,
column and row, whose packing y is and whose images are the cells cellValS y (BaseAt). The record
LayerOrd (Johnson/Road/FormsKeysLinkL.lean) speaks of integer matrices by matrix, row and column, on
all numbers. This file lays the one into the other and carries claims over.

Main definitions.
 - mzTot Mz: the integers as matrices on all numbers: row and column exchanged; 0 out of range.
 - matsOf m: the entries m at the cells' places as matrices on all numbers; 0 out of range.
 - rdAt yl m: the library's cells read off the entries m: cellsOf DF (cellsAt yl (matsOf m)).
Main theorems.
 - matsOf_base, rdAt_base: under BaseAt, at the entries "raw entries beside cellValS y", matsOf is
   the image of mzTot Mz, and rdAt is the cells of which LayerOrd speaks.
 - rdAt_lin: rdAt is linear in the entries.
 - small_mzTot: the clause on smallness, if twice the shift is at most 2^18.
 - layer_start_base: BaseAt, the defects dJ and d10 vanishing on the cube of the positions at the
   cells rdAt, and the two fields EmbField and KeyField give LayerOrd at mzTot Mz.

At which sizes. The library's reference sizes DF and the field Cb.Gl.E, as LayerOrd asks.

What is not claimed. EmbField and KeyField are premises, at mzTot Mz. That the numbers of the
matrices in the signature are the verifier's is not said: both are read by the same number. The
program does not import this file.


-/
import Cb.Pv.Tail.Base
import Johnson.Road.Rows.LayerDict

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows.Norms

open Cb.Pv.Tail
open OnBytes.Model.Layer (Lay Scales)
open Inst.Model (Mat)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Cell dJ d10)

variable {s : Size}

/-- The integers behind the symbols as matrices on all numbers: by matrix, row, column. -/
def mzTot (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) : Mats ℤ := fun σ r c =>
  if h : σ < s.NM then
    if hc : c < s.k (⟨σ, h⟩ : Fin s.NM) then
      if hr : r < s.m (⟨σ, h⟩ : Fin s.NM) then Mz ⟨σ, h⟩ ⟨c, hc⟩ ⟨r, hr⟩ else 0
    else 0
  else 0

/-- The entries at the cells' places as matrices on all numbers. -/
def matsOf {K Jr : Type} [Zero K] (m : Jr ⊕ JCell s → K) : Mats K := fun σ r c =>
  if h : σ < s.NM then
    if hc : c < s.k (⟨σ, h⟩ : Fin s.NM) then
      if hr : r < s.m (⟨σ, h⟩ : Fin s.NM) then m (.inr ⟨⟨σ, h⟩, ⟨c, hc⟩, ⟨r, hr⟩⟩) else 0
    else 0
  else 0

/-- Under the lift the matrices read off the entries are the images of the integers. -/
theorem matsOf_base {K Jr : Type} [Field K] {y : Syms K s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (hB : BaseAt y Mz) (raw : Jr → K) :
    matsOf (Sum.elim raw (cellValS y)) = fun σ r c => ((mzTot Mz σ r c : ℤ) : K) := by
  funext σ r c
  unfold matsOf mzTot
  by_cases h : σ < s.NM
  · rw [dif_pos h, dif_pos h]
    by_cases hc : c < s.k (⟨σ, h⟩ : Fin s.NM)
    · rw [dif_pos hc, dif_pos hc]
      by_cases hr : r < s.m (⟨σ, h⟩ : Fin s.NM)
      · rw [dif_pos hr, dif_pos hr]
        exact hB.2.2 ⟨⟨σ, h⟩, ⟨c, hc⟩, ⟨r, hr⟩⟩
      · rw [dif_neg hr, dif_neg hr, Int.cast_zero]
    · rw [dif_neg hc, dif_neg hc, Int.cast_zero]
  · rw [dif_neg h, dif_neg h, Int.cast_zero]

/-- matsOf is linear in the entries. -/
theorem matsOf_lin {K Jr : Type} [Field K] (a b : K) (m m' : Jr ⊕ JCell s → K) (σ r c : ℕ) :
    matsOf (fun j => a * m j + b * m' j) σ r c = a * matsOf m σ r c + b * matsOf m' σ r c := by
  unfold matsOf
  by_cases h : σ < s.NM
  · simp only [dif_pos h]
    by_cases hc : c < s.k (⟨σ, h⟩ : Fin s.NM)
    · simp only [dif_pos hc]
      by_cases hr : r < s.m (⟨σ, h⟩ : Fin s.NM)
      · simp only [dif_pos hr]
      · simp only [dif_neg hr]
        ring
    · simp only [dif_neg hc]
      ring
  · simp only [dif_neg h]
    ring

/-- All entries of mzTot Mz are small. -/
theorem small_mzTot {K : Type} [Field K] {y : Syms K s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (hB : BaseAt y Mz)
    (hβ : 2 * (s.beta : ℤ) ≤ 2 ^ 18) (yl : Lay) : SmallM yl (mzTot Mz) := by
  intro σ r c _
  unfold mzTot
  split_ifs with h hc hr
  · exact lt_of_lt_of_le (hB.1 _ _ _) hβ
  · simp
  · simp
  · simp

/-- The library's cells, read off the entries. -/
def rdAt {Jr : Type} (yl : Lay) (m : Jr ⊕ JCell s → Cb.Gl.E) : Cell → Cb.Gl.E :=
  cellsOf DF (cellsAt yl (matsOf m))

/-- Under the lift they are the cells of which LayerOrd speaks. -/
theorem rdAt_base {Jr : Type} (yl : Lay) {y : Syms Cb.Gl.E s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (hB : BaseAt y Mz)
    (raw : Jr → Cb.Gl.E) :
    rdAt yl (Sum.elim raw (cellValS y)) = cellsOf DF (cellsAt yl (castM (mzTot Mz))) := by
  unfold rdAt
  rw [matsOf_base hB raw]
  rfl

/-- rdAt is linear in the entries. -/
theorem rdAt_lin {Jr : Type} (yl : Lay) (a b : Cb.Gl.E) (m m' : Jr ⊕ JCell s → Cb.Gl.E)
    (c : Cell) :
    rdAt yl (fun j => a * m j + b * m' j) c = a * rdAt yl m c + b * rdAt yl m' c :=
  matsOf_lin a b m m' _ _ _

/-- The record at the integers behind the committed symbols. -/
theorem layer_start_base {Jr : Type} (h : Model.Layer.Shape) (sc : Scales) (yl : Lay) (g : ℕ)
    (Wi : Mat) (x : Cm.Seg.XI) {y : Syms Cb.Gl.E s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (hB : BaseAt y Mz)
    (hβ : 2 * (s.beta : ℤ) ≤ 2 ^ 18) (raw : Jr → Cb.Gl.E)
    (hOwn : ∀ k ν, k < 17 → ν < DF.nNu → ∀ i, i < 2 ^ DF.lT →
      dJ (scl := sclOf h sc g 4) DF (rdAt yl (Sum.elim raw (cellValS y))) k ν i = 0)
    (hHot : ∀ l, l < DF.ne → ∀ i, i < 2 ^ DF.lT →
      d10 DF (rdAt yl (Sum.elim raw (cellValS y))) l i = 0)
    (hE : EmbField h sc yl g (mzTot Mz) Wi x) (hK : KeyField h sc yl g (mzTot Mz) Wi) :
    LayerOrd h sc yl g (mzTot Mz) Wi x := by
  rw [rdAt_base yl hB raw] at hOwn hHot
  exact layer_start (small_mzTot hB hβ yl)
    ((normField_iff h sc yl g (mzTot Mz) Wi x).2 hOwn)
    ((hotField_iff h sc yl g (mzTot Mz) Wi x).2 hHot) hE hK

end OnBytes.Road.Rows.Norms

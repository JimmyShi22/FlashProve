-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/Rel2Layers.lean: the field relations of the 24 segments of the layers, and what a table of scales
with `LawfulK` gives of the segments of a group.

The field relation of a segment says: every cell is small, and modulo p every key is an entry of its
table and every identity holds (for a feed-forward segment: `TraceSpec.RF`, Blocks/Segment.lean).

Main names:
  `RFL p κ nf tbG W tok T`: the field relations of the 24 segments, and `last`: the stream after
    the last
    layer, as the head reads it from the cells that it borrows, is below 2^39 in absolute value at
    every position and channel. The third clause is what the conditions of a head's final
    normalisation give (for the plain head with the scaled table: `Plain.TP.noWrap`,
    Cm/TargetPHeadNoWrap.lean, under its hypotheses); here it is a hypothesis.
  `settingK`, `sizeOKK`, `expTabK`, `rowsK`, `ffK`, `fitK`: what a lawful table gives of a group.

Limits: this file says nothing on logits, requests or replies: no request occurs in this file.

Terms: lean/GLOSSARY.md.
-/
import Inst.Model.All.TraceK
import Inst.Model.All.NoWrap

set_option autoImplicit false

/- no default table of scales is in sight in this file: what reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Lay

open Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef hRef)

/-- The field relations of the 24 segments of the layers, and the bound that a head gives. -/
structure RFL (p : ℕ) (κ : ℕ → LayerScale) (nf : NormPar) (tbG : ℕ → Tables) (W : Mat)
    (tok : ℕ → ℕ) (T : Trace) : Prop where
  ff : ∀ g < nGr,
    (FFSeg.trace (scl := SFK κ nf g) FFSeg.Dim.ref (tbG g) kRef (4 * g)
        (decide (g = 0)) (ZMod p)).RF
      tok (fun r c => ((W r c : ℤ) : ZMod p)) fun c => T.vFF g c.val
  att : ∀ g < nGr, AttSeg.RFraw (scl := SFK κ nf g) (DAK κ g) (tbG g) (ZMod p) (T.vAtt g)
  last : ∀ i < Head.nT, ∀ j < Head.nD, |Head.xAt T.vHead i j| < 2 ^ 39

/-- the parameters of layer L -/
abbrev PK (κ : ℕ → LayerScale) (L : ℕ) : Params := ppref.at (κ L)

theorem PG_lt (κ : ℕ → LayerScale) (g : ℕ) {l : ℕ} (hl : l < 4) : PG κ g l = PK κ (4 * g + l) := by
  show ppref.at (kapG κ g l) = _
  rw [kapG_lt κ g hl]

section Facts
variable {κ : ℕ → LayerScale} {nf : NormPar} {tbG : ℕ → Tables} {W : Mat}
  {tok : ℕ → ℕ} (hL : LawfulK κ nf tbG) (hW : Layout.WFW ppref kRef W hRef)
  (htok : ∀ i, tok i < ppref.V)

include hL hW htok in
theorem settingK {g : ℕ} (hg : g < nGr) : FFSeg.SettingK (kapG κ g) nf (tbG g) W (4 * g) tok :=
  FFSeg.Spec.Setting.mk (scl := SFK κ nf g) (hL.tab g hg) hW (by omega) (by
    show 4 * g + 4 ≤ 48
    unfold nGr at hg
    omega) htok

include hL in
theorem sizeOKK {g : ℕ} (hg : g < nGr) : AttSeg.SizeOK (scl := SFK κ nf g) (DAK κ g) :=
  AttSeg.SizeOK.mk (scl := SFK κ nf g) (by decide : AttSeg.Dim.ref.ch ≤ 128)
    (by decide : AttSeg.Dim.ref.lT ≤ 10) (by decide : AttSeg.Dim.ref.T ≤ 1024) (hL.ex g hg)

include hL in
theorem expTabK {g : ℕ} (hg : g < nGr) : AttSeg.ExpTab (DAK κ g) (tbG g) :=
  ⟨fun u hu => (hL.tab g hg).2.2.2.1 u hu, (hL.tab g hg).2.2.2.2⟩

include hL in
/-- the live rows of a layer, as an integer and as a number -/
theorem rowsK {g : ℕ} (hg : g < nGr) (l : ℕ) :
    (kapG κ g l).expRows = (((κ (4 * g)).expRows.toNat : ℕ) : ℤ) := by
  have := (hL.ex g hg).pos
  rw [hL.rows g hg (l % 4) (Nat.mod_lt _ (by norm_num))]
  omega

include hL in
/-- under `hL`, `hg`: every word of a group is lawful -/
theorem ffK {g : ℕ} (hg : g < nGr) (l : ℕ) : FFSeg.LawfulW (kapG κ g l) :=
  hL.ff _ (by have := Nat.mod_lt l (show 0 < 4 by norm_num); unfold nGr at hg; omega)

include hL in
theorem fitK {g : ℕ} (hg : g < nGr) (l : ℕ) :
    AttSeg.NW2.Fit (scl := SFK κ nf g) (DAK κ g) (PG κ g l) :=
  AttSeg.NW2.Fit.mk (scl := SFK κ nf g) (by decide : AttSeg.Dim.ref.ch = ppref.ch)
    (by decide : AttSeg.Dim.ref.na = ppref.nq / ppref.nkv) (by decide : 0 < AttSeg.Dim.ref.na)
    (rowsK hL hg l) (hL.one g hg (l % 4) (Nat.mod_lt _ (by norm_num)))

/-! ## The computation -/

theorem XK_even (tbs : ℕ → Tables) (i : Weights) (prompt : Fin ppref.T → Fin ppref.V)
    {n : ℕ} (hn : n % 2 = 0) :
    XK ppref κ tbs i prompt (n + 1) =
      Att.x' (PK κ (n / 2)) (tbs (n / 2)) (i.layer (n / 2)) (n / 2) (XK ppref κ tbs i prompt n) :=
  if_pos hn

theorem XK_odd (tbs : ℕ → Tables) (i : Weights) (prompt : Fin ppref.T → Fin ppref.V)
    {n : ℕ} (hn : ¬ n % 2 = 0) :
    XK ppref κ tbs i prompt (n + 1) =
      FF.x'' (PK κ (n / 2)) (tbs (n / 2)) (i.layer (n / 2)) (n / 2) (XK ppref κ tbs i prompt n) :=
  if_neg hn

theorem tbsOf_at (tbG : ℕ → Tables) (g : ℕ) {l : ℕ} (hl : l < 4) :
    tbsOf tbG (4 * g + l) = tbG g := by
  unfold tbsOf
  rw [show (4 * g + l) / 4 = g by omega]

end Facts

end Cm.Lay

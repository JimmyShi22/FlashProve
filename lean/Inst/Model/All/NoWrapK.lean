-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/All/NoWrapK.lean: facts on the groups of the whole model for all valid scales (`LawfulK`,
Inst/Model/Scales.lean), the steps of the stream at the scales, and that the reference scales are
valid (`lawfulK_const`).

The counterpart of Parts B and C of Inst/Model/All/NoWrap.lean (at the reference parameters).
Notation:
  `XK`: "The residual stream, with layer L at its scales and tables." (Inst/Model/Program.lean)
Limits: nothing on the chain; no claim is made that any valid scales suit the weights of any real
model (that the reference scales are valid: `lawfulK_const`, under its hypothesis on the tables;
where their numbers come from: lean/CREDITS.md, section 8).
-/
import Inst.Model.All.TraceK
import Inst.Model.All.NoWrap
import Inst.Model.Head.NoWrapPolicy
import Inst.Model.Head.NoWrapProgramN
import Inst.Model.ProgramRPol

set_option autoImplicit false

/- no default scales are in sight in this file: what reads scales says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.All

open Finset
open Layout (kRef hRef)

/-- the parameters of layer L -/
abbrev PK (κ : ℕ → LayerScale) (L : ℕ) : Params := ppref.at (κ L)

theorem PG_lt (κ : ℕ → LayerScale) (g : ℕ) {l : ℕ} (hl : l < 4) : PG κ g l = PK κ (4 * g + l) := by
  show ppref.at (kapG κ g l) = _
  rw [kapG_lt κ g hl]

section Facts
variable {κ : ℕ → LayerScale} {nf : NormPar} {tbG : ℕ → Tables} {W : Mat}
  {tok : ℕ → ℕ} (hL : LawfulK κ nf tbG)
  (hW : Layout.WFW ppref kRef W hRef) (htok : ∀ i, tok i < ppref.V)

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
/-- the rows in use of a layer, as an integer and as a number -/
theorem rowsK {g : ℕ} (hg : g < nGr) (l : ℕ) :
    (kapG κ g l).expRows = (((κ (4 * g)).expRows.toNat : ℕ) : ℤ) := by
  have := (hL.ex g hg).pos
  rw [hL.rows g hg (l % 4) (Nat.mod_lt _ (by norm_num))]
  omega

include hL in
/-- under `hL` the scales of every layer of a group are valid -/
theorem ffK {g : ℕ} (hg : g < nGr) (l : ℕ) : FFSeg.LawfulW (kapG κ g l) :=
  hL.ff _ (by have := Nat.mod_lt l (show 0 < 4 by norm_num); unfold nGr at hg; omega)

include hL in
theorem fitK {g : ℕ} (hg : g < nGr) (l : ℕ) :
    AttSeg.NW2.Fit (scl := SFK κ nf g) (DAK κ g) (PG κ g l) :=
  AttSeg.NW2.Fit.mk (scl := SFK κ nf g) (by decide : AttSeg.Dim.ref.ch = ppref.ch)
    (by decide : AttSeg.Dim.ref.na = ppref.nq / ppref.nkv) (by decide : 0 < AttSeg.Dim.ref.na)
    (rowsK hL hg l) (hL.one g hg (l % 4) (Nat.mod_lt _ (by norm_num)))

/-! ## The stream -/

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

/-- the reference scales, the reference final normalisation and any tables with the ranges of (Tab)
(`tb.OK ppref`) are valid -/
theorem lawfulK_const {tb : Tables} (htb : tb.OK ppref) :
    LawfulK (fun _ => ppref.scale) ppref.nf fun _ => tb :=
  ⟨fun _ _ => FFSeg.lawfulW_ref, Head.nf_ok, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => expOK_ref, fun _ _ => htb⟩

end Inst.Model.All

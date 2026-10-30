-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/IdnOfField.lean: CONDITIONAL.

Not shown here. THAT THE LIBRARY's `NormField` OR `HotField` (Johnson/Road/Rows/LayerTop.lean) HOLDS
OF ANY LIST OF INTEGERS: both are hypotheses. THAT THE CELLS READ OFF THE MATRICES Mm ARE THE CELLS
OF THAT LIST: hC is a hypothesis (W/MatsOfList.lean has it from one hypothesis on the committed
symbols). That `FullAt` holds at what a hearing returns: six public equations, shown of no plan
here. Of the hypotheses together no example is known. THE FULL SIZE ALONE: the library's two
sentences stand at its reference sizes `DF`, at four layers in a group and at the field Cb.Gl.E: at
a smaller plan nothing here applies. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import: no module under
Johnson/Goal/, Johnson/D/ or ThirdParty/, and none whose name holds RecCompile. It imports nothing
of the honest side (Johnson/Desc/ProofFile/Honest/).

The hypotheses `IdnHold` (W/Ground.lean) and `HotCube` (W/HotEmb.lean) of the statements on the
claims of the feed-forward layers' own rounds (sub-protocol K4), from the library's two sentences on
a group of layers at a list of integer matrices. Statements with their proofs: calls of the
library's `normField_iff` and `hotField_iff` (Johnson/Road/Rows/LayerDict.lean), and rewriting.

  `idnHold_of_field`, `hotCube_of_field`   general in the list Mz and in the matrices Mm, under hC.
  `FullAt X g h D o`   six public equations: what a hearing has returned (o) has the layout, the
      scales and the group of the public parameters X, four layers in a group; h is X's shape of a
      layer; D is the library's reference sizes.
  `idnHold_full`   the form of the field idn of `ItemOpens` (W/Item.lean): at sclOf h o.v.sc o.v.g
      o.v.y.Lam, D and o.v.y.
  `hotCube_full`   `HotCube` at the same D and o.v.y; the field hot, which asks `HotPoint` at one
      point, follows by `hotPoint_of_cube` (W/HotEmb.lean).
-/
import OnBytes.Model.VerifyPublic
import Johnson.Road.Rows.LayerDict
import Johnson.Road.K4.W.Ground
import Johnson.Road.K4.W.HotEmb

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Scales Own)
open OnBytes.Road.Rows.Norms (NormField HotField castM normField_iff hotField_iff)
open Inst.Model (Mat Scl)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dim)

variable {h : Layer.Shape} {sc : Scales} {y : Lay} {g : ℕ} {Mz : Mats ℤ} {Wi : Mat}
  {x : Cm.Seg.XI} {Mm : Mats Cb.Gl.E}

/-- **The seventeen identities of each norm, from the library's sentence at a list of integers.**
CONDITIONAL: on hN and hC. -/
theorem idnHold_of_field (hN : NormField h sc y g Mz Wi x)
    (hC : cellsOf DF (cellsAt y Mm) = cellsOf DF (cellsAt y (castM Mz))) :
    IdnHold (scl := sclOf h sc g 4) DF (cellsOf DF (cellsAt y Mm)) := by
  letI : Scl := sclOf h sc g 4
  refine ⟨fun ν hν k hk i hi => ?_⟩
  rw [hC]
  exact (normField_iff h sc y g Mz Wi x).1 hN k ν hk hν i hi

/-- **The selector's identity at every routed layer and position, from the library's sentence.**
CONDITIONAL: on hH and hC. -/
theorem hotCube_of_field (hH : HotField h sc y g Mz Wi x)
    (hC : cellsOf DF (cellsAt y Mm) = cellsOf DF (cellsAt y (castM Mz))) :
    HotCube DF (cellsOf DF (cellsAt y Mm)) :=
  fun l hl i hi => by
    rw [hC]
    exact (hotField_iff h sc y g Mz Wi x).1 hH l hl i hi

/-- **What a hearing has returned stands at the public parameters X, at the full size.** This
defines a hypothesis; the definition claims nothing. -/
structure FullAt (X : Verify.Public) (g : ℕ) (h : Layer.Shape) (D : Dim) (o : Own) : Prop where
  /-- the shape of a layer is the public parameters' -/
  shape : h = Verify.layerShape X.P
  /-- the sizes are the library's reference sizes -/
  dim : D = DF
  /-- the layout -/
  lay : o.v.y = X.y
  /-- the scales -/
  sc : o.v.sc = X.layers.sc
  /-- the group -/
  grp : o.v.g = g
  /-- four layers in a group -/
  lam : o.v.y.Lam = 4

variable {X : Verify.Public} {D : Dim} {o : Own}

/-- **`IdnHold` in the form of the field idn of `ItemOpens`.** CONDITIONAL: on Fu, hN and hC. -/
theorem idnHold_full (Fu : FullAt X g h D o)
    (hN : NormField (Verify.layerShape X.P) X.layers.sc X.y g Mz Wi x)
    (hC : cellsOf DF (cellsAt X.y Mm) = cellsOf DF (cellsAt X.y (castM Mz))) :
    IdnHold (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm)) := by
  rw [Fu.lam, Fu.lay, Fu.sc, Fu.grp, Fu.shape, Fu.dim]
  exact idnHold_of_field hN hC

/-- **`HotCube` at the same cells.** CONDITIONAL: on Fu, hH and hC. -/
theorem hotCube_full (Fu : FullAt X g h D o)
    (hH : HotField (Verify.layerShape X.P) X.layers.sc X.y g Mz Wi x)
    (hC : cellsOf DF (cellsAt X.y Mm) = cellsOf DF (cellsAt X.y (castM Mz))) :
    HotCube D (cellsOf D (cellsAt o.v.y Mm)) := by
  rw [Fu.lay, Fu.dim]
  exact hotCube_of_field hH hC

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.idnHold_of_field
#print axioms OnBytes.Road.K4.W.hotCube_of_field
#print axioms OnBytes.Road.K4.W.idnHold_full
#print axioms OnBytes.Road.K4.W.hotCube_full

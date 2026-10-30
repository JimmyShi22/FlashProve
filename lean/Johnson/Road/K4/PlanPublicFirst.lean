-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PlanPublicFirst.lean: THE PREMISES OF THE FIRST GROUP's MAPS (`Plan4F.MeetsF`,
Johnson/Road/K4/PlanMapsFirst.lean) AT A PLACE THAT HOLDS THE PUBLIC PART's OWN RECORD AND PLAN. One
statement: the twin of `Plan4.meets_public` (Johnson/Road/K4/PlanPublic.lean).

  `Plan4F.meetsF_public`: where `Verify.publicOf` returns X, the place holds X's record of the
    layers (with whatever tokens) and X's plan of the group, and the group is the first: four of the
    ten fields are shown (the layout, the reads, the plan's two numbers).

Limits. SIX FIELDS STAY PREMISES, handed through: that K4's text covers the record (hc); that the
library's sizes agree with the parameter file's shape (Z); three choices of the value's letters (kW,
ls, gB); and that the place's group is the first.
-/
import Johnson.Road.K4.PlanMapsFirst
import Johnson.Road.K4.PlanPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (Public publicOf layerShape)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers Par)

variable [scl : Scl] {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **The premises of the first group's maps hold at a place that holds the public part's record and
plan**: four of the ten are shown; hc, Z, wk, hg, hls, hB are handed through. -/
theorem Plan4F.meetsF_public {M Xs : Type} (Q : Plan4F Cb.Gl.E M Xs)
    (h : publicOf pol KL lay = .ok X) {p : Par} {tk : Array Nat}
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hc : covers X.layers = true) (Z : Sized (layerShape X.P) Q.D)
    (wk : Q.kW = X.layers.wsLay.lk) (hg : (p.g == 0) = true) (hls : Q.ls = X.layers.y.ls)
    (hB : Q.gB = X.layers.y.lPd - X.layers.y.ls) :
    Q.MeetsF p (layerShape X.P) X.P.polCalls where
  hy := by rw [hP]; exact (Hd.publicH_of_public h).lay
  hc := by rw [hP]; exact hc
  hrd := by rw [hP]; exact Model.Fit.public_reads h
  Z := Z
  hl := by rw [hP]; exact (planG_sizes (Fo.Pub.public_G h p.g p.hp hG)).1
  hn := by rw [hP]; exact (planG_sizes (Fo.Pub.public_G h p.g p.hp hG)).2
  wk := by rw [hP]; exact wk
  hg := hg
  hls := by rw [hP]; exact hls
  hB := by rw [hP]; exact hB

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.meetsF_public

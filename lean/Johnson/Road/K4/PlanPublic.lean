-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PlanPublic.lean: THE PREMISES ON SIZES, PAID AT WHAT THE VERIFIER's PUBLIC PART
RETURNS. PlanSizes.lean and PlanMaps.lean ask that a layout, tables of reads and a plan are what
`layout`, `readsOf` and `planG` return. Here they are those of the record X that
`Verify.publicOf` returns (OnBytes/Model/VerifyPublic.lean) and of the member number g of its list
of plans X.G. Two short theorems: an assembly of three statements on `publicOf`.

  `dimIs_of_public`: if `publicOf pol KL lay = .ok X`, X.G's member number g is hp, K4's text covers
    X.layers, and the library's sizes D agree with the shape of X's parameter file (`Sized`), then
    `DimIs D (Verify.layerNumbers P hp g)` at P := X.layers with whatever tokens tk laid in.
  `Plan4.meets_public`: then the record `Plan4.Meets` (PlanMaps.lean) holds at a place p whose
    public record is that P, whose plan is X.G's member number p.g, in a group that is not the
    first, if the value's number of rounds of the merge is the committed matrix's layout's.

The payers: `Hd.publicH_of_public` (Johnson/Road/HeadMade.lean: the layout);
`Model.Fit.public_reads` (OnBytes/Model/Fit/LayerCaps.lean); `Fo.Pub.public_G`
(OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean).

Limits. That K4's text covers X.layers stays a premise (a hearing's return gives it:
`hear_parts_first`, `hear_parts_later`); so do `Sized` (`dimOf` of the shape meets it) and the
equation on the merge's rounds, which are choices of the value's letters. That a block's place
holds X's record and plan is a premise. Equations between numbers alone.
-/
import Johnson.Road.K4.PlanMaps
import Johnson.Road.HeadMade
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Tie.Pv.Lay.At (DimIs)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (covers Par)

variable [scl : Scl] {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **The library's sizes are the planner's at the public part's own record and plan**: where K4's
text covers the record and D agrees with the parameter file's shape. -/
theorem dimIs_of_public (h : publicOf pol KL lay = .ok X) {g : ℕ} {hp : Layer.HPlan2}
    (hG : X.G[g]? = some hp) (hc : covers X.layers = true) {D : Dim}
    (Z : Sized (layerShape X.P) D) (tk : Array Nat) :
    DimIs D (Verify.layerNumbers { X.layers with tokv := tk } hp g) :=
  dimIs_layerNumbers (P := { X.layers with tokv := tk }) (Hd.publicH_of_public h).lay hc
    (Model.Fit.public_reads h) Z (planG_sizes (Fo.Pub.public_G h g hp hG)).1
    (planG_sizes (Fo.Pub.public_G h g hp hG)).2

/-- **The premises of the maps hold at a place that holds the public part's record and plan.** -/
theorem Plan4.meets_public {M Xs : Type} (Q : Plan4 Cb.Gl.E M Xs)
    (h : publicOf pol KL lay = .ok X) {p : Par} {tk : Array Nat}
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hc : covers X.layers = true) (Z : Sized (layerShape X.P) Q.D)
    (wk : Q.kW = X.layers.wsLay.lk) (hg : (p.g == 0) = false) :
    Q.Meets p (layerShape X.P) X.P.polCalls where
  hy := by rw [hP]; exact (Hd.publicH_of_public h).lay
  hc := by rw [hP]; exact hc
  hrd := by rw [hP]; exact Model.Fit.public_reads h
  Z := Z
  hl := by rw [hP]; exact (planG_sizes (Fo.Pub.public_G h p.g p.hp hG)).1
  hn := by rw [hP]; exact (planG_sizes (Fo.Pub.public_G h p.g p.hp hG)).2
  wk := by rw [hP]; exact wk
  hg := hg

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.dimIs_of_public
#print axioms OnBytes.Road.K4.Plan4.meets_public

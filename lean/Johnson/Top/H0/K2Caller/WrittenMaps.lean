-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WrittenMaps.lean: the bound of MeetsOfCovered.lean along a READING of a
file's rounds: for every reading M of written rounds as a block's typed rounds that skips no round
(`Maps`, OnBytes/Flat/CarrySMaps.lean), the written counts `M.err ε` are shares of at most
2⁻¹ ^ target; and the same at the code switch.

`Maps.err` is the form in which a piece of a file's description has its error, and `Maps.fits` says
that these counts bear the typed ones where M is in order. The bound is the library's
`Maps.below_held` (OnBytes/Flat/CarrySBelow.lean), whose two premises MeetsOfCovered.lean shows.
Theorems with their proofs.

Main names:
  `maps_below`: general in the block.
  `Letters.mapsBelow`: at the caller of the code switch, for all letters and every such reading.
  `K02WrittenMaps`, `k02WrittenMaps`: the same as one closed proposition; its proof.

Limits: those of MeetsOfCovered.lean and WrittenMeets.lean. The reading M is a letter: no reading of
a switch's two written rounds is written here, and none is shown to be in order. It is no soundness
of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WrittenMeets
import OnBytes.Flat.CarrySBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.G4 OnBytes.Flat OnBytes.Maker Iop
open scoped ENNReal

/-- **Along a reading that skips no round.** -/
theorem maps_below (σ : Setting) (c : Scope) (F : Type) (hp : σ.p = 2 ^ 64 - 2 ^ 32 + 1)
    (hd : σ.degree = 3) {ds : List RDT} {s : Shape} (M : Maps ds s) (ε : Err s)
    (ys : List RoundSpec) (hm : M.marks = allRead (ds.map toRD))
    (hS : ShapeIsAll GE F s (ys.map fun y => (y.round σ c).entry))
    (hC : List.Forall₂ (Cb.Pv.Covered σ c) (ε.toList.zip s.chalList) ys)
    (hD : WrittenAs σ c (ds.map toRD) ys) (hF : ∀ y ∈ ys, Fine σ c y) :
    Err.Below (M.err ε) ((2 : ℝ≥0∞)⁻¹ ^ σ.target) :=
  Maps.below_held σ M (ys.map fun y => y.round σ c) ε
    (premises_of_covered σ c F hp hd s ε ys _ hS hC hD hF).1
    (hm ▸ (premises_of_covered σ c F hp hd s ε ys _ hS hC hD hF).2)

/-- **At the code switch.** -/
theorem Letters.mapsBelow {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h)) {ds : List RDT}
    (M : Maps ds (Cb.Pv.SendLocRide.R X.caller).shape) (hm : M.marks = allRead (ds.map toRD))
    (hd : WrittenAs r.set .request (ds.map toRD) r.specs) :
    Err.Below (M.err (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) := by
  unfold SwRow.writtenOK at hW
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hW
  exact maps_below r.set .request Unit ((r.ok_says h).p.trans p_is) (r.ok_says h).degree M _ r.specs
    hm (X.shape Unit hW.2) (Letters.holds h X).2 hd fun y hy => fine_of (hW.1 y hy)

/-- **As one closed proposition.** -/
def K02WrittenMaps : Prop :=
  ∀ (r : SwRow) (h : r.ok = true), r.writtenOK = true →
    ∀ (X : Letters r (r.ok_says h)) (ds : List RDT)
      (M : Maps ds (Cb.Pv.SendLocRide.R X.caller).shape), M.marks = allRead (ds.map toRD) →
      WrittenAs r.set .request (ds.map toRD) r.specs →
      Err.Below (M.err (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^ r.set.target)

theorem k02WrittenMaps : K02WrittenMaps := fun _ h hW X _ M hm hd =>
  Letters.mapsBelow h hW X M hm hd

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.maps_below
#print axioms VerifiableInference.Desc.First.K2Caller.Letters.mapsBelow
#print axioms VerifiableInference.Desc.First.K2Caller.k02WrittenMaps

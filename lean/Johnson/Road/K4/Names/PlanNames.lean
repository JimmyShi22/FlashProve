-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Names/PlanNames.lean: WHAT A LAYERS' PLAN KEEPS OF ITS SHAPE's LISTS, AND WHAT IT
LAYS FOR THE MATRIX THAT IT READS FROM THE GROUP BEFORE: where planG (OnBytes/Model/LayerPlan.lean)
returns hp, the fields ix, gtTree, pkMat, pxMat of hp.tl are those of what shapeF returned at
bordersOf's three lists; hp.tl.ix.FT has no entry at the first group and one at a later group; and
at a later group entry 0 of hp.tl.plFor names the group before as the owner and the last of the
owner's arrays that another sub-proof reads. No scope is asked.

  `SameN a b`: the four fields are one. Its laws along addTreesF, ownerIs, borderMeans.
  `borderMeans_cut`: what borderMeans lays at entry iF of plFor.
  **`planG_names`**: see its statement. Premise: planG returns.
The walk is that of planG_gt (Johnson/Goal/Meaning/PlanPort.lean).
Limits. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Names.ShapePx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Names
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan OnBytes.Tie.Pv.Tail.Port
open OnBytes.Road (false_of_refuseIf)
open Fo.BatRows (bindE_ok)

/-- Four fields are one. -/
structure SameN (a b : HTailF2) : Prop where
  ix : b.ix = a.ix
  gtTree : b.gtTree = a.gtTree
  pkMat : b.pkMat = a.pkMat
  pxMat : b.pxMat = a.pxMat

theorem SameN.trans {a b c : HTailF2} (h : SameN a b) (k : SameN b c) : SameN a c :=
  ⟨k.ix.trans h.ix, k.gtTree.trans h.gtTree, k.pkMat.trans h.pkMat, k.pxMat.trans h.pxMat⟩

theorem addTreesF_sameN {tl tl' : HTailF2} {F F' : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    SameN tl tl' := by
  obtain ⟨-, -, e⟩ := addTreesF_fits tl tl' F F' T T' nU aTX hb hbLine h
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ownerIs_sameN (tl : HTailF2) (no : Nat) : SameN tl (tl.ownerIs no) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- What borderMeans keeps, and what it lays at entry iF of plFor. -/
theorem borderMeans_cut {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') :
    SameN tl tl' ∧ ∃ pl, tl'.plFor[iF]? = some pl ∧ pl.owner = some ownerNo ∧
      pl.rootIndex = some index := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · rename_i pl hpl
    split at e
    · cases e
    · cases e
      refine ⟨⟨rfl, rfl, rfl, rfl⟩,
        { pl with owner := some ownerNo, rootIndex := some index }, ?_, rfl, rfl⟩
      show (tl.plFor.setIfInBounds iF _)[iF]? = _
      rw [Array.getElem?_setIfInBounds, if_pos rfl, if_pos (Array.getElem?_eq_some_iff.1 hpl).1]

/-- **What a layers' plan keeps of its shape's lists, and what it lays at the seam.** -/
theorem planG_names {P : Layer.Pub} {g : Nat} {O : Option Layer.HPlan2} {hp : Layer.HPlan2}
    (h : Layer.planG P g O = .ok hp) :
    ∃ mats txOf ft tl0,
      Layer.bordersOf P.y (P.tails.getD g {}).mats = .ok (mats, txOf, ft) ∧
      ({ tau := P.set.tau, lidb := P.set.lidb } : HTailF2).shapeF mats txOf ft
        #[false, false, true, false] P.y.h.tau = .ok tl0 ∧
      SameN tl0 hp.tl ∧ hp.tl.ix.FT.size = (if g == 0 then 0 else 1) ∧
      ∀ Oo, O = some Oo → ∃ pl, hp.tl.plFor[0]? = some pl ∧ pl.owner = some (g - 1) ∧
        pl.rootIndex = some (Oo.tl.pkMat.size + Oo.tl.ix.TX.size - 1) := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, hb, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, hFT, h⟩ := bindE_ok h
  have hF : tl1.ix.FT.size = (if g == 0 then 0 else 1) := by
    have := false_of_refuseIf hFT
    simpa using this
  have N1 : SameN tl tl1 := addTreesF_sameN hA
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact ⟨mats, txOf, ft, tl, hb, hS, N1.trans (ownerIs_sameN tl1 g), hF,
      fun Oo e => by cases e⟩
  · rename_i Oo'
    split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      obtain ⟨N2, pl, p1, p2, p3⟩ := borderMeans_cut hB
      dsimp only
      rw [hy]
      refine ⟨mats, txOf, ft, tl, hb, hS, (N1.trans (ownerIs_sameN tl1 g)).trans N2, ?_,
        fun Oo e => ?_⟩
      · rw [N2.ix]
        exact hF
      · obtain rfl := Option.some.inj e
        exact ⟨pl, p1, p2, p3⟩
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

end OnBytes.Road.K4.Names

#print axioms OnBytes.Road.K4.Names.borderMeans_cut
#print axioms OnBytes.Road.K4.Names.planG_names

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Plan/ShapeRowsG.lean: THE SHAPE EQUATION OF ShapeRows.lean AT THE LAYERS' PLAN: in
every plan that Layer.planG (OnBytes/Model/LayerPlan.lean) returns, and so in every layers' plan of
what Verify.publicOf returns, each matrix's shape has a third of its rows of cells, rounded up, as
its rows of symbols.

  `SameShp a b`: b has a's number of matrices, shapes and matrices. `ownerIs_shp`,
    `borderMeans_shp`: the two routines that planG runs behind addTrees keep them (the first turns
    plOwn alone, the second plFor alone). `mS_of_same`: the equation goes along.
  **`planG_mS`** : Layer.planG P g O = .ok hp → ∀ mu, mu < hp.tl.NM → (hp.tl.shp.getD mu {}).mS =
    ((hp.tl.mats.getD mu {}).m + 2) / 3.
  **`public_G_mS`**: the same at X.G[g]? = some hp, where Verify.publicOf pol KL layout = .ok X.
How. One call of `addTreesF_mS`; the opening of planG's text is that of `planG_K3`
(Johnson/Goal/Meaning/PlanPort.lean).
Limits. That the planner returns anywhere is not said. `public_G_mS` speaks at Verify.publicOf, not
at the form with the hash as a letter (publicOfO). Nothing on soundness.

-/
import Johnson.Road.K4.Plan.ShapeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Plan

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open Fo.BatRows (bindE_ok)

/-- b has a's number of matrices, shapes and matrices. -/
structure SameShp (a b : HTailF2) : Prop where
  NM : b.NM = a.NM
  shp : b.shp = a.shp
  mats : b.mats = a.mats

theorem SameShp.trans {a b c : HTailF2} (h : SameShp a b) (k : SameShp b c) : SameShp a c :=
  ⟨k.NM.trans h.NM, k.shp.trans h.shp, k.mats.trans h.mats⟩

/-- ownerIs, which notes the sub-proof's own number, turns plOwn alone. -/
theorem ownerIs_shp (tl : HTailF2) (no : Nat) : SameShp tl (tl.ownerIs no) := ⟨rfl, rfl, rfl⟩

/-- borderMeans, which notes which array of an earlier sub-proof is meant, turns plFor alone. -/
theorem borderMeans_shp {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (h : tl.borderMeans iF ownerNo index = .ok tl') : SameShp tl tl' := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      exact ⟨rfl, rfl, rfl⟩

/-- The equation goes along. -/
theorem mS_of_same {a b : HTailF2} (h : SameShp a b)
    (k : ∀ mu, mu < a.NM → (a.shp.getD mu {}).mS = ((a.mats.getD mu {}).m + 2) / 3) :
    ∀ mu, mu < b.NM → (b.shp.getD mu {}).mS = ((b.mats.getD mu {}).m + 2) / 3 := by
  intro mu hmu
  rw [h.shp, h.mats]
  exact k mu (by rw [← h.NM]; exact hmu)

/-- **The shape equation in every plan that planG returns.** -/
theorem planG_mS (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    ∀ mu, mu < hp.tl.NM → (hp.tl.shp.getD mu {}).mS = ((hp.tl.mats.getD mu {}).m + 2) / 3 := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact mS_of_same (ownerIs_shp tl1 g) (addTreesF_mS hA)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact mS_of_same ((ownerIs_shp tl1 g).trans (borderMeans_shp hB)) (addTreesF_mS hA)
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- **At every layers' plan of what publicOf returns.** -/
theorem public_G_mS {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) :
    ∀ mu, mu < hp.tl.NM → (hp.tl.shp.getD mu {}).mS = ((hp.tl.mats.getD mu {}).m + 2) / 3 :=
  planG_mS X.layers g _ hp (public_G h g hp hg)

end OnBytes.Road.K4.Plan

#print axioms OnBytes.Road.K4.Plan.borderMeans_shp
#print axioms OnBytes.Road.K4.Plan.mS_of_same
#print axioms OnBytes.Road.K4.Plan.planG_mS
#print axioms OnBytes.Road.K4.Plan.public_G_mS

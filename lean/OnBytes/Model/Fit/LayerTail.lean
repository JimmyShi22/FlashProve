-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/LayerTail.lean: the smallness test in the plan of every layer sub-proof of a
record that `Verify.publicOf` returns has few columns: the sum of its matrices' columns, times 276,
is at most 2 ^ 45.

The plan of a group of layers (`Layer.planG`, OnBytes/Model/LayerPlan.lean) makes its smallness test
by `HTailF2.shape`; what it does to that value afterwards (the list of arrays, the owner's number,
the border's record) keeps the list of matrices. So the caps that the success of `shapeF` gives
(OnBytes/Model/Fit/ShapeFCaps.lean) hold of the plan's own value.

Main names:
  `foldColumns_congr`: the sum of the columns hangs on the list of matrices alone.
  `planG_shape`: where `Layer.planG` returns hp there is a value tl0 that `shape` has returned, at
    the settings' tau and lidb, with hp.tl.mats = tl0.mats. Under "there is": three lists of which
    no more is said than that `shape` returns at them, and tl0, fixed by its equation.
  `planG_cap`, `plansG_cap`: so hp.tl.foldColumns * 276 ≤ 2 ^ 45, at one plan and at every member
    of what `Layer.plansG` returns.
  `layers_small`: so at every member of X.G, in the form in which the planner is told the number
    (`smallSize`, OnBytes/Model/RoundSizes.lean).
The walk through `planG` uses `Fo.BatRows.bindE_ok` and `addTreesF_keeps`
(OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean), `Fo.Pub.borderMeans_keeps` (FoPublicA.lean) and
`Fo.Pub.plansG_at`, `public_G` (FoPublic.lean).

Limits: the layers alone. One direction: from a routine that returns; that `publicOf` returns at any
files is shown by no term here. Nothing on soundness. The program does not import this file.

-/
import OnBytes.Model.Fit.ShapeFCaps
import OnBytes.Model.RoundSizes
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model

open Fo.BatRows (bindE_ok addTreesF_keeps)

/-- The sum of the columns hangs on the list of matrices alone. -/
theorem foldColumns_congr {tl tl' : HTailF2} (h : tl'.mats = tl.mats) :
    tl'.foldColumns = tl.foldColumns := by
  unfold HTailF2.foldColumns
  rw [h]

/-- **The plan's smallness test has the matrices of a value that `shape` has returned.** -/
theorem planG_shape {P : Layer.Pub} {g : Nat} {O : Option Layer.HPlan2} {hp : Layer.HPlan2}
    (h : Layer.planG P g O = .ok hp) :
    ∃ mats txOf ft tl0,
      ({ tau := P.set.tau, lidb := P.set.lidb } : HTailF2).shape mats txOf ft
        #[false, false, true, false] P.y.h.tau = .ok tl0 ∧ hp.tl.mats = tl0.mats := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have k1 : tl1.mats = tl.mats := (addTreesF_keeps _ _ _ _ _ _ _ _ hA).1
  have k2 : (tl1.ownerIs g).mats = tl.mats := k1
  refine ⟨mats, txOf, ft, tl, hS, ?_⟩
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl : tl1.ownerIs g = y := Except.ok.inj hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact k2
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := Except.ok.inj ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [← hy]
      exact (Fo.Pub.borderMeans_keeps hB).1.trans k2
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- So its columns are few. -/
theorem planG_cap {P : Layer.Pub} {g : Nat} {O : Option Layer.HPlan2} {hp : Layer.HPlan2}
    (h : Layer.planG P g O = .ok hp) : hp.tl.foldColumns * 276 ≤ 2 ^ 45 := by
  obtain ⟨mats, txOf, ft, tl0, hS, e⟩ := planG_shape h
  rw [foldColumns_congr e]
  exact small_cap hS

/-- At every member of the layers' plans. -/
theorem plansG_cap {P : Layer.Pub} {G : Array Layer.HPlan2} (h : Layer.plansG P = .ok G) (g : Nat)
    (hp : Layer.HPlan2) (hg : G[g]? = some hp) : hp.tl.foldColumns * 276 ≤ 2 ^ 45 :=
  planG_cap (Fo.Pub.plansG_at P G h g hp hg)

/-- **At every layer sub-proof of a record that `Verify.publicOf` returns, in the form in which the
planner is told the number.** -/
theorem layers_small {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : (smallSize hp.tl).columns * 276 ≤ 2 ^ 45 :=
  planG_cap (Fo.Pub.public_G h g hp hg)

end OnBytes.Model

#print axioms OnBytes.Model.planG_shape
#print axioms OnBytes.Model.planG_cap
#print axioms OnBytes.Model.plansG_cap
#print axioms OnBytes.Model.layers_small

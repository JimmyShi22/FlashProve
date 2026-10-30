-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/OneRadAtPlaces.lean: the four closed places of the kind K12 at the full
size (PlacesFull.lean) against the four typed lists of sized stages (StagesFull.lean): equal stages,
equal radii, equal work, and one radius for equal numbers.

Sixteen closed statements, each by an evaluation in Lean's kernel. With StageSizesAtScope.lean and
LastAtScope.lean in this folder, which say of which lists, and under what, it is proved that they
are the planner's at every file in the goals' scope, the stages, radii and work of the closed places
are tied to the planner.
Main names, X one of U, O, W, L:
  `oneRad_XFull`: `oneRadB setAt szXFull = true` (CondAtMade.lean): so the look-up `radBy` by a
    stage's nine numbers is well defined on the list. At the planner's return OneRadPlanned.lean has
    it by theorem (of Omega's list where the shape splits); here it is a closed control.
  `stages_XFull`: `piXFull.nums.stages = szXFull.map stageNums`.
  `radii_XFull`: `radiusOf setAt` at each group of szXFull is `rXFull` at that stage's numbers.
  `work_XFull`: `piXFull.nums.work` is the setting's work before a draw of positions, under the
    scope of the place's chain.
Limits: closed facts on typed values: no planner occurs here. OF A PLACE ONLY THREE THINGS ARE HELD:
the stages, the work, and the radii beside it. Its rows, its first and free trees, its index, its
oracle messages, its answers and what stands before it are held against nothing here. Nothing on
soundness. Nothing on hiding.
-/
import Johnson.Desc.K12.Law.CondAtMade
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.K12.Law.Sizes.StagesFull

set_option autoImplicit false

namespace H2K.Sizes
open OnBytes.Params H2K.Member
open H2K.Pub (oneRadB)
open H2U (stageNums)
open Johnson.Top.H (radiusOf)

/-! ### the folded row's test -/

/-- Two stages of the list with the same nine numbers have one radius. -/
theorem oneRad_UFull : oneRadB setAt szUFull = true := by decide +kernel

/-- The closed place's stages are the list's. -/
theorem stages_UFull : piUFull.nums.stages = szUFull.map stageNums := by decide +kernel

/-- The closed radii are the planner's radii at the list's groups. -/
theorem radii_UFull : szUFull.map (fun y => radiusOf setAt y.g) =
    szUFull.map (fun y => rUFull (stageNums y)) := by decide +kernel

/-- The closed place's work is the setting's, before a draw of positions. -/
theorem work_UFull : piUFull.nums.work = setAt.workOf .query .shared := by decide +kernel

/-! ### Omega's test -/

/-- Two stages of the list with the same nine numbers have one radius. -/
theorem oneRad_OFull : oneRadB setAt szOFull = true := by decide +kernel

/-- The closed place's stages are the list's. -/
theorem stages_OFull : piOFull.nums.stages = szOFull.map stageNums := by decide +kernel

/-- The closed radii are the planner's radii at the list's groups. -/
theorem radii_OFull : szOFull.map (fun y => radiusOf setAt y.g) =
    szOFull.map (fun y => rOFull (stageNums y)) := by decide +kernel

/-- The closed place's work is the setting's, before a draw of positions. -/
theorem work_OFull : piOFull.nums.work = setAt.workOf .query .shared := by decide +kernel

/-! ### the request's own test -/

/-- Two stages of the list with the same nine numbers have one radius. -/
theorem oneRad_WFull : oneRadB setAt szWFull = true := by decide +kernel

/-- The closed place's stages are the list's. -/
theorem stages_WFull : piWFull.nums.stages = szWFull.map stageNums := by decide +kernel

/-- The closed radii are the planner's radii at the list's groups. -/
theorem radii_WFull : szWFull.map (fun y => radiusOf setAt y.g) =
    szWFull.map (fun y => rWFull (stageNums y)) := by decide +kernel

/-- The closed place's work is the setting's, before a draw of positions. -/
theorem work_WFull : piWFull.nums.work = setAt.workOf .query .request := by decide +kernel

/-! ### the first chain's last test -/

/-- Two stages of the list with the same nine numbers have one radius. -/
theorem oneRad_LFull : oneRadB setAt szLFull = true := by decide +kernel

/-- The closed place's stages are the list's. -/
theorem stages_LFull : piLFull.nums.stages = szLFull.map stageNums := by decide +kernel

/-- The closed radii are the planner's radii at the list's groups. -/
theorem radii_LFull : szLFull.map (fun y => radiusOf setAt y.g) =
    szLFull.map (fun y => rLFull (stageNums y)) := by decide +kernel

/-- The closed place's work is the setting's, before a draw of positions. -/
theorem work_LFull : piLFull.nums.work = setAt.workOf .query .request := by decide +kernel

end H2K.Sizes

#print axioms H2K.Sizes.oneRad_UFull
#print axioms H2K.Sizes.stages_UFull
#print axioms H2K.Sizes.radii_UFull
#print axioms H2K.Sizes.work_UFull
#print axioms H2K.Sizes.oneRad_OFull
#print axioms H2K.Sizes.stages_OFull
#print axioms H2K.Sizes.radii_OFull
#print axioms H2K.Sizes.work_OFull
#print axioms H2K.Sizes.oneRad_WFull
#print axioms H2K.Sizes.stages_WFull
#print axioms H2K.Sizes.radii_WFull
#print axioms H2K.Sizes.work_WFull
#print axioms H2K.Sizes.oneRad_LFull
#print axioms H2K.Sizes.stages_LFull
#print axioms H2K.Sizes.radii_LFull
#print axioms H2K.Sizes.work_LFull

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/HalvesNums.lean: CONDITIONAL.

Not shown here. THAT A WORD OF THE HONEST PARTS READS AS THE LIBRARY's TERM. Where K4Plan holds: the
head of Johnson/Road/K4/W/GroundOfHear.lean. By a walk of import lines the closure holds seven
modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), through
Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none
of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The eight public numbers `HalvesNums` (Law/W/Halves.lean) from the nine public facts on the plan
(`K4Plan`, Johnson/Road/K4/W/GroundOfHear.lean) and two equations on what was heard, which
`ground_of_hear` gives where a hearing returns.

  `halvesNums_of_plan`   HalvesNums Q o D.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.Halves
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.K4.PlanSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.Road.K4 (laySizes_of_layout nNu_tie)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)

/-- **The eight numbers, from the plan's public facts.** CONDITIONAL: on A, hy and hg. -/
theorem halvesNums_of_plan {Q : K4Pub} {o : Own} {hS : OnBytes.Model.Layer.Shape}
    {pc : List (List String)} {tl : HTailF2} {D : Dim} (A : K4Plan hS pc Q.P Q.g tl D)
    (hy : o.v.y = Q.P.y) (hg : o.v.g = Q.g) : HalvesNums Q o D := by
  have L := laySizes_of_layout A.lay
  have xl : Q.P.y.h.xl = 5 := by
    rw [L.shape]
    exact A.sw.xl
  have p3 : Q.P.y.h.p3 = true := by
    rw [L.shape]
    exact A.sw.p3
  exact
    { y := hy
      g := hg
      NI := by rw [L.NI, nNu_tie A.sized]
      NS := by
        rw [xl]
        rfl
      NP := by
        rw [xl]
        rfl
      NO := by
        rw [xl]
        rfl
      ends := by
        unfold nEndT
        rw [p3, if_pos rfl]
        exact Nat.le_of_eq (by ring)
      stack := by
        unfold nStack
        omega }

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.halvesNums_of_plan

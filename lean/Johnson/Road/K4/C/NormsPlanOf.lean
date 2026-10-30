-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/NormsPlanOf.lean: CONDITIONAL.

Not shown here. WHERE K4Plan HOLDS: the head of Johnson/Road/K4/W/GroundOfHear.lean; its field sw
bars every shape but those with the library's eleven switches; beside a small synthetic plan, given
one evaluated fact, no example is known. Nothing on soundness, on completeness or on any other
property. No property is claimed.

The seven public facts `NormsPlan` (C/NormsTabs.lean) from the plan's nine public facts (`K4Plan`,
Johnson/Road/K4/W/GroundOfHear.lean): five numbers by the library's laws on a layout that `layout`
returns and on what `readsOf` returns; the matrices' sizes by `matsLaid_of_tails` (C/MatsLaid.lean);
that the features of the streams' limbs lie inside their matrices by `streamsIn_of_plan`
(C/StreamsOf.lean).

  `normsPlan_of_plan`   NormsPlan Q D from K4Plan.
-/
import Johnson.Road.K4.C.Norms
import Johnson.Road.K4.C.MatsLaid
import Johnson.Road.K4.C.StreamsOf
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.K4.PlanClauses

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Road.K4.W (K4Plan)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4.Honest (K4Pub)

/-- **NormsPlan from the plan's public facts.** CONDITIONAL: on A. -/
theorem normsPlan_of_plan {Q : K4Pub} {hS : Layer.Shape} {pc : List (List String)} {tl : HTailF2}
    {D : Dim} (A : K4Plan hS pc Q.P Q.g tl D) : NormsPlan Q D := by
  obtain ⟨m1, _, _⟩ := Fo.readsOf_mu A.reads
  have L := laySizes_of_layout A.lay
  have L2 := laid2_of_layout A.lay
  have Mr := layMore_of_layout A.lay
  have Z := A.sized
  have hls : Q.P.y.ls ≤ Q.P.y.lPd := (norms_sizes A.lay A.sized).2.2.2.1
  have elt : Q.P.y.h.lt = D.lT := by rw [L.shape, Z.lT]
  exact
    { T := by rw [L2.T, elt]
      NI := by rw [L.NI, nNu_tie Z]
      Pd := Mr.Pd
      lsPd := hls
      muV := by
        rw [m1, elt]
        omega
      mats := matsLaid_of_tails Q A.tails A.grp
      streams := streamsIn_of_plan A }

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.normsPlan_of_plan

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K8EndsJoinLay.lean: THE SMALLNESS TEST's NAMED TEST ON SIZES AT EVERY BUILT SEGMENT
(ProofFile.smallSizesOwnB): THE JOIN OF THE LAWS ON "THE TABLES' END": THE TWELVE FEED-FORWARD SEGMENTS'
LAW IS IN. Two theorems. Beside Johnson/P5J/K8EndsJoin.lean, which holds still.
TWELVE OF THE 25 PLACES ARE OPEN: ownSizes_of_att TAKES THE LAW AT THE TWELVE ATTENTION SEGMENTS
(HA) AS A PREMISE: another kind's law.
AND hW : planFitsAllB Zp.p.X = true (the frozen condition's own second conjunct) stays in front.
(Where this and lean/THEOREM.md differ, the page
holds.)
  colsAt_lay         K8N.ColsAt Zp (2 * g), g < 12: u3_cols_lay
                     (Johnson/Road/K4/Plan/U3ColsLay.lean), whose end spells the fold out: one term
                     with tabsEnd.
  **ownSizes_of_att h hW HA**: ownSizes_of_cols (K8EndsJoin.lean) at it.
Can the premises be met together? Evaluated at the goals' named full-size set, in
a file not named here: hW: true; ColsAt's inequality is an equality at all 25. Not proved.
Limits. The head is a premise: over the entry tests' second and third lists. At OnBytes.secondHashFunction.
The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K8EndsJoin
import Johnson.Road.K4.Plan.U3ColsLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First.K8.Ready (planFitsAllB)
open K8N

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The law at the twelve feed-forward segments: another file's (`u3_cols_lay`). -/
theorem colsAt_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : ∀ g < 12, ColsAt Zp (2 * g) :=
  fun _ hg _ _ hG e3 =>
    OnBytes.Road.K4.Plan.u3_cols_lay h.toAtMg.scope h.toAtMg.reads h.toAtMg.laid.pub hG hg e3

/-- **THE NAMED TEST ON SIZES AT EVERY BUILT SEGMENT, FROM THE HEAD, planFitsAllB AND THE LAW ON THE
TABLES' END AT THE TWELVE ATTENTION SEGMENTS.** -/
theorem ownSizes_of_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hW : planFitsAllB Zp.p.X = true) (HA : ∀ g < 12, ColsAt Zp (2 * g + 1)) :
    ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true :=
  ownSizes_of_cols h hW (colsAt_lay h) HA

end P5J

#print axioms P5J.colsAt_lay
#print axioms P5J.ownSizes_of_att
#print axioms OnBytes.Road.K4.Plan.u3_cols_lay

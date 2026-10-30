-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K8OwnSizesHead.lean: THE SMALLNESS TEST's NAMED TEST ON SIZES AT EVERY BUILT SEGMENT
(ProofFile.smallSizesOwnB: the fourth conjunct of the kind's frozen condition) FROM THE HEAD AND ONE LAW.
One theorem.
ONE PREMISE STAYS BESIDE THE HEAD: HA: the law on the tables' end at the TWELVE ATTENTION SEGMENTS
(K8N.ColsAt Zp (2 * g + 1), Johnson/P5J/K8EndsJoin.lean): another kind's: taken as a premise.
(Where this and
lean/THEOREM.md differ, the page holds.)
  ownSizes_of_att_law h HA := ownSizes_of_att (Johnson/P5J/K8EndsJoinLay.lean) at
    AtMgA.k8_planFits (Johnson/Goal/Skeleton/Kinds/K8Rest.lean: planFitsAllB Zp.p.X = true from the
    head alone; beneath it planFitsAllB_of_public: at whatever publicOf returns).
Can the premise be met? Evaluated at the goals' named full-size set, in a file of
evaluations that is not named here: ColsAt's inequality is an equality at all 25. Not proved.
Limits. The head is a premise: over the entry tests' asksAt2 and asksAt3. At OnBytes.secondHashFunction.
The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K8EndsJoinLay
import Johnson.Goal.Skeleton.Kinds.K8Rest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open K8N

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE NAMED TEST ON SIZES AT EVERY BUILT SEGMENT, FROM THE HEAD AND THE LAW ON THE TABLES' END
AT THE TWELVE ATTENTION SEGMENTS.** -/
theorem ownSizes_of_att_law (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (HA : ∀ g < 12, ColsAt Zp (2 * g + 1)) :
    ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true :=
  ownSizes_of_att h h.k8_planFits HA

end P5J

#print axioms P5J.ownSizes_of_att_law
#print axioms P5J.AtMgA.k8_planFits

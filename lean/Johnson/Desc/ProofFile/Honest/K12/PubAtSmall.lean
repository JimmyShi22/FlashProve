-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PubAtSmall.lean: `pubBehind` (PubAtDoor.lean) and `nearOf`
(PubNear.lean) at the small made-up chain of SharedSmall.lean (`P3`), held against the two public
parts that FitSharedAt.lean writes out by hand (`pubU`, `pubO`).

  `sentU3`, `withU_P3`, `splits_P3`, `ahead_P3` what goes out with o_u at `P3`; the two public
                   premises of PubAtDoor.lean hold at `P3`
  `pubBehind_P3`   `(pubBehind P3 sentU3, 0) = pubU`: the term made from the plan is the written one
  `near_pubO` `nearOf pubO.1 1 = nearOf (pubBehind P3 sentU3) 1`: of the written public part at the
                   test on G_omega, the part that `layFits` reads is the one made from the plan
  `layFitsNear_U`, `layFitsNear_Omega`   `layFitsNear` is true at these two parts, at the jobs'
                   parameters and shapes

By what. Each is evaluated by Lean's kernel (`decide +kernel`). The guards at the end are evaluated
by the compiler.

Limits. One small made-up plan. `pubO` as a whole is not `pubBehind`: it holds the two groups and
four messages more that the test on G_u has made (two guards say so). Two facts are not joined at
one job here: that what `layFits` reads of the state on entry is one public term, and that
`layFitsNear` is true at that term. `layFitsNear_U` and `layFitsNear_Omega` stand at `pubJob`
(FitSharedAt.lean), whose own state on entry is `noState`, and no lemma here carries them to
`jobAtU` or `jobAtOmega`; `nearDoor_U` and `nearDoor_Omega` are not stated at `P3` here, and
`doorOf` is not evaluated here. PubAtSmallDoor.lean has all of these: the two facts at one job
(`layFits_small_doorU`, `layFits_small_doorOmega`), the premise on the block of the test on G_u by
the kernel (`planOk_p`), and tests that evaluate `doorOf`. Nothing on completeness, soundness or
hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.PubNear
import Johnson.Desc.ProofFile.Honest.K12.FitSharedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SharedSmall
open OnBytes (OracleNotice)
open Desc.K14 (withU)

/-- What goes out with o_u at `P3`. -/
def sentU3 : Array OracleNotice := (withU P3.S).getD #[]

theorem withU_P3 : withU P3.S = some sentU3 := by decide +kernel

theorem splits_P3 : P3.S.sharedSplitNeeded = true := by decide +kernel

theorem ahead_P3 : P3.S.masksAhead = true := by decide +kernel

/-- **The term made from the plan is the public part that is written out by hand.** -/
theorem pubBehind_P3 : (pubBehind P3 sentU3, 0) = pubU := by decide +kernel

/-- Of the written public part at the test on G_omega, the part that `layFits` reads is the one made
from the plan. -/
theorem near_pubO : nearOf pubO.1 1 = nearOf (pubBehind P3 sentU3) 1 := by decide +kernel

theorem layFitsNear_U :
    layFitsNear (pubJob p (shapesAtU ⟨P3, 0⟩ p)) (nearOf (pubBehind P3 sentU3) 0) = true := by
  decide +kernel

theorem layFitsNear_Omega :
    layFitsNear (pubJob pO (shapesAtOmega ⟨P3, 0⟩ pO)) (nearOf (pubBehind P3 sentU3) 1) = true := by
  decide +kernel

-- the whole written public part at the test on G_omega is another than the plan's term: it has two
-- groups and four messages more
#guard pubO.1 != pubBehind P3 sentU3
#guard pubO.1.groups.size == (pubBehind P3 sentU3).groups.size + 2 &&
  pubO.1.shapes.size == (pubBehind P3 sentU3).shapes.size + 4
-- each check is false at the other group
#guard !layFitsNear (pubJob p (shapesAtU ⟨P3, 0⟩ p)) (nearOf (pubBehind P3 sentU3) 1) &&
  !layFitsNear (pubJob pO (shapesAtOmega ⟨P3, 0⟩ pO)) (nearOf (pubBehind P3 sentU3) 0)
-- at a group that is not there the check is false
#guard !layFitsNear (pubJob p (shapesAtU ⟨P3, 0⟩ p)) (nearOf (pubBehind P3 sentU3) 2)
-- with one more mask row in o_sp's shape the check is false
#guard !layFitsNear (pubJob p (shapesAtU ⟨P3, 0⟩ p))
  (nearOf { pubU.1 with shapes := pubU.1.shapes.modify 3 fun s => { s with maskRows := 2 } } 0)
-- layFitsNear at pubNear is layFits, at JobSharedToy.lean's state on entry to the test on G_u
#guard layFitsNear (ProofFile.Honest.K12.Light.SharedToy.job {})
    (pubNear ProofFile.Honest.K12.Light.SharedToy.door) ==
  (ProofFile.Honest.K12.Light.SharedToy.job {}).layFits ProofFile.Honest.K12.Light.SharedToy.door
-- at its state on entry to the test on G_omega, pubNear is the term made from the plan
#guard pubNear ProofFile.Honest.K12.Light.SharedToy.doorO == nearOf (pubBehind P3 sentU3) 1

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.SharedSmall.withU_P3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.splits_P3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.ahead_P3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.pubBehind_P3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.near_pubO
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFitsNear_U
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFitsNear_Omega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.sentU3

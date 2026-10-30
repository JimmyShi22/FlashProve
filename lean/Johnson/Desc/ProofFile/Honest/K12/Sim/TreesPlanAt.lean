-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesPlanAt.lean: a test: the plan's half `planB` (PlanB.lean)
at the number of trees that the first switch opens, at the library's closed places of a proximity
test whose first reading round opens several trees. Nine closed facts on public numbers, by the
kernel's own evaluation. No property is claimed.

  `planB_U_full`, `planB_U_small`, `planB_KU_full`   "true" at two trees: the tests on the folded
                 row's group: the proof file's at both sizes, the key file's at the full size
  `planB_W_full`, `planB_W_small`, `planB_KW_full`   "true" at three trees: the request's own tests
  `planNo_O_full`, `planNo_O_small`, `planNo_KO_full`   at Omega's tests, whose first fold sends its
                 own table, just two clauses fail: that on the first fold's declared rounds, and
                 that on the later stages

What it is for. With `reachT_U_full` and its like (Sim/TreesReach.lean) it shows that the two
clauses `reach` and `plan` of `PubTiesT` (Sim/TreesExact.lean) can be met at these six places.

Limits. Those of Sim/ReachAt.lean: a "true" counts nothing by itself: the other clauses of
`PubTiesT`, and the condition `OnFreeT`, are not touched; no converse is proved for a "false". The
places and the tables of codes are closed terms that a program made off the print of a run: that
they are the places of a file is no theorem. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ReachAt
import Johnson.Desc.ProofFile.Honest.K12.PlanB

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12
open H2K.Member

/-! ## Where the first reading round opens two trees -/

theorem planB_U_full : planB piUFull codesFull 2 = true := by decide +kernel
theorem planB_U_small : planB piU codesSmall 2 = true := by decide +kernel
theorem planB_KU_full : planB piKUFull codesKeyFull 2 = true := by decide +kernel

/-! ## Where it opens three -/

theorem planB_W_full : planB piWFull codesFull 3 = true := by decide +kernel
theorem planB_W_small : planB piW codesSmall 3 = true := by decide +kernel
theorem planB_KW_full : planB piKWFull codesKeyFull 3 = true := by decide +kernel

/-! ## Where the first fold sends its own table: the names of just the clauses that fail -/

theorem planNo_O_full : planNo piOFull codesFull 3 = ["foldCut", "planFromOk"] := by decide +kernel
theorem planNo_O_small : planNo piO codesSmall 3 = ["foldCut", "planFromOk"] := by decide +kernel
theorem planNo_KO_full : planNo piKOFull codesKeyFull 3 = ["foldCut", "planFromOk"] := by
  decide +kernel

-- the number of trees is read: at another number one clause fails
#guard planNo piUFull codesFull 1 == ["oS"] && planNo piWFull codesFull 2 == ["oS"]
-- all twenty-two clauses are there
#guard (planL piUFull codesFull 2).length == 22 && (planL piWFull codesFull 3).length == 22

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.planB_U_full
#print axioms ProofFile.Honest.K12.planB_U_small
#print axioms ProofFile.Honest.K12.planB_KU_full
#print axioms ProofFile.Honest.K12.planB_W_full
#print axioms ProofFile.Honest.K12.planB_W_small
#print axioms ProofFile.Honest.K12.planB_KW_full
#print axioms ProofFile.Honest.K12.planNo_O_full
#print axioms ProofFile.Honest.K12.planNo_O_small
#print axioms ProofFile.Honest.K12.planNo_KO_full

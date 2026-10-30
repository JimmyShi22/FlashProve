-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OLines.lean: closed lines on the test on G_omega of the key file, by the
kernel's own evaluation.

  `openRowsAndMembers`   of a group of a shape: the number of open rows and the members
  `group_under_test`     at the door's one shape the group under test has one open row, and the members 2 and 3
  `groups_at_door`       all the groups of that shape
  `test_core_returns`    the test on G_u returns at the plan's shape, so that shape is not the fall-back's alone
  `form_at_key`, `own_mask_at_key`, `cut_at_key`   the place's public numbers

Limits. Public numbers and shapes alone. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyTenLinesKernel
import E2E.KeyTenPubKernel
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc.Ground.Sh (GrpSh)
open H2K.Member (piKOFull piKUFull)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (shapeOm sentK)
open AtPublicFiles.AtFiles.Full (QK)

/-- The number of open rows and the members of a group of a shape. -/
def openRowsAndMembers (G : GrpSh) : ℕ × List ℕ := (G.kinds.length, G.members)

/-- **At the door's one shape the group under test has one open row, and the members 2 and 3.** -/
theorem group_under_test :
    (shapeOm.core.st.groups[shapeOm.g]?).map openRowsAndMembers = some (1, [2, 3]) := by
  decide +kernel

/-- Control: group 0 is another. -/
theorem group_zero_is_other :
    (shapeOm.core.st.groups[0]?).map openRowsAndMembers ≠ some (1, [2, 3]) := by
  decide +kernel

/-- All the groups of the door's shape: group 0 of the test on G_u, and those that the test leaves. -/
theorem groups_at_door : shapeOm.core.st.groups.map openRowsAndMembers =
    [(0, [0, 3]), (1, [2, 3]), (0, [4]), (0, [6]), (0, [8]), (0, [10])] := by
  decide +kernel

/-- The test on G_u returns at the shape in front of it. -/
theorem test_core_returns :
    (ProofFile.Honest.Sh.testCore piKUFull (ProofFile.Honest.K12.Light.endOf QK sentK).core
      (ProofFile.Honest.K12.Light.endOf QK sentK).lin.gU
      (ProofFile.Honest.K12.Light.endOf QK sentK).lin.firstMask).isSome = true := by
  decide +kernel

theorem form_at_key : formPubB piKOFull = true := by decide +kernel

/-- Control: a place with no stages fails. -/
theorem form_not_without_stages :
    formPubB { piKOFull with nums := { piKOFull.nums with stages := [] } } = false := by
  decide +kernel

theorem own_mask_at_key : piKOFull.nums.ownMask = true := by decide +kernel

/-- Control: the place of the test on G_u sends no table of its own. -/
theorem own_mask_not_at_U : piKUFull.nums.ownMask = false := by decide +kernel

theorem cut_at_key :
    Johnson.Prover.Link.batCut (((H2K.JointK.laidOf piKOFull).take 1).map (·.1)) = true := by
  decide +kernel

/-- Control: a cut behind the second round is no cut. -/
theorem cut_not_at_two :
    Johnson.Prover.Link.batCut (((H2K.JointK.laidOf piKOFull).take 2).map (·.1)) = false := by
  decide +kernel

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.group_under_test
#print axioms ProofFile.Honest.K12.AtKey.group_zero_is_other
#print axioms ProofFile.Honest.K12.AtKey.groups_at_door
#print axioms ProofFile.Honest.K12.AtKey.test_core_returns
#print axioms ProofFile.Honest.K12.AtKey.form_at_key
#print axioms ProofFile.Honest.K12.AtKey.form_not_without_stages
#print axioms ProofFile.Honest.K12.AtKey.own_mask_at_key
#print axioms ProofFile.Honest.K12.AtKey.own_mask_not_at_U
#print axioms ProofFile.Honest.K12.AtKey.cut_at_key
#print axioms ProofFile.Honest.K12.AtKey.cut_not_at_two

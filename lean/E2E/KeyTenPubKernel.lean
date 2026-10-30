-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyTenPubKernel.lean

`frontPubOwnB` at the key's test on G_omega BY THE KERNEL's OWN EVALUATION, with a control.

Limits. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyTenPubGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyDoorUClosed
open H2K.Member (piKOFull)
open ProofFile.Honest.K12.Own (frontPubOwnB frontOwnFiveB)
open AtPublicFiles.AtFiles.Full (QK)

theorem pub_O : frontPubOwnB piKOFull (ProofFile.Honest.Sh.thinOf shapeOm) = true := by decide +kernel

theorem pub_O_g : frontPubOwnB piKOFull (ProofFile.Honest.Sh.thinOf { shapeOm with g := 99 }) = false := by
  decide +kernel

theorem five_O : frontOwnFiveB piKOFull QK.codes shapeOm = true := by decide +kernel

theorem five_O_mask : frontOwnFiveB piKOFull QK.codes { shapeOm with mask := some 0 } = false := by
  decide +kernel

theorem five_O_g : frontOwnFiveB piKOFull QK.codes { shapeOm with g := 99 } = false := by
  decide +kernel

theorem five_O_U : frontOwnFiveB piKOFull QK.codes shapeU = false := by decide +kernel

end ProofFile.Honest.K12.Light.KeyDoorUClosed

#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.pub_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.pub_O_g
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.five_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.five_O_mask
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.five_O_g
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.five_O_U

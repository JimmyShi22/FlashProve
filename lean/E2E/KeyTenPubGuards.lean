-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyTenPubGuards.lean

`frontPubOwnB` at the key's test on G_omega, by Lean's evaluator, with a control. If it says no, the clause pub of
`FrontAsksO` cannot be had through this test at jobKO. KeyTenPubKernel.lean imports this file.

Limits. An evaluation outside the kernel. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyTenLinesGuards
import Johnson.Desc.ProofFile.Honest.K12.Own.FrontOwnFive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyDoorUClosed
open H2K.Member (piKOFull)
open ProofFile.Honest.K12.Own (frontPubOwnB frontOwnFiveB)
open AtPublicFiles.AtFiles.Full (QK)

#eval frontPubOwnB piKOFull (ProofFile.Honest.Sh.thinOf shapeOm)

-- Foretold: yes. Control: a group that is not there: no.
#guard frontPubOwnB piKOFull (ProofFile.Honest.Sh.thinOf shapeOm)
#guard !frontPubOwnB piKOFull (ProofFile.Honest.Sh.thinOf { shapeOm with g := 99 })

#eval frontOwnFiveB piKOFull QK.codes shapeOm

-- All the shape's clauses in one. Foretold: yes. Controls: a mask named; another group; U's shape: no.
#guard frontOwnFiveB piKOFull QK.codes shapeOm
#guard !frontOwnFiveB piKOFull QK.codes { shapeOm with mask := some 0 }
#guard !frontOwnFiveB piKOFull QK.codes { shapeOm with g := 99 }
#guard !frontOwnFiveB piKOFull QK.codes shapeU

end ProofFile.Honest.K12.Light.KeyDoorUClosed

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CLenB.lean: «proof 0» has 48,293 written rounds, said without List.length (which
nests a level an element for the kernel): nothing is left behind place 48,293, and something behind
place 48,292. A CLOSED FACT FOR LEAN's KERNEL («decide +kernel»: by evaluation in Lean's kernel
alone; no compiled code of this library is trusted), alone in its file. A law file; no running text
imports it. Made by program from one template. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.AtW
import Johnson.AtFull.Rows.StepC

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem drops_p0 :
    (((prW 0).rounds.drop (48292 + 1)).isEmpty && !((prW 0).rounds.drop 48292).isEmpty) = true := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.drops_p0

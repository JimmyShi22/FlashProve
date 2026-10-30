-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CLenA.lean: the lengths: three plans of the key, three of the proof, 27 pieces
of «proof 0». A CLOSED FACT FOR LEAN's KERNEL («decide +kernel»: by evaluation in Lean's kernel
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

theorem lens_W :
    (cW.key.length == 3 && cW.proof.length == 3 && piecesW.length == 27) = true := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.lens_W

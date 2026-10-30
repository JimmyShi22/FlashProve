-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CCtlE.lean: CONTROLS; nothing uses them: ON THE TEST «THE LIGHT TWIN ENDS AT
COUNTERS 0» (CT0L.lean):
  (1) `twinL_key0_open`: endOf CAN SAY OTHERWISE: «key 0»'s light twin with one call behind it that
      writes a scalar and closes nothing ends at 24 open bytes;
  (2) `twinL_key0_notes`: the twin notes a call: so its chain in the tail is no empty one.
A BEND THAT DOES NOT BITE, SAID HERE SO THAT NOBODY TRIES IT AGAIN; NOT SHOWN HERE, by no theorem
and no print: begun with one open byte (or root, or answer) the twin ends at counters 0 all the
same (by the evaluator; and the kernel refused «… = false»): its first closed round takes in what
stood open: «ends at counters 0» does not hang on the counters at the start.
Two closed facts for Lean's kernel (`decide +kernel`: by evaluation in Lean's kernel alone; no
compiled code of this library is trusted), light ones, in one file. A law file; no running text
imports it. Made by program from one template.
Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.AtW
import Johnson.AtFull.Rows.Twin

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem twinL_key0_open :
    endOf sW ⟨.once, 0, 0, 0⟩ (do key0L cW; note (.scalars 1)) = some ⟨.once, 24, 0, 0⟩ := by
  decide +kernel
theorem twinL_key0_notes : 0 < (callsAt sW ⟨.once, 0, 0, 0⟩ (key0L cW)).size := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.twinL_key0_open
#print axioms VerifiableInference.Desc.LinkJoin.twinL_key0_notes

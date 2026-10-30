-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Written/FullOk.lean: an evaluation in the kernel, cut off so that no
file is heavy: see RoundsWritten.lean's head.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Written.Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes.Params (Rounds)
open Johnson.G (dryProofFull dryProofSmall)
open Johnson.G

set_option maxRecDepth 1000000 in
theorem full_closeRuns : (dryProofRunsFull0.all fun x =>
    ((dryProofRecsFull.map closeRoundOk)[x.2]?).getD true) = true := by
  decide +kernel

/-- **EVERY ROUND OF THE FIRST CHAIN's WRITTEN LIST PASSES IT**, at the full size. -/
theorem full_closeRounds : dryProofFull.1.all closeRoundOk = true :=
  all_unrunR closeRoundOk dryProofRecsFull dryProofRunsFull0 full_closeRuns

end VerifiableInference.Desc.First.Close

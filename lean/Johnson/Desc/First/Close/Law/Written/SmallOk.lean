-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Written/SmallOk.lean: an evaluation in the kernel, cut off so that no
file is heavy: see RoundsWritten.lean's head.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Written.Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes.Params (Rounds)
open Johnson.G (dryProofFull dryProofSmall)

set_option maxRecDepth 1000000 in
theorem small_closeRounds : dryProofSmall.1.all closeRoundOk = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem small_members :
    (Fmt.M2.rBatN 6, []) ∈ dryProofSmall.1 ∧ (Fmt.M1.rEps "FOLD epsilon", []) ∈ dryProofSmall.1 ∧
      (Fmt.M1.rTwo "FOLD round", []) ∈ dryProofSmall.1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem small_control : dryProofSmall.2.1.all closeRoundOk = false := by
  decide +kernel

end VerifiableInference.Desc.First.Close

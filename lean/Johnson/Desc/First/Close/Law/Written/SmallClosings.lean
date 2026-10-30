-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Written/SmallClosings.lean: an evaluation in the kernel, cut off so
that no file is heavy: see RoundsWritten.lean's head.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Written.Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes.Params (Rounds)
open Johnson.G (dryProofFull dryProofSmall)

set_option maxRecDepth 1000000 in
theorem small_closings : closingsOf dryProofSmall.1 =
    [(6, some 9), (1536, some 7), (882, some 9), (1536, some 7), (880, some 8),
      (656, some 1)] := by
  decide +kernel

end VerifiableInference.Desc.First.Close

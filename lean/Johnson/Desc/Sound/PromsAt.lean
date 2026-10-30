-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Small lemmas on the shared chain's table's promise
-- and first row, by evaluation.
import Johnson.Desc.Sound.BordersSharedQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

theorem promsAt_zero' (split : Bool) : promsAt split 0 = [.tablePromise, .shape 0] := by
  cases split <;> rfl

end VerifiableInference.Desc.Sound

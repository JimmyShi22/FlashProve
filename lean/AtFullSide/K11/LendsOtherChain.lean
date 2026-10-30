-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsOtherChain.lean: A control: on chain 1 the row is not lent.
-/
import AtFullSide.K11.LendsCut.Controls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open ProofFile.Honest
open ProofFile.Honest.K11 (k11Lends)

/-- A control: on chain 1 the row is not lent. -/
theorem k11LendsW_other_chain : k11Lends k11BookW 1 IM.k11Place (k11ParW 18) = false :=
  (k11Lends_is_small_at _ _).trans k11LendsS_other

end AtFullSide.K11

#print axioms AtFullSide.K11.k11LendsW_other_chain

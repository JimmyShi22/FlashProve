-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsElsewhere.lean: A control: at the piece in front the row is not lent.
-/
import AtFullSide.K11.LendsCut.Controls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open ProofFile.Honest
open ProofFile.Honest.K11 (k11Lends)

/-- A control: at the piece in front the row is not lent. -/
theorem k11LendsW_elsewhere : k11Lends k11BookW 0 ⟨1, some 24, 8, .K11⟩ (k11ParW 18) = false :=
  (k11Lends_is_empty_at8 _).trans k11LendsE_elsewhere

end AtFullSide.K11

#print axioms AtFullSide.K11.k11LendsW_elsewhere

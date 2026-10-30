-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsShort.lean: a control: with one column bit fewer the row is not lent: by the test over the
kind's two entries, at the written book's entries at the kind's place (LendsCut/Join.lean).
-/
import AtFullSide.K11.LendsCut.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open ProofFile.Honest.K11 (k11Lends)

/-- A control: with one column bit fewer the row is not lent. -/
theorem k11LendsW_short : k11Lends k11BookW 0 IM.k11Place (k11ParW 17) = false :=
  (k11Lends_is_small _).trans k11LendsS_short

end AtFullSide.K11

#print axioms AtFullSide.K11.k11LendsW_short

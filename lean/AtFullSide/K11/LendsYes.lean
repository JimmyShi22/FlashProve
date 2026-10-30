-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsYes.lean: at the written book the merge's row is lent: by the test over the kind's two
entries, at the written book's entries at the kind's place (LendsCut/Join.lean).
-/
import AtFullSide.K11.LendsCut.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open ProofFile.Honest.K11 (k11Lends)

/-- **At the written book the merge's row is lent.** -/
theorem k11LendsW : k11Lends k11BookW 0 IM.k11Place (k11ParW 18) = true :=
  (k11Lends_is_small _).trans k11LendsS

end AtFullSide.K11

#print axioms AtFullSide.K11.k11LendsW

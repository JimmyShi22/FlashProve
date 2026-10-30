-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Bridge/CodeListRSFProved.lean: `Cb.BCHKS46F F`, the statement on codes in its form over a base
field (Cb/Gen/CodeListRSF.lean), proved for every field F.

One theorem with its proof: one application of `Cb.bchks46F_of_wide` (Cb/Gen/CodeListRSF.lean) at
`Cb.Bridge.bchks46` (Cb/Bridge/CodeListRSProved.lean), which rests on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15). The line is that of the writers of
Cb/Bridge/CodeListRSProved.lean.
With it all three forms of the statement, `Cb.BCHKS46`, `Cb.BCHKS46F` and `Cb.BCHKS46At`, are
theorems of this library.
Limits: the statement is that of `Cb.BCHKS46F`, to be read there. The paper's own form of the bound
is not proved here.

-/
import Cb.Gen.CodeListRSF
import Cb.Bridge.CodeListRSProved

set_option autoImplicit false

namespace Cb.Bridge

/-- **`BCHKS46F F`, proved, for every field F.** -/
theorem bchks46F (F : Type) [Field F] : BCHKS46F F := bchks46F_of_wide F bchks46

end Cb.Bridge

#print axioms Cb.Bridge.bchks46F

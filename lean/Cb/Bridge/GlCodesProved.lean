-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Bridge/GlCodesProved.lean: `Cb.BCHKS46At Cb.Gl.F Cb.Gl.E`, proved: the statement on agreement of
Reed-Solomon codes below the Johnson radius, over the cubic extension E of the field F with
p = 2^64 - 2^32 + 1 elements, points in F. It is the case F := `Cb.Gl.F`, E := `Cb.Gl.E` of
`Cb.Bridge.bchks46At` (Cb/Bridge/CodeListRSProved.lean), which rests on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).

-/
import Cb.Bridge.CodeListRSProved
import Cb.Gl.GlField

set_option autoImplicit false

namespace Cb.Gl

/-- The statement on codes at this library's two fields. -/
theorem bchks46At : Cb.BCHKS46At Cb.Gl.F Cb.Gl.E := Cb.Bridge.bchks46At Cb.Gl.F Cb.Gl.E

end Cb.Gl

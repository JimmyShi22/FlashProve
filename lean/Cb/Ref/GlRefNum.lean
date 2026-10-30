-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-





Cb/Ref/GlRefNum.lean: the number of elements of the challenge field (`q`), Goldilocks' cubic
extension.




Arithmetic only: no protocol, no code, no model occurs here; nothing is said of a whole protocol.



q = p^3, p = 2^64 - 2^32 + 1; 191.99 < log2 q < 192.























































Limits: this file gives no bound for a protocol.


















Terms: lean/GLOSSARY.md.



-/
import Cb.Gl.GlField
import Cb.Ld.LdRng
import Mathlib.Data.ENNReal.Inv

set_option autoImplicit false

namespace Cb.Gl.Ref
open scoped ENNReal

/-- the number of elements of the challenge field -/
abbrev q : ℕ := Gl.p ^ 3

/-! ### The rounds that draw locations -/

/-! ### The whole second round of a code switch -/

/-! ### The link's one round for both lists of locations -/

/-! ### All other kinds: no proof of work -/

end Cb.Gl.Ref

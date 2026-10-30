-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Exp/Def.lean: the table of exponentials' words by the library's stored words, for
its digest. `expW ι`: the entries of `OnBytes.Road.L5.refL` (Johnson/Road/Lane5AttExp.lean).
A definition alone.

-/
import Johnson.Unfolds.SecondHashFunctionChain
import Inst.Model.TablesRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Exp

/-- Entry ι of the table of exponentials (S = 12, rx = 8) by the library's stored words. -/
def expW (ι : Nat) : Nat := (Inst.Model.refExp (ι : Int)).toNat

end Johnson.Unfolds.Exp

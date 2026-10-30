-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/Def.lean: table SILU's words by the library's stored words, for the pieces of
its digest. `siluW t`: the right side of `Meaning.Gate.silu_word` (Johnson/Meaning/GateRows.lean) as
a natural number. `t1S`: the counter's high word in every call of the compression function for a
list of 65,536 words under the number 72 (`tableHashNumber`, OnBytes/Model/Config.lean).
Definitions alone.

-/
import Johnson.Unfolds.SecondHashFunctionChain
import Inst.Model.TablesRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Silu

/-- Entry t of table SILU by the library's stored words. -/
def siluW (t : Nat) : Nat := (Inst.Model.refSILU (t : Int) + 4096).toNat

/-- `secondHashFunctionState`'s t1 at the number 72 and 65,536 words. -/
def t1S : UInt64 := UInt64.ofNat (72 + 4294967296 * 65536)

end Johnson.Unfolds.Silu

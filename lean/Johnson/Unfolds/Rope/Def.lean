-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/Def.lean: the rotary table's words by the library's stored words, for the
pieces of its digest. `ropeW j`: the right sides of `Meaning.Rope.table_words`
(Johnson/Goal/Meaning/RopeScope.lean): first the 65,536 cosines, then the 65,536 sines.
`t1T`: the counter's high word in every call of the compression function for a list of 131,072 words
under the number 72 (`tableHashNumber`, OnBytes/Model/Config.lean).
Definitions alone.

-/
import Johnson.Unfolds.SecondHashFunctionChain
import Inst.Model.TablesRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Rope

/-- Entry j of the rotary table (cs 12, theta0 500000, dh 128, lt 10) by the stored words. -/
def ropeW (j : Nat) : Nat :=
  if j < 65536 then Inst.Model.dec Inst.Model.Data.cos 14 j
  else Inst.Model.dec Inst.Model.Data.sin 14 (j - 65536)

/-- `secondHashFunctionState`'s t1 at the number 72 and 131,072 words. -/
def t1T : UInt64 := UInt64.ofNat (72 + 4294967296 * 131072)

end Johnson.Unfolds.Rope

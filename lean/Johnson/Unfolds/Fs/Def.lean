-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Fs/Def.lean: table FS's words by the library's stored words, for the pieces of its
digest. `fsW u`: the right sides of `Meaning.Gate.sig_word` (below 32,768) and `fs_upper` (from
there on; Johnson/Meaning/GateRows.lean) as natural numbers.
`t1T`: the counter's high word in every call of the compression function for a list of 65,536 words
under the number 72 (`tableHashNumber`, OnBytes/Model/Config.lean).
Definitions alone.

-/
import Johnson.Unfolds.SecondHashFunctionChain
import Inst.Model.TablesRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Fs

/-- Entry u of table FS (routed experts, the gate's clamp) by the library's stored words. -/
def fsW (u : Nat) : Nat :=
  if u < 32768 then (Inst.Model.refSIGM ((u : Int) + 2 ^ 14)).toNat
  else (Inst.Model.clamp 127 ((u : Int) - 49152) + 128).toNat

/-- `secondHashFunctionState`'s t1 at the number 72 and 65,536 words. -/
def t1T : UInt64 := UInt64.ofNat (72 + 4294967296 * 65536)

end Johnson.Unfolds.Fs

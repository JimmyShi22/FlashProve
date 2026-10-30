-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/TieK12.lean: the numbers of a key file's three later proximity tests, as
Written.lean in this folder has them (four fields by formula, three typed by hand), are those of the
typed places of Johnson/Desc/K12/Law/PlacesKeyFull.lean. Closed statements by evaluations in Lean's
kernel, field by field (`nums_of_same`, Typed.lean in this folder).

Main names. `u_tie : uNums = H2K.Member.piKUFull.nums`; `o_tie`, `w_tie`: the like.

Limits. Of a place only `nums` is tied. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.Typed
import Johnson.Desc.K12.Law.PlacesKeyFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

theorem u_tie : uNums = H2K.Member.piKUFull.nums := nums_of_same (by decide +kernel)

theorem o_tie : oNums = H2K.Member.piKOFull.nums := nums_of_same (by decide +kernel)

theorem w_tie : wNums = H2K.Member.piKWFull.nums := nums_of_same (by decide +kernel)

end Johnson.KB8

#print axioms Johnson.KB8.u_tie
#print axioms Johnson.KB8.o_tie
#print axioms Johnson.KB8.w_tie

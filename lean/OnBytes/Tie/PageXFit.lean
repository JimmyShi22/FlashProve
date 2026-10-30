-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PageXFit.lean: second names for declarations of the library taken from this file.
The encoding's data at a description of a chain that opens stored tables are in Run/PageX.lean;
their fit with the typed oracle functions is in Run/PageXFit.lean.

This file declares nothing. Each name that it exports into the namespace `OnBytes.Tie` is
a second name for the library's declaration of the same short name: `export` makes `OnBytes.Tie.x`
resolve to it, so the files above write `x`, `Tie.x` or `OnBytes.Tie.x`. Its imports are there so
that the files above see through it what they need.

What is not claimed. That the library's text is this file's former text is no theorem. Two programs
have compared them, declaration by declaration, outside comments and up to the prefixes `_root_.`
and `Compile.Batch.`: the same tokens, but for one: `serAllX` writes a stored symbol's position by
`Ser.natG` (binary) where this file had `Ser.nat` (unary), so the strings behind the byte 2 are
others. A name that Lean makes for a structure (a field, `mk`, `rec`) has no second name here. Dot
notation on a value goes by the value's type and needs none; a later declaration `OnBytes.Tie.S.x`
for a structure S that has moved would not be found by it.

-/
import Run.PageX
import Run.PageXFit
import OnBytes.Tie.PageXAgree
import OnBytes.Tie.FamPd
import Run.PlanQXRun
import Run.PageQFit
import Run.PageIsReaders

namespace OnBytes.Tie

export _root_.Run.PQ (
    tagsOK_all PBX chainDX chainDX_fit leafPX leafPX_fit symX pbX serAllX StmInv stmX unstmX
    unstm_stmX stm_unstmX pdX bytes_pdX selF mkF selF_some mkF_selF selF_mkF first0X firstPX
    firstPX_hdr firstPX_fit pageXPd callsX famXPd_eq_famT firstXPd_succ firstXPd_zero leafX_own
    storedX_fit pageXPd_fit implX_stored_string implX_first_string famXPd_leaf_read
    famXPd_node_read famXPd_last_read famXPd_whole_read famXPd_readSome pageX)

end OnBytes.Tie

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Page174.lean: second names for declarations of the library taken from this file.
The partial code of a leaf query on a symbol of a stored table (call number 174) is in
Run/CodingPage174.lean.

This file declares nothing. Each name that it exports into the namespace `OnBytes.Tie` is
a second name for the library's declaration of the same short name: `export` makes `OnBytes.Tie.x`
resolve to it, so the files above write `x`, `Tie.x` or `OnBytes.Tie.x`. Its imports are there so
that the files above see through it what they need.

What is not claimed. That the library's text is this file's former text is no theorem. Two programs
have compared them, declaration by declaration, outside comments and up to the prefixes `_root_.`
and `Compile.Batch.`: the same tokens. A name that Lean makes for a structure (a field, `mk`, `rec`)
has no second name here. Dot notation on a value goes by the value's type and needs none; a
later declaration `OnBytes.Tie.S.x` for a structure S that has moved would not be found by it.

-/
import Run.CodingPage174
import Run.CodingPage
import Run.PageQChain

namespace OnBytes.Tie

export _root_.Run (
    take16_u64 tag_low t174 t174_differs nilTo consTo pCol pCol_put pCol_some pCol_len widthTo
    widthOfWord widthOfWord_widthTo widthTo_widthOfWord pW pW_len posOfWord pPos pPos_len fillS
    pStored4 symOf pStored storedStr storedOK pStored_some pStored_put pStored_tag leafSelS
    leafMkS leafSelS_mk leafMkS_sel startIs pLeafS pLeafS_put pLeafS_some pLeafS_facts)

end OnBytes.Tie

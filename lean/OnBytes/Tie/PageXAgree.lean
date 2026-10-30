-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PageXAgree.lean: second names for declarations of the library taken from this file.
Where the typed oracle functions agree with what the encoding reads out of the single oracle is in
Run/CodingAgreeX.lean.

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
import Run.CodingAgreeX
import OnBytes.Tie.PageX
import Run.CodingAgree
import Run.OCompM
import Run.Toy1TieTree

namespace OnBytes.Tie

export _root_.Run (
    CallsX famT famT_fb_self FitX ansOf_oB leafT_agree nodeT_agree fb_block fb_agree_last
    fb_agree_all fitsCX needCX fitsCX_fb fitsCX_fb_ne needCX_fb fits_last fits_all agreeX_block
    agreeX)

end OnBytes.Tie

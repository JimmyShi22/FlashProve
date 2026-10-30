-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PageXAsked.lean: second names for declarations of the library taken from this file.
What the compiled verifier asks on a typed string, and that its run at the typed oracle functions is
its run at what the encoding reads out of the single oracle, is in Run/PageXAsked.lean.

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
import Run.PageXAsked
import OnBytes.Tie.PageXFit
import Run.OneIsTypedTop
import Run.ThinTie

namespace OnBytes.Tie

export _root_.Run.PQ (
    PqX PlX embX wX later_fitsX askP_loX askP_tailX first_fitsX askP_allX own_fitsX StoredFits
    stored_fitsX extWP_inp TypedOK askedX verifyP_readX verifyBS_readX)

end OnBytes.Tie

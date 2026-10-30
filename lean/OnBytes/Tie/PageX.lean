-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PageX.lean: second names for declarations of the library taken from this file.
The encoding of the typed queries, with the stored tables' leaves among the queries that the format
writes, is in Run/CodingPageX.lean. `Run.PCode.join` and its three laws stand there under
that very name, and need no second name.

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
import Run.CodingPageX
import OnBytes.Tie.Page174

namespace OnBytes.Tie

export _root_.Run (
    PageCX pStoredLeaf pStoredLeaf_facts pLeaf_not_stored pLeaf2 pLeaf2_facts p3X Tag5 p3X_facts
    pAllX pAllX_facts pAllX_no2 totalX totalX_esc theImplX theImplX_leaf1 theImplX_node1
    theImplX_rngLeaf theImplX_rngNode theImplX_fbK theImplX_leaf theImplX_own theImplX_stored
    theImplX_node theImplX_fb theImplX_spare theImplX_other)

end OnBytes.Tie

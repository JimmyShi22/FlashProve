-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Layout/TieRfl.lean: ONE THEOREM, ALONE IN ITS FILE: THE FROZEN LITERAL OF THE STORED
FULL-SIZE LAYOUT FILE IS `String.ofList` OF THE FOURTEEN WRITTEN PIECES' CHARACTERS.
  **`lay_chars`**: `OnBytes.Tie.Pv.Plan.layoutF = String.ofList (pieces.flatten.map chr)`: BY LEAN's
    CHECKER's OWN COMPARISON (`kernel_rfl`, Johnson/Unfolds/KernelRfl.lean): it opens the literal as
    `String.ofList ‹224,975 characters›` and compares the two lists, one character after the other.
THIS FILE WANTS A LARGER THREAD STACK THAN LEAN's DEFAULT: the comparison is nested one level a
character. Under the default (8 MB) Lean says "(kernel) deep recursion detected". Under
`lean --tstack=131072` (128 MB) it passes, and in one trial under 262144: on one machine 43
to 46 s, about 6 GB.
A REPLAY OF THE COMPILED PROOF THROUGH LEAN's KERNEL MEETS THE SAME NEST. Measured in one sitting,
on another machine: by the toolchain's `replayFromImports` inside `lake env lean`, at the default
thread stack it fails with the same message, and with `--tstack=131072` it passes (37.8 s). The
program `leanchecker` fails at this module with the same message at a shell stack limit of 8 MiB,
of 256 MiB and of 1 GiB alike: these larger limits did not help it ("unlimited" was not tried).
WHY IT LIES HERE, with the two files that stand on it (Tie.lean, Size.lean), and not beside the
pieces under Johnson/Unfolds/Layout/: the library `AtFullSide` in lakefile.toml stands outside the
main library and hands Lean that argument (`lake build AtFullSide`). Under Johnson/ Lake compiles
this file at the default stack and it fails (seen), and the main library takes every module under
Johnson/. A file that imports one of the three belongs in this library too: under Johnson/ it would
draw them beneath the main library. The namespace stays `Johnson.Unfolds.Layout`. Tie.lean and
Size.lean pass at the default stack too.
Limits. A closed fact on one stored file. Nothing on soundness.
-/
import Johnson.Unfolds.KernelRfl
import Johnson.Unfolds.StringBytes
import Johnson.Unfolds.Layout.Pieces
import Ladder.Stored

namespace Johnson.Unfolds.Layout

/-- **The literal is the pieces' characters.** -/
theorem lay_chars :
    OnBytes.Tie.Pv.Plan.layoutF = String.ofList (pieces.flatten.map Johnson.Unfolds.chr) := by
  kernel_rfl

end Johnson.Unfolds.Layout

#print axioms Johnson.Unfolds.Layout.lay_chars

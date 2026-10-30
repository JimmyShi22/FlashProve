-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookLineWritten.lean

It states no goal. No property of the protocol is claimed.

The 26 times four Booleans, written: a
definition alone, in a file of its own, so that the closed line over the plan (LotLBookLineFolds.lean)
and the closed lines over the messages (LotLBookLineEntries.lean) do not stand over one another.

  `foldFlagsW`

Limits. A definition. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLineLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

/-- **The Booleans, written**: at 24 rounds all false; at the 25th the switch's part sends what the
fold leaves; at the 26th the test's second part does. -/
def foldFlagsW : List ((Bool × Bool) × (Bool × Bool)) :=
  List.replicate 24 ((false, false), (false, false)) ++
    [((false, true), (false, false)), ((false, false), (false, true))]

end ProofFile.Honest.K12.AtProof

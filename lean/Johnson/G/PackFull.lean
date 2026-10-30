-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/PackFull.lean: the list of Johnson/G/PackList.lean at the full-size example.

Main names:
  `packFull`: `packListOf` at the three public files of prover/examples/target_full_f2, as
    Johnson/G/KitFull.lean holds them; empty if the making refuses.
Whence the numbers of the test: Lean's evaluator, from these three files alone; no other file is
read.
Limits: those of Johnson/G/PackList.lean. The test is evidence by evaluation at one example. An
empty list would make a statement over all its elements true and worthless: the test stands against
that.
-/
import Johnson.G.PackList
import Johnson.G.KitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes

/-- The list at the full-size example; empty if the making refuses. -/
def packFull : List (Codes × List (OracleShape × Nat)) :=
  (packListOf KitFull.policy.toUTF8 KitFull.layout.toUTF8 KitFull.scales).toOption.getD []

-- 119 sendings, 207 sampled messages
#guard packFull.length == 119 && (packFull.map (·.2.length)).sum == 207

end Johnson.G

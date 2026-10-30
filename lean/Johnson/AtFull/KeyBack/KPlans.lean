-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/KPlans.lean: THREE SHORT NAMES FOR LISTS OF ENTRIES OF THE KEY FILE's WRITTEN
PRICED PLANS (`keyThree`, Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean). Definitions alone.
  `roundsA`: the rounds of the first written plan, as `Key.rangesNumbers` reads them of a given
    plan: its entries without the entry "RECORD".
  `entriesB`, `entriesC`: the entries of the second and third written plan, as `Key.keyTestCut`
    reads them of a made plan.
Limits. No theorem is here.

-/
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open VerifiableInference.Number.ByRuns (keyThree)

/-- The first written plan's rounds. -/
abbrev roundsA : List Fmt.Entry := keyThree.A.plan.plan.rounds

/-- The second written plan's entries. -/
abbrev entriesB : List Fmt.Entry := keyThree.B.plan.rounds.map (·.entry)

/-- The third written plan's entries. -/
abbrev entriesC : List Fmt.Entry := keyThree.C.plan.rounds.map (·.entry)

end Johnson.AtFull.KeyBack

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3RoundsD.lean: THE LOT OF THE KIND "LOOKUP": THE DECLARED ROUNDS OF THE
FOUR WRITTEN PARAMETERS OF THE LOOKUPS ON THE DIGITS (`coreW s true`, K3Written.lean) ARE THE
TABLE's LISTS AT THE SORTS' NAMES (`Johnson.AtFull.Rounds.listAt`, `repW`): 746, 716, 746 and 746
rounds. Four closed facts, decided by Lean's kernel: the planner (`lookEntries`) is run at the
written shape.
Limits. Written values on both sides. One check by Lean's own kernel. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3RoundsNames

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Lots.K3

theorem rounds_d0 : (coreW 0 true).rounds = Johnson.AtFull.Rounds.listAt (repW 0 true) := by
  decide +kernel

theorem rounds_d1 : (coreW 1 true).rounds = Johnson.AtFull.Rounds.listAt (repW 1 true) := by
  decide +kernel

theorem rounds_d2 : (coreW 2 true).rounds = Johnson.AtFull.Rounds.listAt (repW 2 true) := by
  decide +kernel

theorem rounds_d3 : (coreW 3 true).rounds = Johnson.AtFull.Rounds.listAt (repW 3 true) := by
  decide +kernel

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.rounds_d0
#print axioms Johnson.AtFull.Lots.K3.rounds_d1
#print axioms Johnson.AtFull.Lots.K3.rounds_d2
#print axioms Johnson.AtFull.Lots.K3.rounds_d3

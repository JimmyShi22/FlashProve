-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3RoundsC.lean: THE LOT OF THE KIND "LOOKUP": THE DECLARED ROUNDS OF THE
FOUR WRITTEN PARAMETERS OF THE LOOKUPS ON THE CALLS (`coreW s false`, K3Written.lean) ARE THE
TABLE's LISTS AT THE SORTS' NAMES (`Johnson.AtFull.Rounds.listAt`, `repW`): 1046, 984, 1046 and 1080
rounds. Four closed facts, decided by Lean's kernel: the planner (`lookEntries`) is run at the
written shape.
Limits. Written values on both sides. One check by Lean's own kernel. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3RoundsNames

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Lots.K3

theorem rounds_c0 : (coreW 0 false).rounds = Johnson.AtFull.Rounds.listAt (repW 0 false) := by
  decide +kernel

theorem rounds_c1 : (coreW 1 false).rounds = Johnson.AtFull.Rounds.listAt (repW 1 false) := by
  decide +kernel

theorem rounds_c2 : (coreW 2 false).rounds = Johnson.AtFull.Rounds.listAt (repW 2 false) := by
  decide +kernel

theorem rounds_c3 : (coreW 3 false).rounds = Johnson.AtFull.Rounds.listAt (repW 3 false) := by
  decide +kernel

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.rounds_c0
#print axioms Johnson.AtFull.Lots.K3.rounds_c1
#print axioms Johnson.AtFull.Lots.K3.rounds_c2
#print axioms Johnson.AtFull.Lots.K3.rounds_c3

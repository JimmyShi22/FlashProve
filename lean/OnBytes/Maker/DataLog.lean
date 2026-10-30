-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/DataLog.lean: "every round's positions have at most 64 bits", as a test with code on
the data of a whole file.

That condition is the premise of `planDraws_law` (Run/PlanDraws.lean), the field `log` of `RMap.OK`
(OnBytes/Flat/CarrySMaps.lean), and the one condition on data of a theorem [`whole_sound_typed`,
OnBytes/Maker/KitSound.lean: not in this library]. Two definitions, one statement with its proof.

Main names (namespace `OnBytes.Maker.DataLog`):
  `logD D : Bool`: the test, over the three chains' rounds.
  `logD_gives`: its value true gives the condition, in the shape in which `whole_sound_typed`
    takes it.
  `logRows DK DP`: the test at two files' data, as two named rows.
Limits: no data are written here, and the test is evaluated at none.

-/
import OnBytes.Maker.Whole

set_option autoImplicit false

namespace OnBytes.Maker.DataLog
open OnBytes.Maker

/-- Every written round's positions have at most 64 bits. -/
def logD (D : WholeD) : Bool :=
  (D.ds₁ ++ (D.ds₂ ++ D.ds₃)).all fun d => decide (d.entry.logN ≤ 64)

theorem logD_gives {D : WholeD} (h : logD D = true) :
    ∀ d ∈ toRDs D.ds₁ ++ (toRDs D.ds₂ ++ toRDs D.ds₃), d.entry.logN ≤ 64 := by
  intro d hd
  have hd' : d ∈ toRDs (D.ds₁ ++ (D.ds₂ ++ D.ds₃)) := by
    show d ∈ (D.ds₁ ++ (D.ds₂ ++ D.ds₃)).map (·.toRD)
    rw [List.map_append, List.map_append]
    exact hd
  obtain ⟨d', hm, rfl⟩ := List.mem_map.1 hd'
  exact of_decide_eq_true (List.all_eq_true.1 h d' hm)

/-- The test at the data of a key file and of a proof file. -/
def logRows (DK DP : WholeD) : List (String × Bool) :=
  [("reading.1: the key file's data: every round's positions have at most 64 bits", logD DK),
    ("reading.2: the proof file's data: the same", logD DP)]

end OnBytes.Maker.DataLog

#print axioms OnBytes.Maker.DataLog.logD_gives

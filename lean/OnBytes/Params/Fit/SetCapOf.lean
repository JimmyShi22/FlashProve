-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/SetCapOf.lean: the setting that the parameter file's lines fix has the caps that
the walk along the planner asks of a setting.

"SetCap s" (OnBytes/Params/Fit/FitCalc.lean) asks five things of a setting: at most four answers to
a sample, a field below 2 ^ 64, a target of at most 256, at most 2 ^ 20 instances (by the
logarithm), and at most 2 ^ 32 positions for every list. "settingOf l"
(OnBytes/Params/Setting.lean) takes the answers and the target from the lines and leaves the field
and the instances at their default values.

Main theorems.
 - setCap_of_lines: LinesCap l (OnBytes/Params/Fit/LinesCap.lean) gives SetCap (settingOf l).
 - **setCap_of_read**: readLines pol = .ok (l, rest) gives SetCap (settingOf l).

Limits. Of settingOf's value alone: a setting that is made from it by changing a field is not
treated. The program does not import this file.


-/
import OnBytes.Params.Fit.FitCalc
import OnBytes.Params.Fit.LinesCap
import OnBytes.Params.Fit.PositionsCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- The lines' ranges give the setting's caps. -/
theorem setCap_of_lines {l : Lines} (H : LinesCap l) : SetCap (settingOf l) where
  samples := H.answers.2
  p := by
    show 2 ^ 64 - 2 ^ 32 + 1 < 2 ^ 64
    omega
  target := H.sec.2
  inst := by
    show clog2 1 ≤ 20
    simp [clog2]
  pos := fun c agree extra => Fit.scopePositions_le (settingOf l) c agree extra

/-- **The reader's yes gives the setting's caps.** -/
theorem setCap_of_read {pol rest : ByteArray} {l : Lines} (h : readLines pol = .ok (l, rest)) :
    SetCap (settingOf l) := setCap_of_lines (linesCap_of_read h)

end OnBytes.Params

#print axioms OnBytes.Params.setCap_of_lines
#print axioms OnBytes.Params.setCap_of_read

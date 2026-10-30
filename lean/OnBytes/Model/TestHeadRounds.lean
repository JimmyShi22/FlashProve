-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestHeadRounds.lean: tests of the numbers that the output head's sub-proof gives to
the planner, at a small configuration, spelled out in OnBytes/Model/TestHeadLayout.lean. The
expected values are what the C++ verifier computes in a planning call. No test here runs that
verifier. One value, 1594, is the sum of the numbers of columns of the five matrices. The plan is
put together here: planH2 is not run, and the guard itself puts in lkW and rows. HPlanH2.rounds is
not run. The program does not import this file.
-/
import OnBytes.Model.HeadRounds
import OnBytes.Model.TestHeadPlan

namespace OnBytes.Model.Head

#guard (smallLayout.toOption.map fun L => forestSize L.fs) == some ⟨23, 19, true⟩
#guard (smallTail.toOption.map smallSize) == some ⟨1594, 128, ⟨24, 11, true⟩⟩
#guard ((do
    let tl ← smallTail
    let P : HPlanH2 := { tl := tl, Fp := {}, Tp := {}, lkW := 11, rows := 897 + tl.equationsF 707 }
    pure (P.own smallShape)).toOption) == some ⟨6, 9, 11, 9, 7, 4, 2712833⟩

end OnBytes.Model.Head

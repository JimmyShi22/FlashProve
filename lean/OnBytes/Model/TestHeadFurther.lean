-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestHeadFurther.lean: the field NMINH (the line nminH) in the layout of the output
head and in the counts of its plan.

`keyFloor` (OnBytes/Model/HeadLayout.lean) takes NMINH, where it is not 0, in the place of nmin. A
line nminH that is not above nmin is refused (policy-nminH, `polBeforeLayout`,
OnBytes/Model/Config.lean), so the line can only raise the floor. Both shapes here keep that rule.
For nmin 20 with NMINH 21 the expected values are what the C++ verifier computes in a planning call
on the small configuration's parameter file with the line nminH 21 added. For nmin 16 with NMINH 20
they are the values for nmin 20 without the line; no planning call was run with these two numbers.
The guards would also hold if the floor were the larger of the two numbers. No test here runs that
verifier or reads a parameter file. `planH2`, whose test internal-h-settings reads NMINH, is not
run. That the layers do not read nminH is not tested. The program does not import this file.
-/
import OnBytes.Model.TestHeadPlan

namespace OnBytes.Model.Head

/-- What the tests below read of the layout for the numbers h, if there is one. -/
def floorView (h : Shape) : Option (List (Nat × Nat) × List (Nat × Nat) × List Nat × Array Nat ×
    Array Nat × Array Nat × Nat) :=
  (layout h someTable).toOption.map fun L =>
    (L.calls.toList.map fun c => (c.lJ, c.J), L.cl.toList.map fun c => (c.n, c.iota),
      [L.fs.dT, L.fs.kT, L.fs.NT, L.fs.rK, L.fs.NC, L.fs.cK], L.fs.first, L.fs.callOf, L.fs.pub,
      L.fs.padding)

/-- The example's numbers with the floor on the keys of the head's calls raised from 20 to 21. -/
def floor21 : Shape := { smallShape with NMINH := 21 }

/-- The example's numbers with nmin 16, and the floor of the head's calls raised back to 20. -/
def floorBack : Shape := { smallShape with nmin := 16, NMINH := 20 }

#guard keyFloor smallShape == 20 && keyFloor floor21 == 21 && keyFloor floorBack == 20
-- every call has twice the example's columns
#guard floorView floor21 ==
  some ([(15, 32768), (15, 32768), (15, 32768), (15, 32768), (15, 32768), (15, 32768)],
    [(21, 0), (21, 0), (21, 0), (21, 0), (21, 0), (21, 0)], [21, 16, 6, 3, 6, 3],
    #[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 5],
    #[1998848, 2064384, 2056704, 2080768, 2080768, 2064384], 16540160)
#guard (countsAt floor21 smallBorder).toOption == some [2930, 898, 11264, 707, 783, 2712834]
-- with NMINH 20 the lower nmin changes none of these values
#guard (floorView floorBack).isSome && floorView floorBack == floorView smallShape
#guard (countsAt floorBack smallBorder).toOption == some [2879, 897, 11264, 707, 783, 2712833]

end OnBytes.Model.Head

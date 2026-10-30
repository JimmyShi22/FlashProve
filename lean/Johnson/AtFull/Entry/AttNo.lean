-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/AttNo.lean: NEGATIVE TESTS beside AttRow0.lean to AttRow6.lean, by Lean's
kernel: the form in which these closed facts are stated can say no. Three theorems.
  `att_7_no`: the makers return, and the row at the number 7, which is no test's, says no.
  `att_none_no`: the makers return, and with the last group's plan taken away row 1 says no.
  `att_0_bent_no`: with every plan's number of slots laid to 0, row 0 says no. All twelve plans are
    there (the bend keeps their number), and test 0 is one comparison: so the no is that
    comparison's.
Limits. Three bends, not a search; the first two do not reach a test. For the tests 1 to 6 no bend
at a present plan is tried. Nothing on soundness, on a binding of the commitment (the opening form,
`BindsWith`), on correctness of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Entry.AttLaw
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Entry
open Johnson.AtFull.Public (atMakers)
open OnBytes.Road.K4.Trial.AttK7Owners (PW)

/-- No test has the number 7. -/
theorem att_7_no : atMakers (fun _ _ A => !rowA 7 PW A) = true := by decide +kernel

/-- Eleven plans are not enough. -/
theorem att_none_no : atMakers (fun _ _ A => !rowA 1 PW A.pop) = true := by decide +kernel

/-- Without slots the lookup's own scalars do not lie among them. -/
theorem att_0_bent_no :
    atMakers (fun _ _ A => !rowA 0 PW (A.map fun a => { a with ns := 0 })) = true := by
  decide +kernel

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.att_7_no
#print axioms Johnson.AtFull.Entry.att_none_no
#print axioms Johnson.AtFull.Entry.att_0_bent_no

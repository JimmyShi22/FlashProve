-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/AttRow2.lean: A CLOSED FACT, BY LEAN's KERNEL, no free letter: at what the
public part's makers return at the full size (`atMakers`, Johnson/AtFull/Public/AtWitnesses.lean),
test number 2 of the seven on public data at the attention segments says yes at all twelve groups:
the lookup's numbers fit the segment's sizes (`K5Asks.testAt`, Johnson/Desc/First/Att/GuardO.lean;
`rowA`, AttLaw.lean). One theorem.
Limits. At the makers' twins and the written scan: the tie to the public part's own value is
`at_witnesses`' (AttAtX0.lean). That the row's form can say no (a lacking plan; a number that is no
test's), and that test 0 says no at a present plan that is bent, is shown in AttNo.lean; for the
tests 1 to 6 no bend at a present plan is tried. Nothing on soundness, on a binding of the
commitment (the opening form, `BindsWith`), on correctness of extraction, on completeness or on
hiding.
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

/-- **Test number 2 says yes at the twelve groups.** -/
theorem att_2 : atMakers (fun _ _ A => rowA 2 PW A) = true := by
  decide +kernel

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.att_2

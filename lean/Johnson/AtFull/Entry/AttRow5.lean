-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/AttRow5.lean: A CLOSED FACT, BY LEAN's KERNEL, no free letter: at what the
public part's makers return at the full size (`atMakers`, Johnson/AtFull/Public/AtWitnesses.lean),
test number 5 of the seven on public data at the attention segments says yes at all twelve groups:
the place's seven units are the description's seven families of pieces (`K5Asks.testAt`,
Johnson/Desc/First/Att/GuardO.lean; `rowA`, AttLaw.lean). One theorem. The test sorts a unit's
pieces by `List.mergeSort`, which the kernel does not unfold: the equation `mergeSort_eq`
(Johnson/Unfolds/MergeSort.lean) puts a text in its place that it does.
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
import Johnson.Unfolds.MergeSort

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Entry
open Johnson.AtFull.Public (atMakers)
open OnBytes.Road.K4.Trial.AttK7Owners (PW)
open VerifiableInference.Desc.First.Att.P

/-- The sort of a unit's pieces, in the form that the kernel evaluates. -/
theorem pcs_eq (u : UnitG) : pcsSortedN u = (Johnson.Unfolds.sortF (fun x y =>
    Decidable.decide (x.lam < y.lam) || (x.lam == y.lam && Decidable.decide (x.a ≤ y.a)))
      (u.pcs.length + 1) u.pcs).getD [] :=
  Johnson.Unfolds.mergeSort_eq _ _

/-- **Test number 5 says yes at the twelve groups.** -/
theorem att_5 : atMakers (fun _ _ A => rowA 5 PW A) = true := by
  simp only [rowA, K5Asks.testAt, unitsN, unitN, pcs_eq]
  decide +kernel

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.pcs_eq
#print axioms Johnson.AtFull.Entry.att_5

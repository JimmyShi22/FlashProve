-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/K3No.lean: NEGATIVE TESTS beside K3DigL.lean, K3DigA.lean, K3DigH.lean and
K3ReadsA.lean, by Lean's kernel: the form in which these closed facts are stated can say no. Five
theorems.
  `digL_swap_no`: the makers return, and the attention's structures held against the layers' written
    values say no: `digOk` at segment 0 with group 0's attention plan. It reaches the comparison of
    views.
  `digA_pop_no`, `readsA_pop_no`: with the last group's plan taken away `digAB`, `readsAB` say no.
    They do not reach a comparison.
  `digH_bent_no`: with the number lk of the weights' layout one higher `digHB` says no: the lookup's
    first slot is another. It reaches the comparison.
  `readsA_bent_no`: with every structure's number of matrices one higher `readsAB` says no. It
    reaches the comparison.
Limits. Five bends, not a search. Nothing on soundness, on a binding of the commitment (the opening
form, `BindsWith`), on correctness of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Entry.K3Places
import Johnson.AtFull.Public.AtWitnesses
import Johnson.AtFull.Head.PlanAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Entry
open Johnson.AtFull.Public (atMakers)

/-- An attention plan is not a layers' plan. -/
theorem digL_swap_no : atMakers (fun _ _ A => (A[0]?).any fun a =>
    !digOk 0 (placeD "layers" 0 a.seam.Fp.fillL a.ns a.seam.tl 0) a.seam.tl) = true := by
  decide +kernel

/-- Eleven plans are not enough. -/
theorem digA_pop_no : atMakers (fun _ _ A => !digAB A.pop) = true := by decide +kernel

theorem readsA_pop_no : atMakers (fun _ _ A => !readsAB A.pop) = true := by decide +kernel

/-- Another number lk gives another first slot. -/
theorem digH_bent_no : atMakers (fun L _ _ => !digHB
    { _root_.AtFull.Head.HW with Fp := _root_.AtFull.Head.HW.Fp.trimL } (L.wsLay.lk + 1)) = true :=
        by
  decide +kernel

/-- One matrix more is not the written structure. -/
theorem readsA_bent_no : atMakers (fun _ _ A => !readsAB (A.map fun a =>
    { a with seam := { a.seam with tl := { a.seam.tl with NM := a.seam.tl.NM + 1 } } })) = true :=
        by
  decide +kernel

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.digL_swap_no
#print axioms Johnson.AtFull.Entry.digA_pop_no
#print axioms Johnson.AtFull.Entry.readsA_pop_no
#print axioms Johnson.AtFull.Entry.digH_bent_no
#print axioms Johnson.AtFull.Entry.readsA_bent_no

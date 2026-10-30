-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/KernelAttNo.lean: Four negative tests of att_W
(Johnson/AtFull/K3X/KernelAtt.lean), by evaluation in Lean's kernel, each stated as "the makers
return twelve plans, and the test rejects" (so that neither a maker's refusal nor an empty list of
plans would pass for a rejection): with the last plan taken away; and, at every one of the twelve
plans, with the number of slots raised by one; with the third count of padding keys raised by one;
with the depth of a tree raised by one. At which clause each rejects is not shown. What follows is a
reading of the test's text, no theorem (a plain conjunction; each change touches one field; att_W
holds the other clauses true): the last plan taken away: there is no twelfth plan: no comparison is
reached; the slots: the comparison with the written number, and the first slot of the lookup on the
digits with it; the count: the comparison of the eleven counts; the depth: the host's count alone
reads it: whether that count returns nothing or another list is not shown.
Limits. All four changes are laid on the made values, behind the makers: they try the test's text,
not the makers. Most clauses of attOneT have no negative test of their own: the four calls, the
depth limit (lid), the number cf.lmb, the first free slot, and all that the lookup on the digits
reads. It is imported by nothing. Nothing on soundness.

-/
import Johnson.AtFull.K3X.KernelTests
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K3X
open Johnson.AtFull.Public (atMakers)

theorem att_no_eleven : atMakers (fun _ _ A => A.size == 12 && !attT A.pop) = true := by
  decide +kernel

theorem att_no_slots : atMakers (fun _ _ A => A.size == 12 &&
    A.all fun a => !attOneT { a with ns := a.ns + 1 }) = true := by decide +kernel

theorem att_no_count : atMakers (fun _ _ A => A.size == 12 && A.all fun a =>
    !attOneT { a with fs := { a.fs with pub := a.fs.pub.modify 2 (· + 1) } }) = true := by
  decide +kernel

theorem att_no_depth : atMakers (fun _ _ A => A.size == 12 && A.all fun a =>
    !attOneT { a with fs := { a.fs with dT := a.fs.dT + 1 } }) = true := by decide +kernel

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.att_no_eleven
#print axioms Johnson.AtFull.K3X.att_no_slots
#print axioms Johnson.AtFull.K3X.att_no_count
#print axioms Johnson.AtFull.K3X.att_no_depth

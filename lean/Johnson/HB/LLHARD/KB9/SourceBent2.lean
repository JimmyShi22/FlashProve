-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/SourceBent2.lean: WHICH OF THE NAMED TESTS ON A KEY FILE's SOURCE CAN REJECT:
NEGATIVE TESTS, CLAUSE BY CLAUSE, for `sourceClauses` (Johnson/Desc/Key/Source.lean: thirty) at the
closed source of the full size's written values (`YW`, Johnson/HB/LLHARD/KB4/SourceW.lean). That the
twenty-three which Lean's kernel evaluates there all accept is Johnson/HB/LLHARD/KB4/CFile.lean's
(`source_W`). Here one number of YW is moved, and all are asked again: each theorem lists the
numbers, from 0, of the clauses that reject. So it is seen that the clause can reject, and which
others reject with it. By evaluations in Lean's kernel (`decide +kernel`).

The seven clauses that are no closed question at YW (1 "setting", 2 "codes", 3 "shape", 5 "read", 6
"made", 11 "ranges", 12 "weights") are laid to true by `patch maskS`, as in `source_W`: of these
nothing is said here. "cut" (7) has its twin in CFile.lean (`source_no`); it rejects here too
wherever a value of the one-time chain as read is bent, since YW holds that value a second time, as
cut.

  The clauses 19 to 29. The tools and the clauses 0 to 18: Johnson/HB/LLHARD/KB9/SourceBent.lean.

Limits. Negative tests alone. YW is in what Key.sourceOf returns at no public files (the head of its
file says so). Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.SourceBent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open Johnson.KB4 (kW YW)

set_option maxRecDepth 1000000 in
/-- Clause 19, "member". Bent: in the one-time chain's shape the own group's mask code is one
higher. It rejects; and "cut" (7) and "lin" (10), which holds W's mask code against it. -/
theorem src_member : a_no (a_src (a_one fun o =>
    { o with lin := { o.lin with ownMaskCode := o.lin.ownMaskCode + 1 } })) =
    [7, 10, 19] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 20, "test.rng". Bent: the ranges' test has its first stage alone. It rejects; and
"cut" (7). -/
theorem src_testRng : a_no (a_src (a_one fun o =>
    { o with ranges := { o.ranges with stages := o.ranges.stages.take 1 } })) =
    [7, 20] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 21, "test.U". Bent: the folded row's test has its first stage alone. It alone rejects. -/
theorem src_testU : a_no (a_src (a_shared fun s =>
    { s with lin := { s.lin with testU := s.lin.testU.take 1 } })) =
    [21] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 22, "test.O". Bent: Omega's test has its first stage alone. It alone rejects. -/
theorem src_testO : a_no (a_src (a_shared fun s =>
    { s with lin := { s.lin with testOmega := s.lin.testOmega.take 1 } })) =
    [22] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 23, "test.own". Bent: the own test has its first stage alone. It alone rejects. -/
theorem src_testOwn : a_no (a_src (a_shared fun s =>
    { s with lin := { s.lin with testOwn := s.lin.testOwn.take 1 } })) =
    [23] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 24, "join.rng". Bent: the lookups' own message has no answer. It rejects; and "cut"
(7) and "samples" (18). -/
theorem src_joinRng : a_no (a_src (a_msg fun m => { m with answers := 0 })) =
    [7, 18, 24] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 25, "join.U". Bent: in the shared chain's shape the folded row's message has no
answer. It alone rejects. -/
theorem src_joinU : a_no (a_src (a_shared fun s => { s with lin := { s.lin with
    fold := { s.lin.fold with u := { s.lin.fold.u with answers := 0 } } } })) =
    [25] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 26, "join.O". Bent: in the shared chain's shape Omega has no answer. It rejects; and
"join.own" (27), of whose group Omega is a member too. -/
theorem src_joinO : a_no (a_src (a_shared fun s =>
    { s with lin := { s.lin with omega := { s.lin.omega with answers := 0 } } })) =
    [26, 27] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 27, "join.own". Bent: in the shared chain's shape W has no answer. It alone rejects. -/
theorem src_joinOwn : a_no (a_src (a_shared fun s =>
    { s with lin := { s.lin with w := { s.lin.w with answers := 0 } } })) =
    [27] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 28, "alone". Bent: Omega's tree, which the own test reads too, is told a second
tenant, of no words and without a sample. It alone rejects. -/
theorem src_alone : a_no (a_src ({ YW with told := (YW.told.1, YW.told.2.1.zipIdx.map fun r =>
    if r.2 == 1 then { r.1 with tenants := r.1.tenants ++ [⟨0, 0, 1, false, []⟩] } else r.1,
    YW.told.2.2) })) =
    [28] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 29, "grouped". Bent: the tenants of the first chain's first tree are told no group. It
alone rejects. -/
theorem src_grouped : a_no (a_src ({ YW with told := (YW.told.1.zipIdx.map fun r =>
    if r.2 == 0 then { r.1 with tenants := r.1.tenants.map fun t => { t with groups := [] } }
    else r.1, YW.told.2.1, YW.told.2.2) })) =
    [29] := by decide +kernel

end Johnson.KB9

#print axioms Johnson.KB9.src_member
#print axioms Johnson.KB9.src_testRng
#print axioms Johnson.KB9.src_testU
#print axioms Johnson.KB9.src_testO
#print axioms Johnson.KB9.src_testOwn
#print axioms Johnson.KB9.src_joinRng
#print axioms Johnson.KB9.src_joinU
#print axioms Johnson.KB9.src_joinO
#print axioms Johnson.KB9.src_joinOwn
#print axioms Johnson.KB9.src_alone
#print axioms Johnson.KB9.src_grouped

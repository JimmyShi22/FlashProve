-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/PlanBent.lean: WHICH OF THE NINE TESTS ON THE PLANS' ENTRIES CAN REJECT:
NEGATIVE TESTS, CLAUSE BY CLAUSE, for `planClauses` (Johnson/Desc/Key/FileOk.lean; the first eight:
`Plan.clausesAt`, Johnson/Desc/Key/Plan/Eight.lean) at the full size's written values (`kW`,
Johnson/HB/LLHARD/KB4/SourceW.lean) and the written declared rounds' three lengths. That all nine
accept there is Johnson/HB/LLHARD/KB4/CFile.lean's (`plan_W`). Here one number of kW is moved, and
all nine are asked again: each theorem lists the numbers, from 0, of the clauses that reject. By
evaluations in Lean's kernel (`decide +kernel`).

The eighth clause (7: the steps use up the plans' rounds) has its twin in CFile.lean (`plan_no`).

  `a_pln k`: the nine values. `pln_unbent`: nine values, no reject. Then the clauses 0 to 6 and 8.

Limits. Negative tests alone. Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.ShapeBent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (planClauses)
open Johnson.KB4 (kW)
open Johnson.KB8 (declKeyFull)

/-- The nine clauses' values, at the written declared rounds' three lengths. -/
def a_pln (k : KeyChains) : List Bool :=
  (planClauses k declKeyFull.1.length declKeyFull.2.1.length declKeyFull.2.2.length).map (·.2)

set_option maxRecDepth 1000000 in
/-- Unbent: nine values, no reject. -/
theorem pln_unbent : ((a_pln kW).length, a_no (a_pln kW)) = (9, []) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 0, okFirst. Bent: in the one-time chain's shape a row of the table holds twice as many
columns: the lookups and the batching would have more rounds. It alone rejects. -/
theorem pln_first : a_no (a_pln ((a_one fun o =>
    { o with lin := { o.lin with kLo := o.lin.kLo + 1 } }).k)) =
    [0] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 1, okFolded. Bent: in the shared chain's shape one column more is drawn. It alone
rejects. -/
theorem pln_folded : a_no (a_pln ((a_shared fun s => { s with lin := { s.lin with
    fold := { s.lin.fold with columns := s.lin.fold.columns + 1 } } }).k)) =
    [1] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 2, okOmega. Bent: the first stage of Omega's test names a code that is not there, so
that its code switch would draw positions below 2 ^ 0. The rounds' names are as before. It alone
rejects. -/
theorem pln_omega : a_no (a_pln ((a_shared fun s => { s with lin := { s.lin with
    testOmega := s.lin.testOmega.zipIdx.map fun x =>
      if x.2 == 0 then { x.1 with code := 99 } else x.1 } }).k)) =
    [2] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 3, the third chain's first: one answer to a sample. Bent: the third chain's plan says
two. It rejects; and the third chain's third and fourth (5, 6), whose wanted entries are made
with that number. -/
theorem pln_answers3 : a_no (a_pln (a_plan3 fun P => { P with samples := 2 })) =
    [3, 5, 6] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 4, the third chain's second: the own test's first stage has the group's codes. Bent:
in the shared chain's shape the own group's mask code is one higher. It alone rejects. -/
theorem pln_codes3 : a_no (a_pln ((a_shared fun s =>
    { s with lin := { s.lin with ownMaskCode := s.lin.ownMaskCode + 1 } }).k)) =
    [4] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 5, the third chain's third: its plan is just the test's entries. Bent: its first entry
has one byte more. It alone rejects. -/
theorem pln_entries3 : a_no (a_pln (a_plan3 fun P =>
    { P with entries := P.entries.zipIdx.map fun x =>
      if x.2 == 0 then { x.1 with msg := x.1.msg + 1 } else x.1 })) =
    [5] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 6, the third chain's fourth: the index-mask message's and W's sendings in the first
chain's plan. Bent: the index-mask message has no answer to a sample. It alone rejects. -/
theorem pln_sends3 : a_no (a_pln ((a_idx fun m => { m with answers := 0 }).k)) =
    [6] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 8, plan.seal. Bent: the shared chain's plan's last entry has another name. It alone
rejects. -/
theorem pln_seal : a_no (a_pln ((a_shared fun s =>
    { s with given := { s.given with plan := { s.given.plan with
      entries := s.given.plan.entries.dropLast ++
        s.given.plan.entries.getLast?.toList.map fun e => { e with name := "LAST" } } } }).k)) =
    [8] := by decide +kernel

end Johnson.KB9

#print axioms Johnson.KB9.pln_unbent
#print axioms Johnson.KB9.pln_first
#print axioms Johnson.KB9.pln_folded
#print axioms Johnson.KB9.pln_omega
#print axioms Johnson.KB9.pln_answers3
#print axioms Johnson.KB9.pln_codes3
#print axioms Johnson.KB9.pln_entries3
#print axioms Johnson.KB9.pln_sends3
#print axioms Johnson.KB9.pln_seal

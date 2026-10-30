-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/ShapeBent.lean: WHICH OF THE TWELVE TESTS ON THE THREE CHAINS' PUBLIC VALUES
CAN REJECT: NEGATIVE TESTS, CLAUSE BY CLAUSE, for `shapeClauses` (Johnson/Desc/Key/FileOk.lean) at
the full size's written values (`kW`, Johnson/HB/LLHARD/KB4/SourceW.lean; the shape off which the
rounds are made: `keyFull`'s). That the ten which Lean's kernel evaluates there all accept is
Johnson/HB/LLHARD/KB4/CFile.lean's (`shape_W`). Here one number of kW is moved, and all are asked
again: each theorem lists the numbers, from 0, of the clauses that reject. By evaluations in Lean's
kernel (`decide +kernel`).

The second clause (1: the program's own `Key.admitted`) and the tenth (9: what `KeyChains.read`
itself tests) are laid to true by `patch maskH`, as in `shape_W`: of these nothing is said here. The
fourth (3) has its twin in CFile.lean (`shape_no`). The last two (10, 11) reject here wherever the
shared chain's shape is bent: so they are seen to reject, with a companion.

  `a_shp k`: the twelve values. `a_plan3 f`: kW with f laid on the third chain's plan as read.
    `shp_unbent`: twelve values, no reject. Then the clauses 0, 2, 4, 5, 6, 7, 8.

Limits. Negative tests alone. Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.SourceBent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (shapeClauses)
open Johnson.KB4 (kW patch maskH)
open Lk6.AtPlan (keyFull)

/-- The twelve clauses' values; the two that are no closed question at kW laid to true. -/
def a_shp (k : KeyChains) : List Bool :=
  (patch maskH (shapeClauses k keyFull.once.shape)).map (·.2)

/-- kW with f laid on the third chain's plan as read. -/
def a_plan3 (f : Fmt.Plan → Fmt.Plan) : KeyChains :=
  { kW with second := { kW.second with
    given := { kW.second.given with plan := f kW.second.given.plan } } }

set_option maxRecDepth 1000000 in
/-- Unbent: twelve values, no reject. -/
theorem shp_unbent : ((a_shp kW).length, a_no (a_shp kW)) = (12, []) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The first. Bent: the third chain's plan is typed at the other field. It alone rejects. -/
theorem shp_field : a_no (a_shp (a_plan3 fun P => { P with field := .one })) =
    [0] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The third. Bent: the lookups' own message has one answer more than the plan says. It alone
rejects. -/
theorem shp_samples : a_no (a_shp ((a_msg fun m => { m with answers := m.answers + 1 }).k)) =
    [2] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The fifth. Bent: the third chain's plan says no answer to a sample. It alone rejects. -/
theorem shp_iopp3 : a_no (a_shp (a_plan3 fun P => { P with samples := 0 })) =
    [4] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The sixth. Bent: the first stage of the ranges' test stands under the next code. It alone
rejects. -/
theorem shp_joinRng : a_no (a_shp ((a_one fun o => { o with ranges := { o.ranges with
    stages := o.ranges.stages.zipIdx.map fun x =>
      if x.2 == 0 then { x.1 with code := x.1.code + 1 } else x.1 } }).k)) =
    [5] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The seventh. Bent: in the shared chain's shape the folded row's message has no answer. It
rejects; and the last two (10, 11), which hold that shape against the one-time chain's and
against the shape off which the rounds are made. -/
theorem shp_joinU : a_no (a_shp ((a_shared fun s => { s with lin := { s.lin with
    fold := { s.lin.fold with u := { s.lin.fold.u with answers := 0 } } } }).k)) =
    [6, 10, 11] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The eighth. Bent: in the shared chain's shape Omega has no answer. It rejects; and the ninth
(8), of whose group Omega is a member too, and the last two (10, 11). -/
theorem shp_joinO : a_no (a_shp ((a_shared fun s =>
    { s with lin := { s.lin with omega := { s.lin.omega with answers := 0 } } }).k)) =
    [7, 8, 10, 11] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The ninth. Bent: in the shared chain's shape W has no answer. It rejects; and the last two
(10, 11). -/
theorem shp_joinOwn : a_no (a_shp ((a_shared fun s =>
    { s with lin := { s.lin with w := { s.lin.w with answers := 0 } } }).k)) =
    [8, 10, 11] := by decide +kernel

end Johnson.KB9

#print axioms Johnson.KB9.shp_unbent
#print axioms Johnson.KB9.shp_field
#print axioms Johnson.KB9.shp_samples
#print axioms Johnson.KB9.shp_iopp3
#print axioms Johnson.KB9.shp_joinRng
#print axioms Johnson.KB9.shp_joinU
#print axioms Johnson.KB9.shp_joinO
#print axioms Johnson.KB9.shp_joinOwn

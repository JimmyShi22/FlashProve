-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/SourceBent.lean: WHICH OF THE NAMED TESTS ON A KEY FILE's SOURCE CAN REJECT:
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

  `a_src Y`: the thirty values. `a_no l`: the places of the rejects. `a_one`, `a_shared`, `a_idx`,
    `a_msg`: YW with a function laid on the one-time chain's values, the shared chain's, the
    index-mask message's shape, the lookups' own message's shape.
  `src_unbent`: thirty values, no reject. Then the clauses 0, 4, 8, 9, 10, 13 to 18. The clauses 19
    to 29: Johnson/HB/LLHARD/KB9/SourceBent2.lean.

Limits. Negative tests alone. YW is in what Key.sourceOf returns at no public files (the head of its
file says so). Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB4.SourceW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (KeySource sourceClauses)
open Johnson.KB4 (kW YW patch maskS)

/-- The thirty clauses' values; the seven that are no closed question at YW laid to true. -/
def a_src (Y : KeySource) : List Bool := (patch maskS (sourceClauses Y)).map (·.2)

/-- The places, from 0, of the rejects. -/
def a_no (l : List Bool) : List Nat := (l.zipIdx.filter fun x => !x.1).map (·.2)

/-- YW with f laid on the one-time chain's values. -/
def a_one (f : OneTime → OneTime) : KeySource :=
  { YW with k := { kW with oneTime := f kW.oneTime } }

/-- YW with f laid on the shared chain's values. -/
def a_shared (f : Shared → Shared) : KeySource :=
  { YW with k := { kW with shared := f kW.shared } }

/-- YW with f laid on the index-mask message's shape. -/
def a_idx (f : OracleShape → OracleShape) : KeySource :=
  a_one fun o => { o with indexMasks := { o.indexMasks with shape := f o.indexMasks.shape } }

/-- YW with f laid on the shape of the lookups' own message. -/
def a_msg (f : OracleShape → OracleShape) : KeySource :=
  a_one fun o => { o with ranges := { o.ranges with
    message := { o.ranges.message with shape := f o.ranges.message.shape } } }

set_option maxRecDepth 1000000 in
/-- Unbent: thirty values, no reject: so what follows is the bends' doing. -/
theorem src_unbent : ((a_src YW).length, a_no (a_src YW)) = (30, []) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 0, "field". Bent: the one-time chain's plan is typed at the other field. It alone
rejects. -/
theorem src_field : a_no (a_src (a_one fun o =>
    { o with given := { o.given with plan := { o.given.plan with field := .one } } })) =
    [0] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 4, "rounds". Bent: the third chain's declared rounds lack their last. It alone
rejects. -/
theorem src_rounds : a_no (a_src ({ YW with D := (YW.D.1, YW.D.2.1, YW.D.2.2.dropLast) })) =
    [4] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 8, "form". Bent: in the shared chain's shape masks are not sent ahead. It alone
rejects. -/
theorem src_form : a_no (a_src (a_shared fun s =>
    { s with lin := { s.lin with masksAhead := false } })) =
    [8] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 9, "lengths". Bent: one base code more, behind all that are named, with messages of 3
entries. It rejects; and "cut" (7), since the codes as read are no longer the codes as cut. -/
theorem src_lengths : a_no (a_src (a_one fun o =>
    { o with codes := { o.codes with base := o.codes.base.push ⟨0, 3, 0⟩ } })) =
    [7, 9] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 10, "lin". Bent: in the one-time chain's shape Omega has the shared split's class of
leaves. It rejects; and "cut" (7). -/
theorem src_lin : a_no (a_src (a_one fun o =>
    { o with lin := { o.lin with omegaLeafClass := o.lin.sharedSplitLeafClass } })) =
    [7, 10] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 13, "lookups". Bent: every lookup has 2 ^ 7 places for planes. It rejects; and "cut"
(7). -/
theorem src_lookups : a_no (a_src (a_one fun o => { o with ranges := { o.ranges with
    lookups := o.ranges.lookups.map fun l => { l with mu := 7 } } })) =
    [7, 13] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 14, "binding". Bent: the binding tree has the depth 1. It alone rejects. -/
theorem src_binding : a_no (a_src (a_one fun o => { o with binding := ⟨1, 0⟩ })) =
    [14] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 15, "messageId". Bent: the lookups' own message has the number 2. It rejects; and
"cut" (7). -/
theorem src_messageId : a_no (a_src (a_one fun o =>
    { o with ranges := { o.ranges with messageId := 2 } })) =
    [7, 15] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 16, "idx". Bent: the index-mask message has no answer to an out-of-domain sample. It
rejects; and "cut" (7), "member" (19) and "join.own" (27), which ask an answer of that message
too. -/
theorem src_idx : a_no (a_src (a_idx fun m => { m with answers := 0 })) =
    [7, 16, 19, 27] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 17, "idxRoom". Bent: the index-mask message has 10 ^ 6 answers, more than a mask row
has entries: no entry is free. It rejects; and "cut" (7). -/
theorem src_idxRoom : a_no (a_src (a_idx fun m => { m with answers := 10 ^ 6 })) =
    [7, 17] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Clause 18, "samples". Bent: the lookups' own message has one answer more than the plan says.
It rejects; and "cut" (7). -/
theorem src_samples : a_no (a_src (a_msg fun m => { m with answers := m.answers + 1 })) =
    [7, 18] := by decide +kernel

end Johnson.KB9

#print axioms Johnson.KB9.src_unbent
#print axioms Johnson.KB9.src_field
#print axioms Johnson.KB9.src_rounds
#print axioms Johnson.KB9.src_form
#print axioms Johnson.KB9.src_lengths
#print axioms Johnson.KB9.src_lin
#print axioms Johnson.KB9.src_lookups
#print axioms Johnson.KB9.src_binding
#print axioms Johnson.KB9.src_messageId
#print axioms Johnson.KB9.src_idx
#print axioms Johnson.KB9.src_idxRoom
#print axioms Johnson.KB9.src_samples

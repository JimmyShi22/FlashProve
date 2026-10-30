-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/ArmCount.lean: HOW MANY SCALARS THE ROUNDS OF AN ARM SEND: the planner's own
count (`Params.scalarsOf`, OnBytes/Params/Gate.lean) at the routine of an arm (`armRounds`,
Johnson/AtFull/Rows/ArmRounds.lean), over three moments, at the written setting. Two definitions and
a tool. A law file; no running text imports it. Nothing on codes.

  `armCount a`: the count. `countIs a n`: a test with code: the count returns n. `count_of_is`: a
    yes gives the equation.

Limits. Definitions and a tool: nothing is evaluated here. The four evaluations stand each in a file
of its own (CountHead, CountAtt, CountLayerFirst, CountLayer). There the count is taken piece by
piece (Johnson/AtFull/Rows/CountPieces.lean); each file's head says what it costs. A BAD RESULT,
KEPT: `countIs` itself, put before Lean's kernel whole at one of these arms, took 4 min 43 s to
7 min 17 s and 43 to 47.3 GiB resident on one machine (alone, two or four side by side, under a
limit of 72 GiB of address space a process); a cap of 47 GiB killed two of four such runs.
Nothing on soundness.

-/
import Johnson.AtFull.Rows.ArmRounds
import Johnson.Goal.Written.Made
import OnBytes.Params.Gate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Rows
open OnBytes OnBytes.Params VerifiableInference.Desc.LinkJoin
open VerifiableInference.PlanWritten.Joined (writtenSized)

/-- The scalars that an arm's rounds send, over three moments, at the written setting. -/
def armCount (a : Arm) : Except String Nat :=
  scalarsOf writtenSized.proof.set (forEach (List.range 3) fun m => armRounds a m)

/-- The count returns n. -/
def countIs (a : Arm) (n : Nat) : Bool :=
  match armCount a with
  | .ok k => k == n
  | .error _ => false

theorem count_of_is {a : Arm} {n : Nat} (h : countIs a n = true) : armCount a = .ok n := by
  unfold countIs at h
  cases e : armCount a with
  | error s =>
    rw [e] at h
    cases h
  | ok k =>
    rw [e] at h
    rw [eq_of_beq h]

end AtFull.Rows

#print axioms AtFull.Rows.count_of_is

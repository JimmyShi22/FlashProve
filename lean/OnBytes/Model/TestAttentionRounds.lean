-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionRounds.lean: tests of OnBytes/Model/AttentionRounds.lean.

The tests run when this file is compiled. The program does not import this file.

What is tested: the sizes of the first attention link of a small configuration, spelled out in
OnBytes/Model/TestAttentionPlan.lean (smallCfg, smallPlan). Of the link's planned rounds: three
totals (rounds, rounds with a draw, scalars), the scalars after moment 0, the one round after moment
1, and the last round. The other rounds are not compared one by one. No file of the repository is
read; the examples under prover/examples may have other numbers.

Where the expected numbers come from.
 1. The sizes. 22, 18 and 23, 11 are the numbers v and d of the two lookups (forestShape,
    verifier/src/vf_lookup_argument.h). 22 and 18 follow by hand: four calls of 2^20 keys each, and
    four tables of 2^16 rows. All four numbers were recorded from a run of the C++ verifier with
    added lines that only print. That build is not part of the repository. 1,276 is the sum of the
    matrices' columns, and 128 is the number tau that smallPlan passes.
 2. 3,076 scalars. The call cp_verify -plan request prints, with the option -fields, one line for
    each message of a proof. On public files with these numbers the lines of the link "attention 4"
    add up to 3,076 scalars.
 3. 1,525 rounds, 1,379 of them with a draw. No program prints these two numbers. They were counted
    in a list of the link's rounds that was written out from the C++ planner's source
    (blocks/numbers/blocks.h, prover/attn/plan_rounds.h, forestPlan, planRounds). The messages of
    that list were compared with the printed lines of point 2.
 4. 1,427, 502 and 2,074,535: see the head of OnBytes/Model/TestAttentionPlan.lean.
-/
import OnBytes.Model.AttentionRounds
import OnBytes.Model.TestAttentionPlan

namespace OnBytes.Attention.TestRounds

-- the lookup of the four calls: 2^22 keys, 2^18 rows, a shift
#guard (smallPlan.toOption.map fun P => Model.forestSize P.fs) == some ⟨22, 18, true⟩
-- the smallness test: 120 + 4 + 32 + 1024 + 96 columns; its lookup: 2^23 keys, 2^11 rows, a shift
#guard (smallPlan.toOption.map fun P => Model.smallSize P.seam.tl) ==
  some ⟨1276, 128, ⟨23, 11, true⟩⟩

/-- The plan's entries of the rounds after a moment, under `Setting`'s default values: a target of
128 bits and no work. -/
def entriesAfter (moment : Nat) : Option (List Fmt.Entry) := do
  let P ← smallPlan.toOption
  let planned ← (Params.finish {} .request (rounds P moment)).toOption
  pure (planned.rounds.map (·.entry))

/-- The number of rounds after a moment, the number of those in which something is drawn, and the
number of scalars of all their messages. -/
def countsAfter (moment : Nat) : Option (Nat × Nat × Nat) :=
  (entriesAfter moment).map fun l =>
    (l.length, (l.filter fun e => e.drawE + e.trits != 0).length, (l.map (·.msg / 24)).sum)

-- the three moments have 1,525 rounds, 1,379 of them with a draw, and 3,076 scalars
#guard ((List.range 3).mapM countsAfter).map (fun l =>
  ((l.map (·.1)).sum, (l.map (·.2.1)).sum, (l.map (·.2.2)).sum)) == some (1525, 1379, 3076)
-- after moment 0: the scalars of the lookup and of the own part
#guard (countsAfter 0).map (·.2.2) == some (1427 + 502)
-- after moment 1: one round, which draws 128 entries for each of the 1,276 columns
#guard (entriesAfter 1).map (fun l => l.map fun e => (e.name, e.msg, e.trits)) ==
  some [("RNG", 0, 128 * 1276)]
-- the last round batches all claims and equations
#guard (((entriesAfter 2).bind (·.getLast?)).map fun e => (e.name, e.rows)) ==
  some ("BAT-sigma", 2074535)
-- there is no fourth moment
#guard (smallPlan.toOption.map fun P => refusal (Params.finish {} .request (rounds P 3))) ==
  some (some "parameters-not-admitted")

end OnBytes.Attention.TestRounds

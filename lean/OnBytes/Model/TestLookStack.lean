-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLookStack.lean: the order of the challenges of a batched sumcheck, tested on
made-up messages.

stackRounds (OnBytes/Model/Look.lean) runs lam rounds and stores their challenges by bit: the top
bit is bound first, so rs[v] is the challenge of round lam - 1 - v. In a dry run all draws are 0 and
the order cannot be seen. Here the rounds are written by the script of
OnBytes/Model/TestLookProver.lean, whose draws are made-up elements; the first and the third differ
(a guard below). The program does not import this file.

What is tested when the file compiles. With three rounds the walk goes through, and rs holds the
third round's challenge, then the second's, then the first's. The messages are made-up elements, so
nothing is said on the sumcheck's claim.
-/
import OnBytes.Model.TestLookProver

namespace OnBytes.Model.Forest.Honest

/-- Rounds of two made-up coefficients each, after each of which the verifier draws one element. -/
def stackScript (lam : Nat) : Prover Unit := do
  for i in List.range lam do
    send [made (100 + 2 * i), made (101 + 2 * i)]
    let _ ← draw1

/-- The challenges by bit that stackRounds stores on these rounds; none if the walk fails or does
not use up all rounds. -/
def stackOn (lam : Nat) : Option (Array E) :=
  let rounds := (Id.run (StateT.run (stackScript lam) {})).2.rounds.toList
  match Blk.walk (StateT.run (stackRounds { lam := lam, p := {} }) (({} : Fork).slots (2 * lam)))
      { entries := List.replicate lam (Test.entry "PSC round" 2 1), st := {} } [] rounds with
  | some (x, []) => some x.1.rs
  | _ => none

-- draw number i of the script is made i
#guard stackOn 3 == some #[made 2, made 1, made 0]
#guard made 0 != made 2

end OnBytes.Model.Forest.Honest

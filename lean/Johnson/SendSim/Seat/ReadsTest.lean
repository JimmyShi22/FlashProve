-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsTest.lean: an executable test, which reads only a description, for the
bound on the positions that its own rounds query. Definitions only.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Executable definitions; no statement and no proof. The file has few imports, so
that the test can be run without the files that the statements on it need.
  readsWithinB  The test, at a description F, parameters P and a number n₀. For every oracle message
                of P that is in a tree τ: drawnFor at tree number n₀ + τ is at most the number of
                entries of the tail of the main code, if the oracle message has main rows, and of
                the mask code, if it has mask rows.
  opensIn       For one chain's declared rounds: for each round, the number of positions that it
                samples, once for each of the round's openings whose source is the first chain's
                tree number n; summed.
  drawnFor      The sum of opensIn over the three chains.
  treesOf       The number of trees (the description declares one Oracle for each root) that a
                chain's declared rounds announce before a given split of its list: the number n₀ at
                which the test is applied.

Limits.
The test accepts at an oracle message that is in no tree, and it accepts every oracle message if the
place's trees cannot be made (Own.treesMade returns nothing).
The test requires more than the bound. It counts a position once for each opening and each round,
whether or not two of them are equal modulo a code's length. If it rejects, nothing follows.
It covers only the first chain's trees (for the other chains: ReadsTestAt.lean).
It reads lists and numbers of the description's declared rounds: no input, no coin and no execution.
No distribution is named.

How it fits. What the test implies is stated in ReadsCount.lean and proved in ReadsCountProof.lean:
where it accepts, ReadsWithin (Bud.lean) holds, and so the rule's clause on queried positions for
the sender's row (BudClause). ReadsTestTie.lean proves that treesOf is the number in these
statements. budAtLots (AtDescLots.lean) applies the test to any list of jobs; LotsTestTie.lean uses
that at the jobs of the two lots.
-/
import Johnson.SendSim.At.Sim

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {Xi : Type}

/-- The number of positions that the declared rounds ds of chain number c sample for the first
chain's tree number n: for each round its number of positions, once for each of its openings with
that source. -/
def opensIn (c n : Nat) (ds : List Fmt.DeclaredRound) : Nat :=
  (ds.map fun d => (d.opens.filter fun o => srcOf c o.2 == (0, n)).length * d.entry.poss).sum

/-- The sum of opensIn over the description's three chains. -/
def drawnFor (F : FileDescription Xi) (n : Nat) : Nat :=
  opensIn 0 n F.roundsDeclaredByBlocks.1 + opensIn 1 n F.roundsDeclaredByBlocks.2.1 + opensIn 2 n F.roundsDeclaredByBlocks.2.2

/-- The test: for every oracle message of P that is in a tree τ, drawnFor at tree number n₀ + τ is
at most the tail's number of entries r, for the main code if it has main rows and for the mask code
if it has mask rows. It accepts at an oracle message that is in no tree. -/
def readsWithinB (F : FileDescription Xi) (P : K1.Par) (n₀ : Nat) : Bool :=
  (List.range P.sent.size).all fun k =>
    match ((Own.treesMade P.codes P.sent).getD {}).tree[k]? with
    | none => true
    | some τ =>
      ((shapeAt P k).mainRows == 0 ||
          decide (drawnFor F (n₀ + τ) ≤ (P.codes.base.getD (shapeAt P k).code default).r)) &&
        ((shapeAt P k).maskRows == 0 ||
          decide (drawnFor F (n₀ + τ) ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).r))

/-- The number of trees (the description declares one Oracle for each root) that are announced in
the rounds of pre, where pre is the start of the list bs: so many are announced before the
sub-protocol that follows pre. -/
def treesOf {S Cl : Type} (bs pre : List (Block S Cl)) : Nat :=
  (((bs.flatMap fun b => b.rounds.zip b.oracles).take (pre.flatMap (·.rounds)).length).map
    (·.2.length)).sum

end OnBytes.SendSim.Seat

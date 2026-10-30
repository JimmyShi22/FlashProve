-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ChainEnd.lean: the last block of each of a proof file's three chains, as one text with
the chain's number, whether it is sealed, and the chain's own clauses as parameters.

This file holds definitions only; no theorem is stated. It stands on the format
(Johnson/Desc/Block.lean) and on the verifier program's record of a statement
(OnBytes/Iop/Ground.lean) alone.

What the block states.
  Rounds       where the chain is sealed (the first and the shared chain) one: the entry named
               "SEAL", all its numbers 0 (no work; no byte of a message; no root; no answer; nothing
               drawn; no claims counted). Where it is not (the second chain) none. Said here as
               data, not taken off a dry run.
  Reads        nothing.
  On the plan  the round in front of the end counts no claims (nothingOwedOnPlan).
  Decides      the chain's own named clauses on its carried record (asks), and nothing else.
  Claims       none, and no run behind a batching.
What an honest prover sends in the sealing round is not written here.

The three ends follow the last lines of the verifier program's three blocks
(OnBytes/Proof/Tail.lean: firstEnd, sharedBlock, secondBlock) and its runner's own end
(OnBytes/Iop/Ground.lean: Blk.runOn).
  The first chain    sealed. The program asks nothing of the statement there: groups of the first
                     chain are still open, for the second chain to test.
  The shared chain   sealed; nothing is left untested (untestedL).
  The second chain   not sealed; nothing is left untested.
  At all three       no count of claims is owed. The program asks it where it closes the sealing
                     round (Blk.close looks back: the entry of the round closed in front counts no
                     claims, or they have been compared) and again at its runner's end, of every
                     chain. Here it is asked in one of two ways, or both. (i) Where the chain's
                     record holds what is owed, a clause on that field is handed in among asks.
                     (ii) On the plan: the last of the rounds that the blocks in front declare
                     counts no claims. (ii) asks more than the program: it refuses a plan whose last
                     round in front counts claims, also if a block compares them.

What is assumed of the caller. inFront is the caller's: whoever lays the chain reads it off the very
blocks that it lays in front. Then the file's test of the blocks' rounds against the plan's ties it
to the plan. At an empty list the test on the plan is idle. Where a chain's record has no field for
what is owed, (ii) is the only way in which it is asked.

untestedL: a proximity test has begun on every group; every sampled oracle message is in a tested
group. So no claim that was laid on a group, and no sample, is left untested at the chain's end.
The second clause asks more than the program. Blk.requireAllTested (OnBytes/Iop/Ground.lean) asks
that a sampled message's list of groups is not empty; it does not ask that a number in that list is
a group's. Here one of them must be the number of a group that is there and whose test has begun.
Where the first clause holds, the two part only at a record in which a message names a group that is
not there; where it fails, the two clauses here can fail together.

What the program asks beside these at a chain's end is the format's in the blocks' form: the entry's
name and numbers (the file's test of the blocks' rounds against the plan's); that the round shows no
item and draws nothing (Block.step: "the rounds"); that a round is there (the fold: "the stretch is
short"); that no round and no column is left (chainAt). Block.step shows a block its round without
the sealed digest: what ties a seal to the later chain is not this block's.

What is not claimed. That a test written here is the program's: no theorem of this file ties the
two. That a test which has begun was carried through. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Desc.Block
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.ChainEnd
open OnBytes

/-- A test as a list of named clauses. -/
abbrev Clauses : Type := List (String × Bool)

/-- The first failing clause's name, as a refusal. A clause's name says what is asked, so the
refusal sets "not met: " in front of it. -/
def refuse (l : Clauses) : Except String Unit :=
  match l.find? (!·.2) with
  | some c => .error ("not met: " ++ c.1)
  | none => .ok ()

/-- Nothing is left untested, as two named clauses. -/
def untestedL (S : Statement) : Clauses :=
  [("end: a proximity test has begun on every group", S.groups.all (·.inRun)),
   ("end: every sampled message is in a tested group", S.oracles.all fun x =>
     !x.sampled || x.groups.any fun g => (S.groups[g]?).any (·.inRun))]

/-- The round in which a chain is sealed. -/
def sealRound : Fmt.DeclaredRound := ⟨{ name := "SEAL" }, [], []⟩

/-- On the plan: no count of claims is owed at the end: the last of the rounds that the blocks in
front declare counts no claims. True where there is no round in front. -/
def nothingOwedOnPlan (inFront : List Fmt.DeclaredRound) : Bool :=
  (inFront.getLast?).all (·.entry.rows == 0)

/-- **A chain's last block.** chain: the chain's number; piece: the block's number at the chain's
end; sealed: the chain has a sealing round; inFront: the rounds that the chain's blocks in front
declare; asks: the chain's own clauses on its carried record. -/
def chainEnd {S Cl : Type} (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → Clauses) : Block S Cl :=
  let rounds := if sealed then [sealRound] else []
  { name := "the end of chain " ++ toString chain, place := ⟨chain, none, piece, .frame⟩
    planOk := nothingOwedOnPlan inFront, rounds := rounds, oracles := rounds.map fun _ => []
    before := [], decide := fun s _ _ => (refuse (asks s)).map fun _ => s
    claims := [], after := [] }

end VerifiableInference.Desc.ChainEnd

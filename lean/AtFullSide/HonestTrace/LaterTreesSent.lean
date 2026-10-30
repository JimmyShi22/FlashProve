-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/LaterTreesSent.lean

Nothing on hiding. No property of the protocol is claimed. Public counts alone. At letters: no description, no prover, no
thread at a value.

THE HONEST OFFSETS, OFF THE DESCRIPTION ITSELF: a member's offset at its tree number j is THE NUMBER OF THE MEMBER's OWN ROUND THAT SENDS THAT TREE.
At these offsets the value "fixedByLots" (LaterTreesFixed.lean) IS THE LIBRARY's OWN VALUE OF
"fixed": the rounds in front of the chain plus the number of
the chain's round that sends the tree ("sentIn", Honest/Small/FixedSent.lean, whose "hand_fixed" proves the fourth clause of "Thread.fits" there, and
whose head says why the number is the sending round's and not one more). So no offset has to be named kind by kind, and the bound "OffsetsWithinRounds"
holds of every list, with no premise.

* "sendingOffsets bs": the offsets.
* "sendingOffsets_within": no offset exceeds its member's rounds. No premise.
* "sent_at_member": over a list whose members are "Listed": the chain's round that sends a member's tree number j is the rounds before the member plus
  the member's own round that sends it.
* "fixedByLots_is_front_plus_sending_round": at every tree that the list declares, "fixedByLots" at these offsets is front + sentIn.

By what. "sentIn_le", "sender_front", "sender_found", "treesTo_roots", "decls_split", "Listed" (Honest/Small/FixedSent.lean); "sender_behind"
(Honest/Small/SentFirst.lean: "trees_sent_first" there is the like at a member's first round); "declsTo_succ" (Honest/Thread/MadeLaw.lean); "tree_split"
(Honest/Thread/ScriptLots.lean).

Limits. Numbers only: that a tree's table changes no more after that many challenges is not shown. Beyond the list's last tree the two values differ
(FixedSent.lean says so at "sentIn_beyond"): the equation is stated below it alone. That a kind's own number (the proximity test's "seedRound") is this
offset at its member is not said here.
-/
import AtFullSide.HonestTrace.LaterTreesFixed
import Johnson.Desc.ProofFile.Honest.Small.SentFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun.LaterTrees
open VerifiableInference.Desc (Block sendRound)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Small (sentIn sentIn_le sender_front sender_found sender_behind treesTo_roots
  decls_split Listed rootsSum)

variable {S Cl : Type}

/-- **The honest offsets**: at member number b and its tree number j: the number, from 0, of the member's own round that sends the
tree; 0 where the list has no member b, or no round of the member sends such a tree. -/
def sendingOffsets (bs : List (Block S Cl)) : Nat → Nat → Nat :=
  fun b j => ((bs[b]?).map fun blk => sentIn blk.rounds j).getD 0

/-- At a member of the list. -/
theorem sendingOffsets_at {bs : List (Block S Cl)} {b : Nat} {blk : Block S Cl}
    (hblk : bs[b]? = some blk) (j : Nat) : sendingOffsets bs b j = sentIn blk.rounds j := by
  unfold sendingOffsets
  rw [hblk]
  rfl

/-- **No offset exceeds its member's number of rounds.** No premise. -/
theorem sendingOffsets_within (bs : List (Block S Cl)) :
    OffsetsWithinRounds bs (sendingOffsets bs) := by
  intro b blk hblk j _
  rw [sendingOffsets_at hblk]
  exact sentIn_le _ _

/-- A member that is "Listed" declares as many trees as its rounds count roots. -/
theorem member_trees_are_roots {blk : Block S Cl} (h : Listed blk) :
    (blk.oracles.flatMap id).length = rootsSum blk.rounds := by
  rw [List.length_flatMap]
  unfold rootsSum
  rw [h.2]
  rfl

/-- **The chain's round that sends a member's tree**: the rounds before the member, plus the member's own round that sends it. -/
theorem sent_at_member {bs : List (Block S Cl)} (listed : ∀ x ∈ bs, Listed x) {b j : Nat}
    {blk : Block S Cl} (hblk : bs[b]? = some blk) (hj : j < (blk.oracles.flatMap id).length) :
    sentIn (bs.flatMap (·.rounds)) (treesTo bs b + j) = roundsTo bs b + sentIn blk.rounds j := by
  have hj' : j < rootsSum blk.rounds := by
    rw [← member_trees_are_roots (listed blk (List.mem_of_getElem? hblk))]
    exact hj
  obtain ⟨i, hi⟩ := sender_found blk.rounds j hj'
  unfold sentIn
  rw [decls_split bs (b + 1), declsTo_succ hblk, List.append_assoc, treesTo_roots bs listed b,
    sender_behind, sender_front blk.rounds _ j hj', hi]
  show i + (declsTo bs b).length = roundsTo bs b + i
  unfold roundsTo
  exact Nat.add_comm _ _

/-- **At these offsets this value is the library's**, at every tree that the list declares. -/
theorem fixedByLots_is_front_plus_sending_round {bs : List (Block S Cl)}
    (listed : ∀ x ∈ bs, Listed x) (front : Nat) (atTaken : Nat → Nat → Nat) :
    ∀ t, t < treesTo bs bs.length →
      fixedByLots bs front (sendingOffsets bs) atTaken (.own t) =
        front + sentIn (bs.flatMap (·.rounds)) t := by
  intro t ht
  obtain ⟨b, j, blk, -, hblk, hj, rfl⟩ := tree_split bs bs.length (Nat.le_refl _) ht
  rw [fixedByLots_at_member hblk hj, sent_at_member listed hblk hj, sendingOffsets_at hblk]
  exact Nat.add_assoc _ _ _

end HonestTraceRun.LaterTrees

#print axioms HonestTraceRun.LaterTrees.sendingOffsets_within
#print axioms HonestTraceRun.LaterTrees.member_trees_are_roots
#print axioms HonestTraceRun.LaterTrees.sent_at_member
#print axioms HonestTraceRun.LaterTrees.fixedByLots_is_front_plus_sending_round

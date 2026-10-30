-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/LaterTreesFixed.lean

Nothing on hiding. No property of the protocol is claimed. Public counts alone. At letters: no
description, no prover, no thread at a value.

A PROPOSED VALUE FOR TWO LETTERS OF A LATER CHAIN's THREAD, "fixed" AND "taken" (Honest/Thread/Thr.lean), WITH THE LAWS THAT THEIR
USERS ASK. "fixed σ" says after how many challenges the table of the tree σ changes no more; "taken" lists the sources of the trees
that a chain takes over.

Why a value is needed. The test "Thread.fits" asks an upper bound: a tree that is available at a border is fixed by the challenges
heard there. At "fixed := fun _ => 0" that bound holds for nothing. The kinds' own form "OwnTrees" (Honest/Thread/ScriptLots.lean)
asks an equation: at a member's tree number j, "fixed" is the rounds in front of the chain, plus the rounds before the member, plus
the member's own offset at j. The value here is the one of "Script.ofLots" (the same file), with the offsets as a letter: it meets the
equation by its text and the bound where no offset exceeds its member's rounds.

* "fixedByLots": the value of "fixed": at an own tree by its sender's offset; at a taken source what the letter "atTaken" lays.
* "OffsetsWithinRounds": no offset exceeds its member's number of rounds. The form of a premise.
* "fixedByLots_at_member": the equation of "OwnTrees.fixed".
* "fixedByLots_own_le": the bound at an own tree.
* "fixedOfEarlierChains": the value of "atTaken": chain 0: the first chain's own number; any other: the first chain's rounds plus the
  shared chain's own number.
* "TakenAreDeclared": each taken source names chain 0 or 1 and a tree that this chain declares. The form of a premise.
* "fixedOfEarlierChains_le": the bound at a taken source, from the two earlier chains' own bounds.
* "takenSourcesOpened": the value of "taken": the sources declared as taken over that the chain's rounds open.
* "takenSourcesOpened_are_taken", "opened_taken_source_is_listed": what "Thread.fits" and "opensAvailable_second" ask of it.

Limits. Definitions and laws on lists and numbers. That any thread bears these values is said by nobody here. The offsets are a letter:
each sender says theirs. Nothing on what a table holds.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun.LaterTrees
open VerifiableInference.Desc (Block)
open ProofFile.Honest ProofFile.Honest.FirstThread

variable {S Cl S₁ Cl₁ S₂ Cl₂ : Type}

/-! ## 1 "fixed" -/

/-- **After how many challenges a tree's table changes no more, by lots.** bs: the chain's blocksInOrder list. front: the rounds in front of
the chain. offset b j: how many of its own challenges the table of member b's tree number j reads. atTaken c j: the number at the
source "tree j of chain c, taken over". -/
def fixedByLots (bs : List (Block S Cl)) (front : Nat) (offset : Nat → Nat → Nat)
    (atTaken : Nat → Nat → Nat) : Fmt.TreeSource → Nat
  | .own t =>
    front + roundsTo bs (senderOf bs t) + offset (senderOf bs t) (t - treesTo bs (senderOf bs t))
  | .taken c j => atTaken c j

/-- **No offset exceeds its member's number of rounds.** -/
def OffsetsWithinRounds (bs : List (Block S Cl)) (offset : Nat → Nat → Nat) : Prop :=
  ∀ b blk, bs[b]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
    offset b j ≤ blk.rounds.length

variable {bs : List (Block S Cl)} {front : Nat} {offset atTaken : Nat → Nat → Nat}

/-- **The equation that "OwnTrees.fixed" asks**, at a member's tree. -/
theorem fixedByLots_at_member {b j : Nat} {blk : Block S Cl} (hblk : bs[b]? = some blk)
    (hj : j < (blk.oracles.flatMap id).length) :
    fixedByLots bs front offset atTaken (.own (treesTo bs b + j)) =
      front + roundsTo bs b + offset b j := by
  show front + roundsTo bs (senderOf bs (treesTo bs b + j)) +
    offset (senderOf bs (treesTo bs b + j))
      (treesTo bs b + j - treesTo bs (senderOf bs (treesTo bs b + j))) = _
  rw [senderOf_own hblk hj, Nat.add_sub_cancel_left]

/-- **The bound at an own tree**: a tree that is declared before a border is fixed by the challenges before that border. -/
theorem fixedByLots_own_le (within : OffsetsWithinRounds bs offset) :
    ∀ b', b' ≤ bs.length → ∀ t, t < treesTo bs b' →
      fixedByLots bs front offset atTaken (.own t) ≤ front + roundsTo bs b' := by
  intro b' hb' t ht
  obtain ⟨b, j, blk, hb, hblk, hj, rfl⟩ := tree_split bs b' hb' ht
  rw [fixedByLots_at_member hblk hj]
  have h1 := within b blk hblk j hj
  have h2 := roundsTo_succ hblk
  have h3 := roundsTo_mono bs (b + 1) b' (by omega)
  omega

/-! ## 2 At the sources that are taken over -/

/-- **The number at a taken source, off the two earlier chains' own numbers.** The last chain hears the first chain's challenges, then
the shared chain's, then its own. -/
def fixedOfEarlierChains (fixedFirst fixedShared : Fmt.TreeSource → Nat) (roundsFirst : Nat) :
    Nat → Nat → Nat :=
  fun c j => if c = 0 then fixedFirst (.own j) else roundsFirst + fixedShared (.own j)

/-- **Each taken source names chain 0 or 1 and a tree that this chain declares.** -/
def TakenAreDeclared (taken : List Fmt.TreeSource) (first : List (Block S₁ Cl₁))
    (shared : List (Block S₂ Cl₂)) : Prop :=
  ∀ σ ∈ taken, (∃ j, σ = .taken 0 j ∧ j < treesTo first first.length) ∨
    ∃ j, σ = .taken 1 j ∧ j < treesTo shared shared.length

/-- **The bound at a taken source**: it is fixed by the challenges in front of the chain. -/
theorem fixedOfEarlierChains_le {taken : List Fmt.TreeSource} {first : List (Block S₁ Cl₁)}
    {shared : List (Block S₂ Cl₂)} {fixedFirst fixedShared : Fmt.TreeSource → Nat}
    (declared : TakenAreDeclared taken first shared)
    (boundFirst : ∀ j, j < treesTo first first.length →
      fixedFirst (.own j) ≤ roundsTo first first.length)
    (boundShared : ∀ j, j < treesTo shared shared.length →
      fixedShared (.own j) ≤ roundsTo shared shared.length) :
    ∀ σ ∈ taken, fixedByLots bs front offset
        (fixedOfEarlierChains fixedFirst fixedShared (roundsTo first first.length)) σ ≤
      roundsTo first first.length + roundsTo shared shared.length := by
  intro σ hσ
  rcases declared σ hσ with ⟨j, rfl, hj⟩ | ⟨j, rfl, hj⟩
  · show fixedOfEarlierChains fixedFirst fixedShared (roundsTo first first.length) 0 j ≤ _
    unfold fixedOfEarlierChains
    rw [if_pos rfl]
    exact Nat.le_trans (boundFirst j hj) (Nat.le_add_right _ _)
  · show fixedOfEarlierChains fixedFirst fixedShared (roundsTo first first.length) 1 j ≤ _
    unfold fixedOfEarlierChains
    rw [if_neg (by decide)]
    exact Nat.add_le_add_left (boundShared j hj) _

/-! ## 3 "taken" -/

/-- Is the source declared as taken over. -/
def isTakenSource : Fmt.TreeSource → Bool
  | .taken _ _ => true
  | .own _ => false

/-- **The sources declared as taken over that the chain's rounds open**, in the order of the rounds. A source that two rounds open
stands twice. -/
def takenSourcesOpened (bs : List (Block S Cl)) : List Fmt.TreeSource :=
  ((bs.flatMap (·.rounds)).flatMap fun d => d.opens.map (·.2)).filter isTakenSource

/-- **Each is declared as taken over**: what "Thread.fits" asks of the list. -/
theorem takenSourcesOpened_are_taken (bs : List (Block S Cl)) :
    ∀ σ ∈ takenSourcesOpened bs, ∃ c j, σ = Fmt.TreeSource.taken c j := by
  intro σ hσ
  have h := (List.mem_filter.1 hσ).2
  cases σ with
  | own t => cases h
  | taken c j => exact ⟨c, j, rfl⟩

/-- **Each taken source that a round opens is listed**: the premise htk of "opensAvailable_second". -/
theorem opened_taken_source_is_listed (bs : List (Block S Cl)) :
    ∀ d ∈ bs.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ c j, o.2 = Fmt.TreeSource.taken c j →
      o.2 ∈ takenSourcesOpened bs := by
  intro d hd o ho c j e
  refine List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨d, hd, List.mem_map.2 ⟨o, ho, rfl⟩⟩, ?_⟩
  rw [e]
  rfl

end HonestTraceRun.LaterTrees

#print axioms HonestTraceRun.LaterTrees.fixedByLots_at_member
#print axioms HonestTraceRun.LaterTrees.fixedByLots_own_le
#print axioms HonestTraceRun.LaterTrees.fixedOfEarlierChains_le
#print axioms HonestTraceRun.LaterTrees.takenSourcesOpened_are_taken
#print axioms HonestTraceRun.LaterTrees.opened_taken_source_is_listed

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/LaterTreesFixedAtLaterThreads.lean

Nothing on hiding. No property of the protocol is claimed. Public counts alone.

THE MATTER OF THE FIELDS "fix₂", "fix₃", "takenAre" OF THE THREADS' DEBTS (ThreadDebts, AtFullSide/Honest/ThreadsAtTheTerm.lean; not imported), AT
"sharedParts h later" AND AT "lastThread h first reads parts w" FOR ANY parts WHOSE "fixed" AND "taken" ARE THOSE OF "lastLetters"
(Honest/Thread/TheLaterThreads.lean, TheFirstThread.lean), WHERE THESE LETTERS BEAR THE VALUES OF LaterTreesFixed.lean. The debts' own thread at the
last chain, "threadThree", is "lastThread" at parts that differ from "lastParts h first lastLetters" in the field "ends" alone: so fix₃ in its own
letters is one call of "last_trees_fixed" (LaterTreesFixedAtTheTerm.lean).

* "shared_trees_fixed": fix₂, where later.fixed is "fixedByLots" at the shared chain's list, nothing in front.
* "last_taken_are_taken": takenAre, where lastLetters.taken is "takenSourcesOpened" of the last chain's list.
* "last_opened_taken_are_listed": the premise htk of "opensAvailable_second" at that value.
* "last_trees_fixed": fix₃, where lastLetters.fixed is "fixedByLots" at the last chain's list, the two earlier chains' rounds in front, and at the
  taken sources "fixedOfEarlierChains"; from fix₁ and fix₂.

Premises that stay. THE THREE EQUATIONS ON THE LETTERS:
no value of LaterLetters or LastLetters is laid here: whoever lays them lays them so, or
these laws say nothing of the value. "OffsetsWithinRounds" at each of the two chains: each sender's. "TakenAreDeclared": each taken source
that the last chain opens names chain 0 or 1 and a tree that this chain declares: a public fact on the description.

Limits. A head at a return is a letter. Counts only: nothing on what a tree holds.
-/
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads
import AtFullSide.HonestTrace.LaterTreesFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.LaterTrees
open ProofFile.Honest ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (later : LaterLetters A) (lastLetters : LastLetters A)

/-- **The field "fix₂".** -/
theorem shared_trees_fixed {offset atTaken : Nat → Nat → Nat}
    (fixedIs : later.fixed = fixedByLots h.description.shared.blocksInOrder 0 offset atTaken)
    (within : OffsetsWithinRounds h.description.shared.blocksInOrder offset) :
    ∀ b, b ≤ h.description.shared.blocksInOrder.length → ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      (sharedParts h later).fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b := by
  intro b hb j hj
  show later.fixed (.own j) ≤ _
  rw [fixedIs]
  have key := fixedByLots_own_le (front := 0) (atTaken := atTaken) within b hb j hj
  rw [Nat.zero_add] at key
  exact key

/-- **The field "takenAre".** -/
theorem last_taken_are_taken
    (takenIs : lastLetters.taken = takenSourcesOpened h.description.second.blocksInOrder) :
    ∀ σ ∈ (lastParts h first lastLetters).taken, ∃ c j, σ = Fmt.TreeSource.taken c j := by
  intro σ hσ
  have hσ' : σ ∈ lastLetters.taken := hσ
  rw [takenIs] at hσ'
  exact takenSourcesOpened_are_taken _ σ hσ'

/-- **The premise htk of "opensAvailable_second"**, at that value. -/
theorem last_opened_taken_are_listed
    (takenIs : lastLetters.taken = takenSourcesOpened h.description.second.blocksInOrder) :
    ∀ d ∈ h.description.second.blocksInOrder.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ c j,
      o.2 = Fmt.TreeSource.taken c j → o.2 ∈ (lastParts h first lastLetters).taken := by
  intro d hd o ho c j e
  show o.2 ∈ lastLetters.taken
  rw [takenIs]
  exact opened_taken_source_is_listed _ d hd o ho c j e

/-- **The matter of the field "fix₃"**, at the last chain's thread at any parts and any input. -/
theorem last_trees_fixed (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    {offset : Nat → Nat → Nat}
    (fixedIs : parts.fixed = fixedByLots h.description.second.blocksInOrder
      (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
        roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length) offset
      (fixedOfEarlierChains first.script.fixed later.fixed
        (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length)))
    (within : OffsetsWithinRounds h.description.second.blocksInOrder offset)
    (declared : TakenAreDeclared parts.taken h.description.first.blocksInOrder h.description.shared.blocksInOrder)
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b)
    (fixShared : ∀ b, b ≤ h.description.shared.blocksInOrder.length →
      ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      (sharedParts h later).fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b) :
    ∀ b, b ≤ h.description.second.blocksInOrder.length →
      ∀ σ ∈ (lastThread h first reads parts w).hand b,
      (lastThread h first reads parts w).fixed σ ≤
        (lastThread h first reads parts w).front + roundsTo (lastThread h first reads parts w).bs b := by
  intro b hb σ hσ
  have hσ' : σ ∈ parts.taken ++
      (List.range (treesTo h.description.second.blocksInOrder b)).map Fmt.TreeSource.own := hσ
  show parts.fixed σ ≤
    (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length ++
      declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).length +
      roundsTo h.description.second.blocksInOrder b
  rw [List.length_append, fixedIs]
  rcases List.mem_append.1 hσ' with ht | ho
  · exact Nat.le_trans
      (fixedOfEarlierChains_le declared (fun j hj => fixFirst _ (Nat.le_refl _) j hj)
        (fun j hj => fixShared _ (Nat.le_refl _) j hj) σ ht) (Nat.le_add_right _ _)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ho
    exact fixedByLots_own_le within b hb t (List.mem_range.1 ht)

end HonestTraceRun.LaterTrees

#print axioms HonestTraceRun.LaterTrees.shared_trees_fixed
#print axioms HonestTraceRun.LaterTrees.last_taken_are_taken
#print axioms HonestTraceRun.LaterTrees.last_opened_taken_are_listed
#print axioms HonestTraceRun.LaterTrees.last_trees_fixed

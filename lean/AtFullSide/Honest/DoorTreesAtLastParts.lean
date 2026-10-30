-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/DoorTreesAtLastParts.lean: THE TREES THAT THE LAST CHAIN TAKES OVER ARE AT HAND AT
THE DOOR: at a run's three threads (AtFullSide/Honest/TheThreeThreads.lean), where the last thread's
parts are `lastParts` (Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean) at letters L whose
three fields on trees are the terms of Johnson/Desc/ProofFile/Honest/K12/AtFile/LastTerm.lean:
wherever the first and the shared thread's invariants hold at their chains' ends, each tree that the
last thread takes over is available at the stand with which that thread begins, from the sender and
with the table that the thread names. Statements with their proofs; no definition.

Main names.
  `first_trees_to_end`, `shared_trees_to_end`: under the head the first chain's sub-protocols state
    83 trees, the shared chain's 11.
  `door_trees_at_lastThread`: **the statement, at the last thread (`lastThread`) at any parts whose
    three fields on trees are these terms.** The library's `trees_taken_of`
    (Johnson/Desc/ProofFile/Honest/Thread/Door.lean) at `taken_at_door` (LastTerm.lean), with that
    law's premises on the run paid from the two invariants, `ready`'s return and the head.
  `door_trees_at_lastParts`: the same in the letters in which the threads' debts at a run are
    gathered: at `lastParts`.

The premises. hR: `ready` returns. ht, htb, hfx: L's list of taken trees, its tables and its counts
are `takenLast`, `lastTable` and `lastFixed` over the two earlier threads' own tables and counts;
own, ownF: these terms' letters for the last chain's own trees, of which nothing is read here. fix₁:
each tree of the first chain is fixed by the challenges heard when it is available.

Limits. NOT IN FRONT OF A LAW OVER COINS: the statement speaks of one run's stands. NO VALUE OF L IS
SHOWN HERE: where the structure of the letters holds a proof that the tables have the declared
depths, letters with these three fields exist only if the two earlier threads' tables have these
depths at all coins, inputs and challenges; were that false, the statement would speak of nothing.
Conditional on the two invariants at their chains' ends, which hold that the earlier chains' own
trees are at hand; that they hold at any run is not shown here. The full size, and the hash function
`OnBytes.secondHashFunction`, alone.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.Honest.TheThreeThreads
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LastTerm
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest
open OnBytes
open ProofFile ProofFile.Honest ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Place)
open ProofFile.Honest.K12.AtFile (lastTable lastFixed takenLast taken_at_door)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- Under the head the first chain's sub-protocols state 83 trees. -/
theorem first_trees_to_end (h : HeadAtReturn files A) :
    treesTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length = 83 := by
  unfold treesTo
  rw [List.take_length]
  exact h.head.toAtMg.first_told

/-- Under the head the shared chain's sub-protocols state 11 trees. -/
theorem shared_trees_to_end (h : HeadAtReturn files A) :
    treesTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length = 11 := by
  unfold treesTo
  rw [List.take_length]
  exact (_root_.Desc.K14.Law.Fence.counts_of_planOk h.description "proof file" _
    h.head.laid.planOk h.head.laid.data).2.trans h.head.toAtMg.trees.2

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- hR, ht, htb, hfx and fix₁ are premises. **The trees that the last chain takes over are at hand
at the stand with which its thread begins**, at the last thread at any parts with these three
fields. -/
theorem door_trees_at_lastThread (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ IndexCommitterCoins) {Wt : Type} (shared : SharedThreadParts A Wt)
    (last : LastThreadParts A) (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (own : ℕ → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn → Place × Table)
    (ownF : ℕ → ℕ) (ht : last.taken = takenLast)
    (htb : last.table = lastTable
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
      (fun w => ⟨w.w₀, w.rc, A.H.key w.x⟩) (threadOne h first R).table
      (threadTwo h reads shared R).table own)
    (hfx : last.fixed = lastFixed
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
      (threadOne h first R).fixed (threadTwo h reads shared R).fixed ownF)
    (fix₁ : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      (lastThread h first reads last R.own).Trees
        (lastThread h first reads last R.own).taken k (R.start₃ A.H m₁ m₂)
        (envThird E₁ E₂) := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂
  obtain ⟨-, tr, -, hown, hcom, -, -, -⟩ := ready_ok hR
  have ec : R.common = ⟨R.own.w₀, R.own.rc, A.H.key R.own.x⟩ := by rw [hcom, hown]
  have hi₁ : m₁.st.input = R.own := by
    have t := u₁.1
    unfold Thr at t
    exact t.2.2.2.2.2.2.1
  have hi₂ : m₂.st.input = ⟨R.own.w₀, R.own.rc, A.H.key R.own.x⟩ := by
    have t := u₂.1
    unfold Thr at t
    exact (t.2.2.2.2.2.2.1 : m₂.st.input = R.common).trans ec
  have e83 := first_trees_to_end h
  have e11 := shared_trees_to_end h
  have hin₂ : 1 < treesTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length := by
    rw [e11]
    decide
  have hin₁ : ∀ j, j = 1 ∨ j = 82 →
      j < treesTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length := by
    intro j hj
    rw [e83]
    rcases hj with rfl | rfl <;> decide
  have ht' : (lastThread h first reads last R.own).taken = takenLast := ht
  have htb' : (lastThread h first reads last R.own).table = lastTable
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
      (fun w => ⟨w.w₀, w.rc, A.H.key w.x⟩) (threadOne h first R).table
      (threadTwo h reads shared R).table own := htb
  have hfx' : (lastThread h first reads last R.own).fixed = lastFixed
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
      (threadOne h first R).fixed (threadTwo h reads shared R).fixed ownF := hfx
  have hl : m₁.st.heard.length =
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length :=
    drawsFit_length _ _ u₁.1.2.1
  have hf : ∀ j, j = 1 ∨ j = 82 → (threadOne h first R).fixed (.own j) ≤
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length :=
    fun j hj => fix₁ _ (Nat.le_refl _) j (hin₁ j hj)
  have hh₁ : ∀ j, j = 1 ∨ j = 82 → Fmt.TreeSource.own j ∈
      (threadOne h first R).hand h.description.first.blocksInOrder.length :=
    fun j hj => List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 (hin₁ j hj), rfl⟩)
  have hh₂ : Fmt.TreeSource.own 1 ∈
      (threadTwo h reads shared R).hand h.description.shared.blocksInOrder.length :=
    List.mem_append_right _ (List.mem_map.2 ⟨1, List.mem_range.2 hin₂, rfl⟩)
  have tk := taken_at_door (F := h.description) (H := A.H) (R := R) (k := k)
    (T₁ := threadOne h first R) (T₂ := threadTwo h reads shared R)
    (T₃ := lastThread h first reads last R.own)
    (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
    h.description.first.blocksInOrder.length h.description.shared.blocksInOrder.length
    (fun w => ⟨w.w₀, w.rc, A.H.key w.x⟩) own ownF ht' htb' hfx' m₁ m₂ hi₁ hi₂ hl hf hh₁ hh₂
  exact trees_taken_of (F := h.description) (H := A.H) (R := R) (k := k)
    (T₁ := threadOne h first R) (T₂ := threadTwo h reads shared R)
    (T₃ := lastThread h first reads last R.own) u₁.1 u₂.1 tk

/-- The premises are those of `door_trees_at_lastThread`, on the letters L. **The same in the
letters in which the threads' debts at a run are gathered**: at `lastParts`. -/
theorem door_trees_at_lastParts (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ IndexCommitterCoins) {Wt : Type} (shared : SharedThreadParts A Wt)
    (L : LastLetters A) (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (own : ℕ → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn → Place × Table)
    (ownF : ℕ → ℕ) (ht : L.taken = takenLast)
    (htb : L.table = lastTable
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
      (fun w => ⟨w.w₀, w.rc, A.H.key w.x⟩) (threadOne h first R).table
      (threadTwo h reads shared R).table own)
    (hfx : L.fixed = lastFixed
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
      (threadOne h first R).fixed (threadTwo h reads shared R).fixed ownF)
    (fix₁ : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      (threadThree h first reads (lastParts h first L) R).Trees
        (threadThree h first reads (lastParts h first L) R).taken
        k (R.start₃ A.H m₁ m₂) (envThird E₁ E₂) :=
  door_trees_at_lastThread h first reads shared
    (lastParts h first L) R hR own ownF ht htb hfx fix₁

end AtFullSide.Honest

#print axioms AtFullSide.Honest.first_trees_to_end
#print axioms AtFullSide.Honest.shared_trees_to_end
#print axioms AtFullSide.Honest.door_trees_at_lastThread
#print axioms AtFullSide.Honest.door_trees_at_lastParts

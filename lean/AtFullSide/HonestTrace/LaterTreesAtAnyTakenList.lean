-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/LaterTreesAtAnyTakenList.lean

Nothing on hiding. No property of the protocol is claimed. Public counts alone.

THE FIELDS "fix₂", "fix₃", "takenAre" OF THE THREADS' DEBTS (ThreadFieldsP, AtFullSide/Honest/ThreadsAtTheTerm.lean; not imported), IN THEIR OWN LETTERS, AT ANY LIST OF TAKEN SOURCES THAT IS
"TakenAreDeclared" (LaterTreesFixed.lean); AND AT THE TERMS THAT OTHER FILES HOLD FOR THE LAST CHAIN's FIELDS ON TREES: "lastFixed"
(Honest/K12/AtFile/LastTerm.lean) and "takenLast" (Honest/K12/AtFile/OpensLines.lean: the written list of three sources).

Why. "later_fields_at_sending_rounds" (LaterTreesSentAtTheTerm.lean) asks that the letter "taken" IS "takenSourcesOpened" of the last chain's list. "takenLast" is
another term. Here the list is a letter.

* "later_fields_at_any_taken_list": fix₂ ∧ fix₃ ∧ takenAre from four sentences on "fixed", each asked only where it is read, "TakenAreDeclared" at the letter
  "taken", and fix₁. takenAre follows from "TakenAreDeclared".
* "trees_by_cut", "treesTo_whole": how many trees a list declares, off its cut into rows.
* "written_trees_first", "written_trees_shared": BY LEAN's KERNEL: the written cuts tell 83 and 11 trees; each with a control.
* "takenLast_declared": under the head "takenLast" is "TakenAreDeclared".
* "later_fields_at_written_taken_list": the three fields where lastLetters.fixed is "lastFixed" over the first Script's and the shared letters' own numbers, and
  lastLetters.taken is "takenLast".

By what. As LaterTreesSentAtTheTerm.lean; "toldOf_cut" (Johnson/Desc/First/CutAtNumbers.lean); "cuts_of_laid" (Johnson/Goal/Skeleton/CutIsOfLaid.lean). The way of
"trees_by_cut" is that of "treesLens_at_head" (Honest/K12/OffAt354.lean).

PREMISES THAT STAY at the last. That later.fixed at each tree of the shared chain, and "lastFixed"'s letter "own" at each tree of the last chain, count up to the
sending round. K12's files lay own τ := n₀ + seedRound stages τ; their closed lines "sent_last", "seed_W" (Honest/K12/AtFile/TableLines.lean) say at the written
rounds that these are the sending rounds; the step from the written rounds to the head's description is not made here. fix₁.

Limits. That the values of LaterLetters and LastLetters laid over named holes ("OpenShared", "OpenLast") in AtFullSide/Honest/TheLettersShared.lean
("later") and TheLettersLast.lean ("last") meet the sentences asked here is not shown here. "Thread.fits" and these fields are tests on numbers: nothing on what a table holds.
That the ends are the text of the fields in AtFullSide/Honest/ThreadsAtTheTerm.lean, at shared :=
sharedParts h later and last := lastParts h first lastLetters, is not guarded by Lean here: this
file does not import that file.
-/
import AtFullSide.HonestTrace.LaterTreesSentAtTheTerm
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LastTerm
import Johnson.Desc.First.CutAtNumbers
import Johnson.Goal.Skeleton.CutIsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.LaterTrees
open VerifiableInference.Desc (Block)
open VerifiableInference.PlanWritten (cutOf cutFirstFull cutSharedFull)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Small (sentIn sentIn_front treesTo_roots treesTo_le_all decls_split lists_of_shaped
  hand_fixed_below)
open ProofFile.Honest.K12.AtFile (lastFixed takenLast)
open AtFullSide.Honest (threadThree)

/-! ## 1 How many trees a list declares, off its cut -/

section
variable {S Cl : Type}

/-- How many trees each sub-protocol declares is the length of what its row of the cut tells. -/
theorem trees_by_cut (bs : List (Block S Cl)) :
    bs.map (fun b => (b.oracles.flatMap id).length) =
      (cutOf bs).map fun r => (r.2.2.2.2.1.flatMap (·.2)).length := by
  have e := VerifiableInference.Desc.First.toldOf_cut bs
  have e' := congrArg (List.map List.length) e
  unfold VerifiableInference.Desc.First.toldOf at e'
  rw [List.map_map, List.map_map] at e'
  rw [show (fun b : Block S Cl => (b.oracles.flatMap id).length) =
    List.length ∘ fun b => b.oracles.flatten from funext fun b => by
      show (b.oracles.flatMap id).length = b.oracles.flatten.length
      rw [List.flatMap_id]]
  exact e'

/-- The trees of the whole list. -/
theorem treesTo_whole (bs : List (Block S Cl)) :
    treesTo bs bs.length = ((cutOf bs).map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).sum := by
  unfold treesTo
  rw [List.take_length, List.length_flatMap, trees_by_cut]

end

set_option maxRecDepth 1000000 in
/-- By the kernel: the first chain's written cut tells 83 trees. The second clause is a control: without its last two rows, 82. -/
theorem written_trees_first :
    (cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).sum = 83 ∧
      ((cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).take 356).sum = 82 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: the shared chain's written cut tells 11 trees. The second clause is a control: its first two rows tell none. -/
theorem written_trees_shared :
    (cutSharedFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).sum = 11 ∧
      ((cutSharedFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).take 2).sum = 0 := by
  decide +kernel

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  (later : LaterLetters A) (lastLetters : LastLetters A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

/-! ## 2 At any list -/

/-- **The three fields, at any list of taken sources that is declared.** -/
theorem later_fields_at_any_taken_list
    (sharedFixedIs : ∀ j, j < treesTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length →
      later.fixed (.own j) = sentIn (h.description.shared.blocksInOrder.flatMap (·.rounds)) j)
    (lastFixedIs : ∀ j, j < treesTo h.description.second.blocksInOrder h.description.second.blocksInOrder.length →
      lastLetters.fixed (.own j) =
        roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
          roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length +
          sentIn (h.description.second.blocksInOrder.flatMap (·.rounds)) j)
    (takenFromFirstIs : ∀ j, lastLetters.fixed (.taken 0 j) = first.script.fixed (.own j))
    (takenFromSharedIs : ∀ j, lastLetters.fixed (.taken 1 j) =
      roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length + later.fixed (.own j))
    (declared : TakenAreDeclared lastLetters.taken h.description.first.blocksInOrder
      h.description.shared.blocksInOrder)
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    (∀ b, b ≤ h.description.shared.blocksInOrder.length → ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      (sharedParts h later).fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b) ∧
    (∀ b, b ≤ h.description.second.blocksInOrder.length →
      ∀ σ ∈ (threadThree h first reads (lastParts h first lastLetters) R).hand b,
      (threadThree h first reads (lastParts h first lastLetters) R).fixed σ ≤
        (threadThree h first reads (lastParts h first lastLetters) R).front +
          roundsTo
            (threadThree h first reads (lastParts h first lastLetters) R).bs b) ∧
    ∀ σ ∈ (lastParts h first lastLetters).taken, ∃ c j, σ = Fmt.TreeSource.taken c j := by
  obtain ⟨-, s2, s3⟩ := planOk_all (head_planOk h.head)
  have fixShared : ∀ b, b ≤ h.description.shared.blocksInOrder.length →
      ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      later.fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b := by
    intro b _ j hj
    rw [sharedFixedIs j (Nat.lt_of_lt_of_le hj (treesTo_le_all _ b)),
      decls_split h.description.shared.blocksInOrder b]
    refine sentIn_front _ _ j ?_
    rw [← treesTo_roots h.description.shared.blocksInOrder (fun x hx => lists_of_shaped (s2 x hx).2) b]
    exact hj
  have front : (threadThree h first reads (lastParts h first lastLetters) R).front =
      roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
        roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length := by
    show (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length ++
      declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).length = _
    rw [List.length_append]
    rfl
  refine ⟨fixShared, fun b _ => hand_fixed_below _ (fun x hx => lists_of_shaped (s3 x hx).2) ?_ ?_ b,
    ?_⟩
  · intro σ hσ
    refine le_of_le_of_eq ?_ front.symm
    show lastLetters.fixed σ ≤ _
    rcases declared σ hσ with ⟨j, rfl, hj⟩ | ⟨j, rfl, hj⟩
    · rw [takenFromFirstIs]
      exact Nat.le_trans (fixFirst _ (Nat.le_refl _) j hj) (Nat.le_add_right _ _)
    · rw [takenFromSharedIs]
      exact Nat.add_le_add_left (fixShared _ (Nat.le_refl _) j hj) _
  · intro j hj
    exact (lastFixedIs j hj).trans
      (congrArg (· + sentIn (h.description.second.blocksInOrder.flatMap (·.rounds)) j) front.symm)
  · intro σ hσ
    rcases declared σ hσ with ⟨j, rfl, -⟩ | ⟨j, rfl, -⟩
    · exact ⟨0, j, rfl⟩
    · exact ⟨1, j, rfl⟩

/-! ## 3 At the other files' terms -/

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **Under the head the written list of three sources is declared.** -/
theorem takenLast_declared :
    TakenAreDeclared takenLast h.description.first.blocksInOrder h.description.shared.blocksInOrder := by
  obtain ⟨c1, c2, -⟩ := P5J.cuts_of_laid h.head.toAtMg.scope h.head.toAtMg.laid
  have t1 : treesTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length = 83 := by
    rw [treesTo_whole, c1]
    exact written_trees_first.1
  have t2 : treesTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length = 11 := by
    rw [treesTo_whole, c2]
    exact written_trees_shared.1
  have e : takenLast = [.taken 0 1, .taken 0 82, .taken 1 1] := by decide
  intro σ hσ
  rw [e] at hσ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl
  · exact .inl ⟨1, rfl, by rw [t1]; decide⟩
  · exact .inl ⟨82, rfl, by rw [t1]; decide⟩
  · exact .inr ⟨1, rfl, by rw [t2]; decide⟩

/-- **The three fields at "lastFixed" and "takenLast".** own: the letter of "lastFixed" at the last chain's own trees. -/
theorem later_fields_at_written_taken_list {own : Nat → Nat}
    (sharedFixedIs : ∀ j, j < treesTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length →
      later.fixed (.own j) = sentIn (h.description.shared.blocksInOrder.flatMap (·.rounds)) j)
    (fixedIs : lastLetters.fixed =
      lastFixed (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length)
        first.script.fixed later.fixed own)
    (ownIs : ∀ j, j < treesTo h.description.second.blocksInOrder h.description.second.blocksInOrder.length →
      own j = roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
        roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length +
        sentIn (h.description.second.blocksInOrder.flatMap (·.rounds)) j)
    (takenIs : lastLetters.taken = takenLast)
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    (∀ b, b ≤ h.description.shared.blocksInOrder.length → ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      (sharedParts h later).fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b) ∧
    (∀ b, b ≤ h.description.second.blocksInOrder.length →
      ∀ σ ∈ (threadThree h first reads (lastParts h first lastLetters) R).hand b,
      (threadThree h first reads (lastParts h first lastLetters) R).fixed σ ≤
        (threadThree h first reads (lastParts h first lastLetters) R).front +
          roundsTo
            (threadThree h first reads (lastParts h first lastLetters) R).bs b) ∧
    ∀ σ ∈ (lastParts h first lastLetters).taken, ∃ c j, σ = Fmt.TreeSource.taken c j :=
  later_fields_at_any_taken_list h first reads later lastLetters R sharedFixedIs
    (fun j hj => by rw [fixedIs]; exact ownIs j hj) (fun j => by rw [fixedIs]; rfl)
    (fun j => by rw [fixedIs]; rfl) (by rw [takenIs]; exact takenLast_declared h) fixFirst

end HonestTraceRun.LaterTrees

#print axioms HonestTraceRun.LaterTrees.trees_by_cut
#print axioms HonestTraceRun.LaterTrees.treesTo_whole
#print axioms HonestTraceRun.LaterTrees.written_trees_first
#print axioms HonestTraceRun.LaterTrees.written_trees_shared
#print axioms HonestTraceRun.LaterTrees.later_fields_at_any_taken_list
#print axioms HonestTraceRun.LaterTrees.takenLast_declared
#print axioms HonestTraceRun.LaterTrees.later_fields_at_written_taken_list

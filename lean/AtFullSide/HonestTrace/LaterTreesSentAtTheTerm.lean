-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/LaterTreesSentAtTheTerm.lean

Nothing on hiding. No property of the protocol is claimed. Public counts alone.

THE FIELDS "fix₂", "fix₃", "takenAre" OF THE THREADS' DEBTS (ThreadFieldsP, AtFullSide/Honest/ThreadsAtTheTerm.lean; not imported), IN THEIR OWN LETTERS, WHERE "fixed" COUNTS
THE CHALLENGES UP TO THE ROUND THAT SENDS THE TREE: the library's own value (Honest/Small/FixedSent.lean). No premise on offsets is left.

* "later_fields_at_sending_rounds": fix₂ ∧ fix₃ ∧ takenAre, from FIVE SENTENCES ON THE LETTERS, each asked only where it is read, and fix₁:
    at each tree that the shared chain declares, later.fixed is the number of the shared chain's round that sends it ·
    at each tree that the last chain declares, lastLetters.fixed is the two earlier chains' rounds plus the number of the last chain's sending round ·
    at a tree taken over from chain 0, lastLetters.fixed is the first Script's own number · from chain 1: the first chain's rounds plus later.fixed ·
    lastLetters.taken is "takenSourcesOpened" of the last chain's list.
* "later_threads_fit_at_sending_rounds": so both later threads pass "Thread.fits".
* "later_threads_fit_at_letters_laid_by_sending_rounds": the same at "laterLettersFixedByLots", "lastLettersFixedByLots" (LaterTreesFixedLetters.lean) at
  the offsets "sendingOffsets": THE HEAD AT THE RETURN AND fix₁ ARE THE ONLY PREMISES.

By what. "sentIn_front", "treesTo_roots", "treesTo_le_all", "decls_split", "lists_of_shaped", "hand_fixed_below" (Honest/Small/FixedSent.lean); "planOk_all"
(Honest/Thread/File.lean); "head_planOk" (Honest/Thread/FirstSits.lean); "taken_opened_are_declared" (LaterTreesFixedDeclared.lean);
"fits_sharedThread", "fits_lastThread" (Honest/Thread/FitsAtTerm.lean); "sendingOffsets_within" (LaterTreesSent.lean).

WHAT IS NOT SHOWN HERE. The five sentences say how "fixed" and "taken" have to be laid. That the values laid over named holes ("OpenShared", "OpenLast") in
AtFullSide/Honest/TheLettersShared.lean ("later") and TheLettersLast.lean ("last") meet them is not shown here. THAT THE
TABLES LAID IN THE LETTER "table" CHANGE NO MORE AFTER THAT MANY CHALLENGES, and that a kind's own number at its member (the proximity test's "seedRound")
is the sending round's, is said by nobody here: "Thread.fits" is a test on numbers.
That the ends are the text of the fields in AtFullSide/Honest/ThreadsAtTheTerm.lean, at shared :=
sharedParts h later and last := lastParts h first lastLetters, is not guarded by Lean here: this
file does not import that file.
-/
import AtFullSide.HonestTrace.LaterTreesFixedLetters
import AtFullSide.HonestTrace.LaterTreesSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.LaterTrees
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Small (sentIn sentIn_front treesTo_roots treesTo_le_all decls_split lists_of_shaped
  hand_fixed_below)
open AtFullSide.Honest (threadTwo threadThree)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  (later : LaterLetters A) (lastLetters : LastLetters A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

/-- **The three fields, where "fixed" counts up to the sending round.** -/
theorem later_fields_at_sending_rounds
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
    (takenIs : lastLetters.taken = takenSourcesOpened h.description.second.blocksInOrder)
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
  have declared : TakenAreDeclared lastLetters.taken h.description.first.blocksInOrder
      h.description.shared.blocksInOrder := by
    rw [takenIs]
    exact taken_opened_are_declared (head_planOk h.head)
  have front : (threadThree h first reads (lastParts h first lastLetters) R).front =
      roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
        roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length := by
    show (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length ++
      declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).length = _
    rw [List.length_append]
    rfl
  refine ⟨fixShared, fun b _ => hand_fixed_below _ (fun x hx => lists_of_shaped (s3 x hx).2) ?_ ?_ b,
    last_taken_are_taken h first lastLetters takenIs⟩
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

/-- **So both later threads pass the test "fits".** -/
theorem later_threads_fit_at_sending_rounds
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
    (takenIs : lastLetters.taken = takenSourcesOpened h.description.second.blocksInOrder)
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    (threadTwo h reads (sharedParts h later) R).fits h.description.shared.blocksInOrder.length = true ∧
      (threadThree h first reads (lastParts h first lastLetters) R).fits
        h.description.second.blocksInOrder.length = true := by
  obtain ⟨f2, f3, tk⟩ := later_fields_at_sending_rounds h first reads later lastLetters R
    sharedFixedIs lastFixedIs takenFromFirstIs takenFromSharedIs takenIs fixFirst
  exact ⟨fits_sharedThread h reads (sharedParts h later) R.common f2,
    fits_lastThread h first reads _ R.own tk f3⟩

/-- **At the letters laid by the sending rounds: the head at the return and fix₁ are the only premises.** -/
theorem later_threads_fit_at_letters_laid_by_sending_rounds
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    (threadTwo h reads (sharedParts h (laterLettersFixedByLots later h
        (sendingOffsets h.description.shared.blocksInOrder))) R).fits
        h.description.shared.blocksInOrder.length = true ∧
      (threadThree h first reads
        (lastParts h first (lastLettersFixedByLots lastLetters h first
          (laterLettersFixedByLots later h (sendingOffsets h.description.shared.blocksInOrder))
          (sendingOffsets h.description.second.blocksInOrder))) R).fits
        h.description.second.blocksInOrder.length = true :=
  later_threads_fit_at_laid_letters h first reads later lastLetters R
    (sendingOffsets_within _) (sendingOffsets_within _) fixFirst

end HonestTraceRun.LaterTrees

#print axioms HonestTraceRun.LaterTrees.later_fields_at_sending_rounds
#print axioms HonestTraceRun.LaterTrees.later_threads_fit_at_sending_rounds
#print axioms HonestTraceRun.LaterTrees.later_threads_fit_at_letters_laid_by_sending_rounds

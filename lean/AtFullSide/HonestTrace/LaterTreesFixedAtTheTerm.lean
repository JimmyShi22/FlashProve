-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/LaterTreesFixedAtTheTerm.lean

Nothing on hiding. No property of the protocol is claimed. Public counts alone.

THE FIELD "fix₃" OF THE THREADS' DEBTS (ThreadFieldsP, AtFullSide/Honest/ThreadsAtTheTerm.lean; not imported) IN ITS OWN LETTERS, at "threadThree h
first reads (lastParts h first lastLetters) R": one call of "last_trees_fixed" (LaterTreesFixedAtLaterThreads.lean), whose premises and
limits stand. The fields "fix₂" and "takenAre" stand in their own letters there already ("shared_trees_fixed", "last_taken_are_taken").

* "last_trees_fixed_at_the_run": fix₃.
* "later_fields_at_the_proposed_values": fix₂, fix₃ AND takenAre TOGETHER, from: the three equations on the letters "later.fixed", "lastLetters.fixed",
  "lastLetters.taken" · "OffsetsWithinRounds" at the shared and at the last chain · fix₁. "TakenAreDeclared" is paid here, by the head's "planOk"
  ("taken_opened_are_declared", LaterTreesFixedDeclared.lean).

* "later_threads_fit": SO THE TEST "Thread.fits" SAYS YES AT THE SHARED AND AT THE LAST CHAIN's THREAD AT THE RUN: the three fields handed to their own
  spenders "fits_sharedThread", "fits_lastThread" (Honest/Thread/FitsAtTerm.lean), as ThreadsAtTheTerm.lean's "fitsTwo", "fitsThree" hand them.

WHAT IS NOT SHOWN HERE.
The three equations say how "fixed" and "taken" have to be laid for these laws to speak of a value of LaterLetters or LastLetters.
That the values laid over named holes ("OpenShared", "OpenLast") in AtFullSide/Honest/TheLettersShared.lean ("later") and TheLettersLast.lean ("last")
meet them is not shown here. The two bounds on the offsets are each sender's.
That the ends are the text of the fields in AtFullSide/Honest/ThreadsAtTheTerm.lean, at shared :=
sharedParts h later and last := lastParts h first lastLetters, is not guarded by Lean here: this
file does not import that file.
-/
import AtFullSide.Honest.TheThreeThreads
import AtFullSide.HonestTrace.LaterTreesFixedAtLaterThreads
import AtFullSide.HonestTrace.LaterTreesFixedDeclared
import Johnson.Desc.ProofFile.Honest.Thread.FirstSits
import Johnson.Desc.ProofFile.Honest.Thread.FitsAtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.LaterTrees
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest (threadTwo threadThree)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  (later : LaterLetters A) (lastLetters : LastLetters A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

/-- **The field "fix₃".** -/
theorem last_trees_fixed_at_the_run {offset : Nat → Nat → Nat}
    (fixedIs : lastLetters.fixed = fixedByLots h.description.second.blocksInOrder
      (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
        roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length) offset
      (fixedOfEarlierChains first.script.fixed later.fixed
        (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length)))
    (within : OffsetsWithinRounds h.description.second.blocksInOrder offset)
    (declared : TakenAreDeclared lastLetters.taken h.description.first.blocksInOrder
      h.description.shared.blocksInOrder)
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b)
    (fixShared : ∀ b, b ≤ h.description.shared.blocksInOrder.length →
      ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      (sharedParts h later).fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b) :
    ∀ b, b ≤ h.description.second.blocksInOrder.length →
      ∀ σ ∈ (threadThree h first reads (lastParts h first lastLetters) R).hand b,
      (threadThree h first reads (lastParts h first lastLetters) R).fixed σ ≤
        (threadThree h first reads (lastParts h first lastLetters) R).front +
          roundsTo
            (threadThree h first reads (lastParts h first lastLetters) R).bs b :=
  last_trees_fixed h first reads later
    (lastParts h first lastLetters) R.own fixedIs
    within declared fixFirst fixShared

/-- **The three fields together, at the proposed values of the letters.** -/
theorem later_fields_at_the_proposed_values {offsetShared offsetLast atTaken : Nat → Nat → Nat}
    (sharedFixedIs : later.fixed = fixedByLots h.description.shared.blocksInOrder 0 offsetShared atTaken)
    (lastFixedIs : lastLetters.fixed = fixedByLots h.description.second.blocksInOrder
      (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
        roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length) offsetLast
      (fixedOfEarlierChains first.script.fixed later.fixed
        (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length)))
    (takenIs : lastLetters.taken = takenSourcesOpened h.description.second.blocksInOrder)
    (withinShared : OffsetsWithinRounds h.description.shared.blocksInOrder offsetShared)
    (withinLast : OffsetsWithinRounds h.description.second.blocksInOrder offsetLast)
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
  have fixShared := shared_trees_fixed h later sharedFixedIs withinShared
  have declared : TakenAreDeclared lastLetters.taken h.description.first.blocksInOrder
      h.description.shared.blocksInOrder := by
    rw [takenIs]
    exact taken_opened_are_declared (head_planOk h.head)
  exact ⟨fixShared,
    last_trees_fixed_at_the_run h first reads later lastLetters R lastFixedIs withinLast declared
      fixFirst fixShared,
    last_taken_are_taken h first lastLetters takenIs⟩

/-- **So both later threads pass the test "fits"**, at the proposed values of the letters. -/
theorem later_threads_fit {offsetShared offsetLast atTaken : Nat → Nat → Nat}
    (sharedFixedIs : later.fixed = fixedByLots h.description.shared.blocksInOrder 0 offsetShared atTaken)
    (lastFixedIs : lastLetters.fixed = fixedByLots h.description.second.blocksInOrder
      (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
        roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length) offsetLast
      (fixedOfEarlierChains first.script.fixed later.fixed
        (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length)))
    (takenIs : lastLetters.taken = takenSourcesOpened h.description.second.blocksInOrder)
    (withinShared : OffsetsWithinRounds h.description.shared.blocksInOrder offsetShared)
    (withinLast : OffsetsWithinRounds h.description.second.blocksInOrder offsetLast)
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    (threadTwo h reads (sharedParts h later) R).fits h.description.shared.blocksInOrder.length = true ∧
      (threadThree h first reads (lastParts h first lastLetters) R).fits
        h.description.second.blocksInOrder.length = true := by
  obtain ⟨f2, f3, tk⟩ := later_fields_at_the_proposed_values h first reads later lastLetters R
    sharedFixedIs lastFixedIs takenIs withinShared withinLast fixFirst
  exact ⟨fits_sharedThread h reads (sharedParts h later) R.common f2,
    fits_lastThread h first reads _ R.own tk f3⟩

end HonestTraceRun.LaterTrees

#print axioms HonestTraceRun.LaterTrees.later_threads_fit
#print axioms HonestTraceRun.LaterTrees.last_trees_fixed_at_the_run
#print axioms HonestTraceRun.LaterTrees.later_fields_at_the_proposed_values

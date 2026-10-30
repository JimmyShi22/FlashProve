-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/LaterTreesFixedLetters.lean

Nothing on hiding. No property of the protocol is claimed. Public counts alone.

THE PROPOSED VALUES LAID INTO THE LETTERS: from any value of "LaterLetters" and of "LastLetters" (Honest/Thread/TheLaterThreads.lean) the value with the
fields "fixed" and "taken" laid as LaterTreesFixed.lean proposes, all other fields kept. So the three equations that
"later_fields_at_the_proposed_values" and "later_threads_fit" (LaterTreesFixedAtTheTerm.lean) take as premises CAN BE MET, by "rfl", whatever the other
fields are: the premises of these laws are not empty for that reason.

* "laterLettersFixedByLots later h offsets": "fixed" laid; at a taken source 0 (the shared chain takes no tree over).
* "lastLettersFixedByLots lastLetters h first later offsets": "fixed" and "taken" laid.
* "later_threads_fit_at_laid_letters": both later threads pass "Thread.fits" at these letters, from the two bounds on the offsets and fix₁ alone.

Limits. The offsets are letters: at "fun _ _ => 0" the two bounds hold for nothing, and then the kinds' form "OwnTrees" is met only by senders whose
tables read none of their own challenges. WHICH OFFSETS THE SENDERS OF THE TWO LATER CHAINS HAVE IS SAID BY NOBODY HERE. That the tables laid at the taken
sources are the earlier chains' own is a matter of the letter "table": not treated.
-/
import AtFullSide.HonestTrace.LaterTreesFixedAtTheTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.LaterTrees
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest (threadTwo threadThree)

section
variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The shared chain's letters with "fixed" laid by lots.** -/
def laterLettersFixedByLots (later : LaterLetters A) (h : HeadAtReturn files A)
    (offsets : Nat → Nat → Nat) : LaterLetters A :=
  { later with fixed := fixedByLots h.description.shared.blocksInOrder 0 offsets fun _ _ => 0 }

/-- **The last chain's letters with "fixed" laid by lots and "taken" laid as the sources that its rounds open.** later: the shared
chain's letters, whose "fixed" is read at the trees taken over from that chain. -/
def lastLettersFixedByLots (lastLetters : LastLetters A) (h : HeadAtReturn files A)
    (first : FirstThreadParts A) (later : LaterLetters A) (offsets : Nat → Nat → Nat) :
    LastLetters A :=
  { lastLetters with
    taken := takenSourcesOpened h.description.second.blocksInOrder
    fixed := fixedByLots h.description.second.blocksInOrder
      (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
        roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length) offsets
      (fixedOfEarlierChains first.script.fixed later.fixed
        (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length)) }

end

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  (later : LaterLetters A) (lastLetters : LastLetters A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

/-- **Both later threads pass "fits" at the laid letters.** -/
theorem later_threads_fit_at_laid_letters {offsetShared offsetLast : Nat → Nat → Nat}
    (withinShared : OffsetsWithinRounds h.description.shared.blocksInOrder offsetShared)
    (withinLast : OffsetsWithinRounds h.description.second.blocksInOrder offsetLast)
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    (threadTwo h reads (sharedParts h (laterLettersFixedByLots later h offsetShared)) R).fits
        h.description.shared.blocksInOrder.length = true ∧
      (threadThree h first reads
        (lastParts h first (lastLettersFixedByLots lastLetters h first
          (laterLettersFixedByLots later h offsetShared) offsetLast)) R).fits
        h.description.second.blocksInOrder.length = true :=
  later_threads_fit h first reads (laterLettersFixedByLots later h offsetShared)
    (lastLettersFixedByLots lastLetters h first (laterLettersFixedByLots later h offsetShared)
      offsetLast) R rfl rfl rfl withinShared withinLast fixFirst

end HonestTraceRun.LaterTrees

#print axioms HonestTraceRun.LaterTrees.laterLettersFixedByLots
#print axioms HonestTraceRun.LaterTrees.lastLettersFixedByLots
#print axioms HonestTraceRun.LaterTrees.later_threads_fit_at_laid_letters

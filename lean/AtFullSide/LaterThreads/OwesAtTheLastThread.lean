-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/OwesAtTheLastThread.lean: CONDITIONAL. THE FULL SIZE ALONE.

AT LETTERS WHOSE RIDERS BEGIN WITH THE TWO TIED ONES, AS `lastRiders` DOES, THE FIELD ridersBeginLate IS FALSE
AND THIS STRUCTURE CANNOT BE MET: AtFullSide/LaterThreads/OwesAtTheLastThreadTied.lean stands in its stead.

What is here. THE TWO DEBTS owes₃ AND yes₃ OF `ThreadDebts` (AtFullSide/Honest/ThreadsAtTheTerm.lean): `OwesS` and `YesS` at the second chain's thread: `lastThread` (Honest/Thread/TheFirstThread.lean) with its fields at the
values `lastParts h first L` (Honest/Thread/TheLaterThreads.lean), at ANY letters L, any readers, any input w, any Said and any fall: GATHERED FROM THE FIVE STATEMENTS AT EACH OF ITS FOUR MEMBERS. Nothing new is shown: the chain's length, a split
of the member's number, and the rule `owesS_of_five` | `yesS_of_five` (Honest/Thread/FiveAtBorder.lean). That file's `threadThree` is this thread at the input R.own and at the letters whose field ends is the run's
(AtFullSide/LaterThreads/LastAtRun.lean).

  `lastThreadAt`          the thread
  `LastThreadDebts`       WHAT IS STILL OWED BY OTHERS, one field a debt
  `last_thread_length`    the thread's list has four members (`last_fits_descPure`, Johnson/ToldDescR/PlacesAtTable.lean, at the head's value)
  `five_at_the_linear_claim`   member 0 (the linear claim's second part, kind K14): the law `five_at_lastParts` (AtFullSide/K14/AtLaterThreads.lean)
  `five_at_every_member_of_the_last_thread`   at every number below four
  `owes_and_yes_at_the_last_thread`   **the two debts**

Not shown here. EVERY FIELD OF `LastThreadDebts` IS A HYPOTHESIS; that they can be met together at
one value of the letters is not shown. NO THEOREM OF THIS LIBRARY THAT NAMES THIS THREAD SHOWS A
STAND OF IT AT ANY BORDER BEYOND 0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door
(`doorAtTheTerm`, AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the
two earlier threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. So the two debts are not shown
here to speak at any run: each
of the five is an implication from the thread's stand in front of the member. OF MEMBER 0 ITS WRITERS' OWN TWO LIMITS STAND: nobody shows the items ev and dot, nor the rider at border 0, all owed where the chain is entered; and `BehindS` and
`ExchangeS` hold for nothing wherever the form's test at border 0 is false, which has been evaluated at no state. Nothing on hiding. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import AtFullSide.K14.AtLaterThreads
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder
import Johnson.ToldDescR.PlacesAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.LaterThreads
open ProofFile ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastLetters lastThread lastParts
  head_value)
open VerifiableInference.Desc.Third (S₃)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- The second chain's thread with its fields at `lastParts`. -/
abbrev lastThreadAt (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (L : LastLetters A) (w : Local W₀ Rc ProofFile.Inst Tr) :=
  lastThread h first reads (lastParts h first L) w

/-- **WHAT THE GATHER AT THE SECOND CHAIN STILL TAKES FROM OTHERS.** A definition, meant as a hypothesis: one field a debt. -/
structure LastThreadDebts (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (L : LastLetters A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) : Prop where
  /-- no rider that the letters hold begins before border 2: whoever lays `LastLetters` shows it -/
  ridersBeginLate : ∀ c ∈ L.riders, 2 ≤ c.lo
  /-- the five at the member of the taken trees' sources -/
  atTheSources : FiveAtBorder (lastThreadAt h first reads L w) Said fall 1
  /-- the five at the last chain's proximity test (AtFullSide/LaterThreads/ProximityRestAtTheLastThread.lean carries a law here, under what it asks) -/
  atTheProximityTest : FiveAtBorder (lastThreadAt h first reads L w) Said fall 2
  /-- the five at the chain's end -/
  atTheEnd : FiveAtBorder (lastThreadAt h first reads L w) Said fall 3

variable (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (L : LastLetters A) (w : Local W₀ Rc ProofFile.Inst Tr)
  {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
  {fall : Nat → S₃ → List Fmt.Drawn → Option String}

/-- CONDITIONAL: on h. **The second chain's thread has four members.** -/
theorem last_thread_length : (lastThreadAt h first reads L w).bs.length = 4 :=
  (ToldDesc.last_fits_descPure (head_value h.head)).2

variable {h first reads L w}

/-- CONDITIONAL: on h and one field of D. **THE FIVE AT MEMBER 0.** -/
theorem five_at_the_linear_claim (D : LastThreadDebts h first reads L w Said fall) :
    FiveAtBorder (lastThreadAt h first reads L w) Said fall 0 :=
  AtFullSide.K14.five_at_lastParts h first L reads w Said fall D.ridersBeginLate

/-- CONDITIONAL: on h and D. **THE FIVE AT EVERY MEMBER OF THE SECOND CHAIN's THREAD.** -/
theorem five_at_every_member_of_the_last_thread (D : LastThreadDebts h first reads L w Said fall) :
    ∀ b, b < 4 → FiveAtBorder (lastThreadAt h first reads L w) Said fall b := by
  intro b hb
  obtain rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
  · exact five_at_the_linear_claim D
  · exact D.atTheSources
  · exact D.atTheProximityTest
  · exact D.atTheEnd

/-- CONDITIONAL: on h and D. **`OwesS` AND `YesS` AT THE SECOND CHAIN's THREAD**, at any Said and any fall: at the run's letters, at `saidThree` and at `fallsBy f₃ h.description.second.blocksInOrder` they are the fields owes₃ and yes₃ of
`ThreadDebts`. -/
theorem owes_and_yes_at_the_last_thread (D : LastThreadDebts h first reads L w Said fall) :
    OwesS (lastThreadAt h first reads L w) Said ∧ YesS (lastThreadAt h first reads L w) Said fall := by
  have len : (lastThreadAt h first reads L w).bs.length = 4 := last_thread_length h first reads L w
  have F : ∀ b, b < (lastThreadAt h first reads L w).bs.length →
      FiveAtBorder (lastThreadAt h first reads L w) Said fall b := fun b hb =>
    five_at_every_member_of_the_last_thread D b (len ▸ hb)
  exact ⟨owesS_of_five F, yesS_of_five F⟩

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.last_thread_length
#print axioms AtFullSide.LaterThreads.five_at_the_linear_claim
#print axioms AtFullSide.LaterThreads.five_at_every_member_of_the_last_thread
#print axioms AtFullSide.LaterThreads.owes_and_yes_at_the_last_thread

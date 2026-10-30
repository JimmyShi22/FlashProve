-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/OwesAtTheLastThreadTied.lean: CONDITIONAL. THE FULL SIZE ALONE.

THE YES AT MEMBERS 0 AND 1 IS TAKEN OUT OF THE INVARIANT IN FRONT, NOT SHOWN OF THE RUN: the stand at
border 0 holds `doorRider`'s eleven tests and the test `tiedAheadB` at the start's record, the stand at
border 1 holds what `tiedRider` says, and the yes is read off these. So THIS YES IS HALF A SENTENCE
WITHOUT THE ONE OBJECT's THREE FIELDS `doorRides`, `doorFive` AND `doorTrees`, which speak of what the door
lays into that stand. Nothing here says that the last chain accepts.

What is here. THE SECOND CHAIN's GATHER (AtFullSide/LaterThreads/OwesAtTheLastThread.lean) AT THE FORM OF THE RIDERS THAT THE THREADS' WRITERS LAY: the letters' list of riders begins with `tiedAheadRider` (Honest/K14/TiedAhead.lean: it speaks at border 0 alone) and `tiedRider`
(Honest/Thread/TheLaterThreads.lean: at border 1 alone), and every later one begins at border 2 or later. AT SUCH LETTERS THE FIELD ridersBeginLate OF `LastThreadDebts` IS FALSE (the first two begin at 0 and 1), SO THAT STRUCTURE CANNOT BE MET THERE: THIS ONE STANDS IN ITS STEAD. Member 0's five are the law
`five_at_lastParts_tied` (AtFullSide/K14/AtLastTied.lean). Nothing new is shown.

  `LastThreadDebtsTied`    WHAT IS STILL OWED BY OTHERS, one field a debt
  `five_at_every_member_of_the_last_thread_tied` · `owes_and_yes_at_the_last_thread_tied`   **`OwesS` and `YesS` at `lastThread h first reads (lastParts h first L) w`**, at any Said and fall

Not shown here. EVERY FIELD IS A HYPOTHESIS; that they can be met together at one value of the
letters is not shown here (AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean's head says who
meets what the letters leave). NO THEOREM OF THIS LIBRARY THAT NAMES THIS THREAD SHOWS A STAND OF IT
AT ANY BORDER BEYOND 0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door (`doorAtTheTerm`,
AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the two earlier
threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Each of the five is an
implication from a stand. Of member 0 its writers' limits stand: the items ev and dot, the door's
rider and
the test of `tiedAheadRider` at border 0 are owed where the chain is entered; `BehindS` and `ExchangeS` hold for nothing wherever the form's test at border 0 is false. Nothing on hiding, soundness, completeness or any other property.

No property is claimed.
-/
import AtFullSide.K14.AtLastTied
import AtFullSide.LaterThreads.OwesAtTheLastThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.LaterThreads
open ProofFile ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.FirstThread
open VerifiableInference.Desc.Third (S₃)

section
variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **WHAT THE GATHER AT THE SECOND CHAIN STILL TAKES FROM OTHERS, AT THE RIDERS THAT THE THREADS' WRITERS LAY.** A definition, meant as a hypothesis: one field a debt. -/
structure LastThreadDebtsTied (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (L : LastLetters A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) : Prop where
  /-- the letters' riders are the two tied ones and then riders that begin at border 2 or later: whoever lays `LastLetters` shows it -/
  ridersAreTied : ∃ later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃),
    L.riders = tiedAheadRider _ (LLT25.c2 h.places).rounds :: tiedRider _ h.places :: later ∧
      ∀ c ∈ later, 2 ≤ c.lo
  /-- the five at the member of the taken trees' sources -/
  atTheSources : FiveAtBorder (lastThreadAt h first reads L w) Said fall 1
  /-- the five at the last chain's proximity test -/
  atTheProximityTest : FiveAtBorder (lastThreadAt h first reads L w) Said fall 2
  /-- the five at the chain's end -/
  atTheEnd : FiveAtBorder (lastThreadAt h first reads L w) Said fall 3

variable {h : HeadAtReturn files A} {first : FirstThreadParts A} {reads : IndexReaders W₀ Rc}
  {L : LastLetters A} {w : Local W₀ Rc ProofFile.Inst Tr}
  {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
  {fall : Nat → S₃ → List Fmt.Drawn → Option String}

/-- CONDITIONAL: on h and D. **THE FIVE AT EVERY MEMBER OF THE SECOND CHAIN's THREAD.** -/
theorem five_at_every_member_of_the_last_thread_tied
    (D : LastThreadDebtsTied h first reads L w Said fall) :
    ∀ b, b < 4 → FiveAtBorder (lastThreadAt h first reads L w) Said fall b := by
  intro b hb
  obtain rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
  · obtain ⟨later, hrid, late⟩ := D.ridersAreTied
    exact AtFullSide.K14.five_at_lastParts_tied h first L reads w Said fall hrid late
  · exact D.atTheSources
  · exact D.atTheProximityTest
  · exact D.atTheEnd

/-- CONDITIONAL: on h and D. **`OwesS` AND `YesS` AT THE SECOND CHAIN's THREAD.** -/
theorem owes_and_yes_at_the_last_thread_tied (D : LastThreadDebtsTied h first reads L w Said fall) :
    OwesS (lastThreadAt h first reads L w) Said ∧ YesS (lastThreadAt h first reads L w) Said fall := by
  have len : (lastThreadAt h first reads L w).bs.length = 4 := last_thread_length h first reads L w
  have F : ∀ b, b < (lastThreadAt h first reads L w).bs.length →
      FiveAtBorder (lastThreadAt h first reads L w) Said fall b := fun b hb =>
    five_at_every_member_of_the_last_thread_tied D b (len ▸ hb)
  exact ⟨owesS_of_five F, yesS_of_five F⟩

end

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.five_at_every_member_of_the_last_thread_tied
#print axioms AtFullSide.LaterThreads.owes_and_yes_at_the_last_thread_tied

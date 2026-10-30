-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/LastThreadAtTheValues.lean: CONDITIONAL. THE FULL SIZE ALONE.

THE YES AT MEMBERS 0 AND 1 IS TAKEN OUT OF THE INVARIANT IN FRONT, NOT SHOWN OF THE RUN: the stand at
border 0 holds `doorRider`'s eleven tests and the test `tiedAheadB` at the start's record, the stand at
border 1 holds what `tiedRider` says, and the yes is read off these. So THIS YES IS HALF A SENTENCE
WITHOUT THE ONE OBJECT's THREE FIELDS `doorRides`, `doorFive` AND `doorTrees`, which speak of what the door
lays into that stand. Nothing here says that the last chain accepts.

What is here. THE DEBTS OF THE SECOND CHAIN's GATHER (`LastThreadDebtsTied`,
AtFullSide/LaterThreads/OwesAtTheLastThreadTied.lean) AT THE VALUES THAT THE THREADS' WRITERS LAY
FOR THE RIDERS AND FOR WHAT A STEP KEEPS: `lastRiders` and `lastKeeps`
(Honest/Thread/TheLaterThreads.lean): the members 0, 1 and 3 are had by calls; what these calls ask
takes the fives' place.

  `five_at_the_last_end`   member 3, from the yes there and from the riders and keeps behind it.
     `PlaysS`, `ExchangeS` and `RidesPastS` are the frame's writers' `last_plays`, `last_exchange`,
     `last_rides_three` (AtFullSide/Frames/LastChain.lean); `BehindS` goes by the steps of their
     `last_three`'s own proof, typed here once more, because that law asks beside them for the
     condition of the step's yes, which `BehindS` does not need.
  `LastThreadDebtsAtTheValues`   WHAT IS STILL OWED BY OTHERS: one field a debt.

  `lastThreadDebtsTied_at_the_values`   it gives `LastThreadDebtsTied`.
  `owes_and_yes_at_the_last_thread_at_the_values`   **so `OwesS` and `YesS` at the second chain's
     thread.**

WHO PAYS WHICH MEMBER. 0: `five_at_lastParts_tied`, inside the gather · 1: `five_at_last_one_late`
(AtFullSide/Frames/LastAtValues.lean) · 2: a field · 3: `five_at_the_last_end`, its yes a field.

Not shown here. EVERY FIELD IS A HYPOTHESIS HERE; that they can be met together is not shown here
(AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean's head says who meets what the letters
leave). NO THEOREM OF THIS LIBRARY THAT NAMES THIS THREAD SHOWS A STAND OF IT AT ANY BORDER BEYOND 0
BUT FROM A PREMISE THAT HOLDS ONE. Had: the door (`doorAtTheTerm`,
AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the two earlier
threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Each of the five is an
implication from the thread's stand in front of the member. The riders at the borders 0 and 1 move a
debt to the door. Nothing on
hiding. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import AtFullSide.LaterThreads.OwesAtTheLastThreadTied
import AtFullSide.Frames.LastAtValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.LaterThreads
open ProofFile ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Frames (last_block_three last_plays last_exchange last_rides_three shape_of_form
  form_four keeps_three five_at_last_one_late)
open VerifiableInference.Desc (Block Place step_inv)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (step_three)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- CONDITIONAL: on h, behind and accepted. **THE FIVE AT THE SECOND CHAIN's END**, at any fields of
the thread. behind: at a stand in front of the end the riders at border 4 hold and keeps at the
end's place allows the state as it stands. accepted: the end says yes. -/
theorem five_at_the_last_end (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (behind : ∀ k s m E, ThrS (lastThread h first reads parts w) Said 3 k s m E →
      parts.rides 4 m.st.input s ∧ parts.keeps ⟨3, none, 3, .frame⟩ s s)
    (accepted : AcceptedS (lastThread h first reads parts w) Said fall 3) :
    FiveAtBorder (lastThread h first reads parts w) Said fall 3 := by
  obtain ⟨blk, hblk, hr, -, hd⟩ := last_block_three h first reads parts w
  refine ⟨(last_plays h first reads parts w Said).2, ?_,
    (last_exchange h first reads parts w Said).2, last_rides_three h first reads parts w Said,
    accepted⟩
  refine behindS_quiet _ _ hblk hr fun k s m E s' hA hst => ?_
  obtain ⟨-, -, -, hdec⟩ := step_inv _ _ _ _ _ _ _ hst
  rw [hd] at hdec
  have hform := hA.1.2.2.1
  obtain ⟨f, o, hf, hoo, h2⟩ := shape_of_form h first reads parts w hform
  obtain ⟨h4, hn⟩ := step_three h2 ([] : List (Block S₃ Unit)) [] [] hdec
  obtain ⟨e, -⟩ :=
    VerifiableInference.Desc.Last.end₃_yes ([] : List (Block S₃ Unit)) s s' [] [] hdec
  subst e
  exact ⟨form_four h first reads parts w hf hoo h4 hn hform.2, (behind k _ m E hA).1,
    keeps_three h first reads parts w (behind k _ m E hA).2⟩

/-- **WHAT THE GATHER AT THE SECOND CHAIN STILL TAKES FROM OTHERS, AT THE THREADS' WRITERS' VALUES
OF THE RIDERS AND OF KEEPS.** A definition, meant as a hypothesis: one field a debt. later: the
riders behind the two tied ones. own: what a step keeps beside "the state stays at the frame's two".
-/
structure LastThreadDebtsAtTheValues (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (L : LastLetters A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)) (own : Place → S₃ → S₃ → Prop) :
    Prop where
  /-- the letters' riders are `lastRiders`: by unfolding at their
  value -/
  ridersAreTheLastRiders : L.riders = lastRiders h.places later
  /-- the riders behind the two tied ones begin at border 3 or later: whoever lays them shows it -/
  laterRidersBeginLate : ∀ c ∈ later, 3 ≤ c.lo
  /-- the letters' keeps is `lastKeeps`: by unfolding at their value
  -/
  keepsAreTheLastKeeps : L.keeps = lastKeeps own
  /-- the own clause allows the state as it stands at the taken trees' sources: whoever lays
  it shows this -/
  ownAllowsTheSources : ∀ s, own ⟨3, none, 1, .frame⟩ s s
  /-- the same at the chain's end -/
  ownAllowsTheEnd : ∀ s, own ⟨3, none, 3, .frame⟩ s s
  /-- at a stand in front of the end the riders at border 4 hold: whoever lays the later
  riders shows it -/
  ridersBehindTheEnd : ∀ k s m E, ThrS (lastThreadAt h first reads L w) Said 3 k s m E →
    (lastParts h first L).rides 4 m.st.input s
  /-- the five at the last chain's proximity test -/
  atTheProximityTest : FiveAtBorder (lastThreadAt h first reads L w) Said fall 2
  /-- the chain's end says yes: by the run on shapes
  (AtFullSide/LaterThreads/LastRunClosed.lean, under its own debts) -/
  theEndAccepts : AcceptedS (lastThreadAt h first reads L w) Said fall 3

variable {h : HeadAtReturn files A} {first : FirstThreadParts A} {reads : IndexReaders W₀ Rc}
  {L : LastLetters A} {w : Local W₀ Rc ProofFile.Inst Tr}
  {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
  {fall : Nat → S₃ → List Fmt.Drawn → Option String}
  {later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)} {own : Place → S₃ → S₃ → Prop}

/-- CONDITIONAL: on D. **The debts at the values give the gather's.** -/
theorem lastThreadDebtsTied_at_the_values
    (D : LastThreadDebtsAtTheValues h first reads L w Said fall later own) :
    LastThreadDebtsTied h first reads L w Said fall where
  ridersAreTied := ⟨later, D.ridersAreTheLastRiders,
    fun c hc => Nat.le_trans (by omega) (D.laterRidersBeginLate c hc)⟩
  atTheSources := five_at_last_one_late h first L reads w Said fall D.ridersAreTheLastRiders
    D.laterRidersBeginLate D.keepsAreTheLastKeeps fun _ s _ _ _ => D.ownAllowsTheSources s
  atTheProximityTest := D.atTheProximityTest
  atTheEnd := five_at_the_last_end h first reads (lastParts h first L) w Said fall
    (fun k s m E stand => ⟨D.ridersBehindTheEnd k s m E stand, by
      show L.keeps ⟨3, none, 3, .frame⟩ s s
      rw [D.keepsAreTheLastKeeps]
      exact ⟨fun _ => rfl, D.ownAllowsTheEnd s⟩⟩)
    D.theEndAccepts

/-- CONDITIONAL: on D. **`OwesS` AND `YesS` AT THE SECOND CHAIN's THREAD, FROM THE DEBTS AT THE
VALUES.** Implications from the thread's stand in front of each member; no theorem of this library
that names this thread shows a stand of it at any border beyond 0 but from a premise that holds one.
-/
theorem owes_and_yes_at_the_last_thread_at_the_values
    (D : LastThreadDebtsAtTheValues h first reads L w Said fall later own) :
    OwesS (lastThreadAt h first reads L w) Said ∧ YesS (lastThreadAt h first reads L w) Said fall :=
  owes_and_yes_at_the_last_thread_tied (lastThreadDebtsTied_at_the_values D)

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.five_at_the_last_end
#print axioms AtFullSide.LaterThreads.lastThreadDebtsTied_at_the_values
#print axioms AtFullSide.LaterThreads.owes_and_yes_at_the_last_thread_at_the_values

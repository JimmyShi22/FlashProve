-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/AtLastTied.lean: the linear claim's second part ("K14, second part", the first member
of a proof file's last chain): THE STRUCTURE FiveAtBorder
(Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean) AT THE MEMBER 0 OF THE LAST CHAIN's THREAD
AT lastParts (Honest/Thread/TheLaterThreads.lean), WHERE THE RIDERS THAT LastLetters HOLDS BEGIN
WITH tiedAheadRider (Honest/K14/TiedAhead.lean) AND tiedRider (TheLaterThreads.lean).

  five_at_lastParts_tied   **the five**. hrid: L's riders are: tiedAheadRider at the own test's
                           declared rounds · tiedRider · clauses that begin at border 2 or later
                           (late)
  five_at_lastRiders   the same where L's riders are the value lastRiders (TheLaterThreads.lean)

five_at_lastParts (AtFullSide/K14/AtLaterThreads.lean) asks that every rider of L begin at border 2
or later; it cannot be called where tiedRider, which speaks at border 1, is among them. This one
can.

THE PRICE, AND ALL THAT IS OWED WHERE THE CHAIN IS ENTERED: AtFullSide/K14/AtLaterThreads.lean's
head, limit (1), and one clause more at border 0: tiedAheadB at the record that the chain's start
returns: it reads, in the two earlier chains' books, the numbers of the trees of Omega, of the own
group's members and of the mask. Limit (2) of that head binds here too.

What is not claimed. That the thread's invariant holds at any state: no state is known here at which
the five speak; that tiedAheadB says yes at any record. Nothing on completeness, soundness or
hiding. Terms. letter, border: lean/GLOSSARY.md.
-/
import AtFullSide.K14.AtLaterThreads
import Johnson.Desc.ProofFile.Honest.K14.FiveAtLastThreadTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastLetters lastThread
  lastParts tiedRider lastRiders)
open VerifiableInference.Desc.Third (S₃)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **FiveAtBorder at the member 0 of the last chain's thread at lastParts, with tiedRider laid.**
hrid, late: the form of L's riders. BehindS and ExchangeS hold vacuously wherever fillZ's test at
border 0 is false; ExchangeS takes the items ev and dot, AcceptedS secondDoor's tests, and the
laying of tiedRider the test tiedAheadB, from the invariant in front. -/
theorem five_at_lastParts_tied (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (L : LastLetters A) (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    {later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hrid : L.riders = tiedAheadRider _ (LLT25.c2 h.places).rounds :: tiedRider _ h.places :: later)
    (late : ∀ c ∈ later, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads (lastParts h first L) w) Said fall 0 :=
  five_at_lastThread_laid_tied h first reads (lastParts h first L) w Said fall (fun _ => rfl)
    (fun _ => rfl)
    (fun inp a b q _ _ v hp => pin₁_lastParts h first L inp a b q _ _ v hp)
    (fun inp a b e _ _ v hp => pin_lastParts h first L inp a b e _ _ v hp)
    (LLT25.c2 h.places) (cs := later)
    (fun b v s => by
      show ridersOf (doorRider _ (ToldDesc.p14At A.Z) :: L.riders) b v s ↔ _
      rw [hrid]
      exact Iff.rfl) late

/-- **The same where L's riders are the value lastRiders.** late: each of the later clauses begins
at border 2 or later. -/
theorem five_at_lastRiders (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (L : LastLetters A) (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    {later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hrid : L.riders = lastRiders h.places later) (late : ∀ c ∈ later, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads (lastParts h first L) w) Said fall 0 :=
  five_at_lastParts_tied h first L reads w Said fall hrid late

end AtFullSide.K14

#print axioms AtFullSide.K14.five_at_lastParts_tied
#print axioms AtFullSide.K14.five_at_lastRiders

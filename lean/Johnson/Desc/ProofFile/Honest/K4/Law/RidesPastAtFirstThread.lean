-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RidesPastAtFirstThread.lean: CONDITIONAL: on a head at a return
of the maker, at whichever filling. THE FULL SIZE ALONE.

What is here. THE COLUMN hR OF THE FRAME's GATHERING AT THE MEMBERS OF THE FEED-FORWARD LAYERS' OWN
ROUNDS (sub-protocol K4), AT THE FRAME's OWN FIRST THREAD (`firstThread`,
Honest/Thread/TheFirstThread.lean): `k4_ridesPast_column` (Law/RidesPastColumn.lean) with its one
hypothesis on the thread's parameter for keeps paid at that thread's own value `firstClauses`.
Nothing new is shown: a projection and a call.

  `k4KeepsM_of_firstClauses`   at the kind K4 the frame's clause of keeps gives `K4KeepsM`
     (Law/KeepsStep.lean): it is that sentence with further sentences laid beside it, layer by
     layer; the proof tries four depths, so that one layer more turns no text here.
  `k4_ridesPast_column_firstThread`   **the column at every number of the kind K4.**
  `k4_ridesPastS_firstThread`   `RidesPastS` there.

Not shown here. NO STAND OF THIS THREAD BEYOND BORDER 0 IS KNOWN TO ANYBODY, SO THE STATEMENTS ARE
NOT KNOWN TO SPEAK AT ANY RUN: they speak only where the thread stands in front of the member, keeps
holds and the item's sentence holds in front. h (`HeadAtReturn`): a hypothesis: the library's
hypothesis on the public files at A's public part, and that the maker returned A at SOME filling
(its field returned): which filling is asked nowhere, so A's prover and book are those of any
filling's return. parts, w, Said: letters; nothing is asked of them. That `firstClauses` holds
behind an accepting step of the member is the third part of the end of `k4_behindS_at_first_thread`
(Law/BehindAtFirstThread.lean). Every limit of Law/RidesPastColumn.lean's head holds here. OF ITS
IMPORT CLOSURE 24 FILES ARE NO PART OF THE LIBRARY YET: seven of these writers (this one,
Law/RidesPastColumn.lean, Law/RidersSorted.lean and the four on the run "objects") and seventeen
of the threads' writers (Honest/Thread/TheFirstThread.lean and the files of the clauses beneath it),
which still turn. A LAW, NOT A PART: no file that defines a part of the proof file's description may
import this one. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RidesPastColumn
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (Place KindName)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstClauses firstLetters firstThread)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **AT THE KIND K4 THE FRAME's CLAUSE OF KEEPS GIVES `K4KeepsM`.** -/
theorem k4KeepsM_of_firstClauses (h : HeadAtReturn files A) :
    ∀ (p : Place) (s s' : TS), firstClauses h KindName.K4 p s s' → K4KeepsM s s' :=
  fun _ _ _ a => by
    first
      | exact a.1.1.1.1
      | exact a.1.1.1.1.1
      | exact a.1.1.1.1.1.1
      | exact a.1.1.1.1.1.1.1

/-- CONDITIONAL: on h. **THE COLUMN hR AT EVERY NUMBER OF THE KIND K4, AT THE FRAME's FIRST
THREAD.** The end is an implication from the thread's sentence in front, keeps and the item's own
sentence in front; no stand of the thread beyond border 0 is known. -/
theorem k4_ridesPast_column_firstThread (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K4 →
      ∀ i ∈ (firstThread h parts w).opened b, i ∉ ((firstThread h parts w).row b).shuts →
      i ∉ ((firstThread h parts w).row b).owes → RidesPastAtS (firstThread h parts w) Said b i := by
  unfold firstThread firstLetters
  exact k4_ridesPast_column h.head _ _ _ _ _ _ _ _ _ _ (firstClauses h) w Said
    (k4KeepsM_of_firstClauses h)

/-- CONDITIONAL: on h. **`RidesPastS` AT EVERY NUMBER OF THE KIND K4, AT THE FRAME's FIRST
THREAD.** An implication from the thread's stand in front; no stand beyond border 0 is known. -/
theorem k4_ridesPastS_firstThread (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K4 →
      RidesPastS (firstThread h parts w) Said b :=
  fun b p hb hk =>
    ridesPastS_shares _ Said (k4_ridesPast_column_firstThread h parts w Said b p hb hk)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4KeepsM_of_firstClauses
#print axioms ProofFile.Honest.K4.k4_ridesPast_column_firstThread
#print axioms ProofFile.Honest.K4.k4_ridesPastS_firstThread

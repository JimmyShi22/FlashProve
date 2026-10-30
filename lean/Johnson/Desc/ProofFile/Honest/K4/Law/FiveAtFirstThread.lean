-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FiveAtFirstThread.lean: CONDITIONAL.

Can the hypotheses be met together? NOT KNOWN. The first statement asks h : `HeadAtReturn files A`
(Honest/Thread/TheFirstThread.lean: the maker returned A at some filling, and the library's
hypothesis `AtMgA` at A's public part), g < 12, and hP, hX, hAccepted; the second asks h, g < 12,
hP, hX, hAcceptedJ, hNext. That any files have such an h is not shown here. hP, hX AND hAccepted
(hAcceptedJ, hNext) ARE FIELDS OF THE END THEMSELVES (hX item by item), TAKEN AS HYPOTHESES: they
are other files' work. AND ALL FIELDS ARE IMPLICATIONS FROM THE THREAD's STAND IN FRONT OF THE
MEMBER: NO STAND OF THIS THREAD BEYOND BORDER 0 IS KNOWN TO ANYBODY, SO THE STATEMENTS ARE NOT KNOWN
TO SPEAK AT ANY RUN.

What is here. THE THREADS' WRITERS' TWO STRUCTURES (Honest/Thread/FiveAtBorder.lean) `FiveAtBorder`
(`PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`, `AcceptedS` at one border) AND `FiveAtBorderJ` (the
same four, `AcceptedJ` and `NextJ`, at a family J on the verifier's state) AT THE TWELVE MEMBERS OF
THE FEED-FORWARD LAYERS' OWN ROUNDS (kind K4), the members number 28 g + 4, g < 12, AT THEIR ONE
TERM FOR THE FIRST CHAIN's THREAD, `firstThread h parts w` (Honest/Thread/TheFirstThread.lean),
general in the types of the index, of the tables' randomness and of the trace. No definition; two
statements with their proofs: two tuples.

WHAT IS PROVED IN THE ENDS, AS IMPLICATIONS, FROM h AND g < 12: `BehindS`
(`k4_behindS_at_first_thread`, Law/BehindAtFirstThread.lean) AND `RidesPastS`
(`k4_ridesPast_column_firstThread`, Law/RidesPastAtFirstThread.lean, through the frame's
`ridesPastS_shares`). `PlaysS` is hP, `AcceptedS` is hAccepted, `AcceptedJ` is hAcceptedJ and
`NextJ` is hNext to the letter; `ExchangeS` is hX through the frame's `exchangeS_iff`
(Honest/Thread/SharesS.lean). This file is a join: it gathers; K4 does not count by it while one of
these is a hypothesis.

  `k4_five_at_first_thread`   **`FiveAtBorder (firstThread h parts w) Said fall (28 * g + 4)`**,
      from h, g < 12, hP, hX, hAccepted.
  `k4_five_with_family_at_first_thread`   **`FiveAtBorderJ (firstThread h parts w) Said J fall (28 *
      g + 4)`**, at any family J, from h, g < 12, hP, hX, hAcceptedJ, hNext. (Whoever has
      `AcceptedS` has `AcceptedJ` at every J: the writers' `acceptedJ_of`,
      Honest/Thread/ShapeJ.lean.)

Letters. The public files, the return A, the types of the index, of the tables' randomness and of
the trace, the parts (the script and the falls' stated numbers), the run's input w, what has been
said (Said), the fall and the family J are arguments: nothing is asked of them beyond h and the
hypotheses named, which are sentences on them. THE FALL IS TIED TO NOTHING HERE: the one that the
thread's own test reads is `fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder`.

Limits. CONDITIONAL, as said at the top. All fields hold for nothing at a Said, or at a thread,
whose invariant holds of nothing: so at an input w that the thread's own condition on the input
(`ReadyInput`) refuses. At a prover whose side stops at the member at all challenges, or to whom the
book lends no steps, hP, hX and hAccepted hold for nothing. At a fall that always speaks hAccepted,
hAcceptedJ and hNext hold for nothing; at a fall that never speaks hAccepted asks a yes at all
challenges at which nothing stops. At a family J that holds of no state at the border 28 g + 4,
hAcceptedJ and hNext hold for nothing, and so do the end's last two fields. `firstThread`,
`FiveAtBorder` and `FiveAtBorderJ` are definitions of the threads' writers; if they turn, these
statements turn with them. Its imports reach files that are no part of the library yet: thirteen of
ours under Law/ (this one, BehindAtFirstThread, BehindColumns, FormBehindHead, LaidAtGroup, LaysOwn,
RidesPastAtFirstThread, RidesPastColumn, RidersSorted, ObjectsRidesHead, ObjectsOnAll,
ObjectsOnKeeps, ObjectsOn) and, of the threads' writers, Honest/Thread/FiveAtBorder.lean,
Honest/Thread/TheFirstThread.lean and what that file imports of theirs. THE FULL SIZE ALONE, AND THE
FORMAT's EARLIER HASH ALONE. A LAW, NOT A PART: it rests, through Law/ElevenHead.lean, on modules
under Johnson/Goal/: no file that defines a part may build on it; it states no goal. Nothing on
soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.BehindAtFirstThread
import Johnson.Desc.ProofFile.Honest.K4.Law.RidesPastAtFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread)

variable {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
  (fall : Nat → TS → List Fmt.Drawn → Option String)

/-- **THE FIVE STATEMENTS AT K4's BORDER 28 g + 4, GATHERED AT THE FIRST THREAD.** CONDITIONAL: on
h, hg, and on three of the five themselves: hP, hX, hAccepted. `BehindS` and `RidesPastS` are
proved, as implications from the thread's stand in front; no such stand is known. -/
theorem k4_five_at_first_thread {g : ℕ} (hg : g < 12)
    (hP : PlaysS (firstThread h parts w) Said (28 * g + 4))
    (hX : ∀ i ∈ ((firstThread h parts w).row (28 * g + 4)).owes,
      ExchangeAtS (firstThread h parts w) Said (28 * g + 4) i)
    (hAccepted : AcceptedS (firstThread h parts w) Said fall (28 * g + 4)) :
    FiveAtBorder (firstThread h parts w) Said fall (28 * g + 4) :=
  ⟨hP, k4_behindS_at_first_thread h parts w Said hg, (exchangeS_iff _ Said).2 hX,
    ridesPastS_shares _ Said (k4_ridesPast_column_firstThread h parts w Said (28 * g + 4)
      (IM.k4Place g) (k4_written_place_at_border hg) rfl), hAccepted⟩

/-- **THE SIX STATEMENTS OF THE FORM WITH A FAMILY J ON THE VERIFIER's STATE, GATHERED THERE.**
CONDITIONAL: on h, hg, and on four of the six themselves: hP, hX, hAcceptedJ, hNext. `BehindS` and
`RidesPastS` are proved, as implications from the thread's stand in front; no such stand is known.
-/
theorem k4_five_with_family_at_first_thread (J : Nat → TS → Prop) {g : ℕ} (hg : g < 12)
    (hP : PlaysS (firstThread h parts w) Said (28 * g + 4))
    (hX : ∀ i ∈ ((firstThread h parts w).row (28 * g + 4)).owes,
      ExchangeAtS (firstThread h parts w) Said (28 * g + 4) i)
    (hAcceptedJ : AcceptedJ (firstThread h parts w) Said J fall (28 * g + 4))
    (hNext : NextJ (firstThread h parts w) Said J fall (28 * g + 4)) :
    FiveAtBorderJ (firstThread h parts w) Said J fall (28 * g + 4) :=
  ⟨hP, k4_behindS_at_first_thread h parts w Said hg, (exchangeS_iff _ Said).2 hX,
    ridesPastS_shares _ Said (k4_ridesPast_column_firstThread h parts w Said (28 * g + 4)
      (IM.k4Place g) (k4_written_place_at_border hg) rfl), hAcceptedJ, hNext⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_five_at_first_thread
#print axioms ProofFile.Honest.K4.k4_five_with_family_at_first_thread

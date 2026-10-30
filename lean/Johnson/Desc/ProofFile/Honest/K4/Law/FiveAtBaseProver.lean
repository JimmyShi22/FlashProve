-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FiveAtBaseProver.lean: CONDITIONAL.

Can the hypotheses be met together? NOT KNOWN. The statement asks that the maker returns A at the
base filling (hA), h : `HeadAtReturn files A`, g < 12, and hX. That the maker returns at any files,
and that a return has such an h, are not shown here. hX IS ONE OF THE FIVE STATEMENTS ITSELF, ITEM
BY ITEM, TAKEN AS A HYPOTHESIS: it is another file's work. AND ALL FIELDS ARE IMPLICATIONS FROM THE
THREAD's STAND IN FRONT OF THE MEMBER: NO STAND OF THIS THREAD BEYOND BORDER 0 IS KNOWN TO ANYBODY,
SO THE STATEMENT IS NOT KNOWN TO SPEAK AT ANY RUN.

What is here. THE THREADS' WRITERS' STRUCTURE `FiveAtBorder` (Honest/Thread/FiveAtBorder.lean) AT
THE TWELVE MEMBERS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (kind K4), the members number 28 g + 4, g
< 12, AT THEIR ONE TERM FOR THE FIRST CHAIN's THREAD (`firstThread h parts w`,
Honest/Thread/TheFirstThread.lean) AT THE BASE PROVER: the prover that the maker returns at the
wider filling at the matrices' input. The fall is that thread's own list of falls. No definition;
one statement with its proof: calls.

  `k4_five_at_base_prover`   **`FiveAtBorder (firstThread h parts w) Said (fallsBy (firstFalls A
      parts.numbers) h.firstChain.blocksInOrder) (28 * g + 4)`**, from h, hA, g < 12 and hX.

Whence each field. `PlaysS` and `AcceptedS`: `k4_playsS_first_thread_base`,
`k4_accepted_first_thread_base` (Law/TwoAtFirstThread.lean). `BehindS`: `k4_behindS_at_first_thread`
(Law/BehindAtFirstThread.lean). `RidesPastS`: `k4_ridesPast_column_firstThread`
(Law/RidesPastAtFirstThread.lean). `ExchangeS`: hX, a hypothesis.

Limits. CONDITIONAL, as said at the top. K4 does not count by this statement while hX is a
hypothesis. How often the fall speaks is not said here. At the base prover, not at the term's own
types: the crossing is another house's law. `firstThread` and `FiveAtBorder` are definitions of the
threads' writers; if they turn, this statement turns with them. THE FULL SIZE ALONE, AND THE
FORMAT's EARLIER HASH ALONE. A LAW, NOT A PART: it rests on modules under Johnson/Goal/: no file
that defines a part may build on it; it states no goal. Nothing on soundness, on completeness or on
any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FiveAtFirstThread
import Johnson.Desc.ProofFile.Honest.K4.Law.TwoAtFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstFalls)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (parts : FirstThreadParts A)
  (w : Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

/-- **THE FIVE STATEMENTS AT K4's BORDER 28 g + 4, AT THE BASE PROVER's FIRST THREAD, AT THE FALLS
OF THAT THREAD's OWN LIST.** CONDITIONAL: on h, hA, hg, and on one of the five itself, item by
item: hX. -/
theorem k4_five_at_base_prover
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {g : ℕ} (hg : g < 12)
    (hX : ∀ i ∈ ((firstThread h parts w).row (28 * g + 4)).owes,
      ExchangeAtS (firstThread h parts w) Said (28 * g + 4) i) :
    FiveAtBorder (firstThread h parts w) Said
      (fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder) (28 * g + 4) :=
  k4_five_at_first_thread h parts w Said _ hg (k4_playsS_first_thread_base h parts w Said hA hg) hX
    (k4_accepted_first_thread_base h parts w Said hA hg)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_five_at_base_prover

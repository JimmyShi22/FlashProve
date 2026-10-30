-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FiveWithShapesAtBaseProver.lean: CONDITIONAL.

Can the hypotheses be met together? NOT KNOWN. The statement asks that the maker returns A at the
base filling (hA), h : `HeadAtReturn files A`, g < 12, hX and hyes. That the maker returns at any
files, and that a return has such an h, are not shown here. hX IS ONE OF THE SIX STATEMENTS ITSELF,
ITEM BY ITEM, TAKEN AS A HYPOTHESIS: it is another file's work. hyes: the run on shapes over all 358
members of the first chain says yes from the shape a₀: a premise that all kinds of the first chain
share; that it is true at any public part is not shown here. AND ALL FIELDS ARE IMPLICATIONS FROM
THE THREAD's STAND IN FRONT OF THE MEMBER: NO STAND OF THIS THREAD BEYOND BORDER 0 IS KNOWN TO
ANYBODY, SO THE STATEMENT IS NOT KNOWN TO SPEAK AT ANY RUN.

What is here. THE THREADS' WRITERS' STRUCTURE `FiveAtBorderJ` (Honest/Thread/FiveAtBorder.lean) AT
THE TWELVE MEMBERS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (kind K4), the members number 28 g + 4, g
< 12, AT `firstThread h parts w` (Honest/Thread/TheFirstThread.lean) AT THE BASE PROVER, at the
family J := "the run on shapes over the members in front returns the state's shape" (`shapeJ`,
Honest/Thread/ShapeJ.lean, at the library's table `firstZA` at the return's public part and the
thread's own ground) and at the thread's own list of falls. No definition; one statement with its
proof: calls.

  `k4_five_with_shapes_at_base_prover`   **`FiveAtBorderJ` there**, from h, hA, g < 12, hX and hyes.

Whence each field. `PlaysS`: `k4_playsS_first_thread_base` (Law/TwoAtFirstThread.lean). `BehindS`:
`k4_behindS_at_first_thread` (Law/BehindAtFirstThread.lean). `RidesPastS`:
`k4_ridesPast_column_firstThread` (Law/RidesPastAtFirstThread.lean). `ExchangeS`: hX, a hypothesis.
`AcceptedJ`: `k4_accepted_first_thread_base` (Law/TwoAtFirstThread.lean) through the writers'
`acceptedJ_of`. `NextJ`: `k4_next_at_first_thread` (Law/NextAtFirstThread.lean).

Limits. CONDITIONAL, as said at the top. K4 does not count by this statement while hX is a
hypothesis. At a state of which J does not hold the last two fields say nothing. How often the fall
speaks is not said here. At the base prover, not at the term's own types: the crossing is another
law. `firstThread` and `FiveAtBorderJ` are definitions of the threads' writers; if they
turn, this statement turns with them. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE. A
LAW, NOT A PART: it rests on modules under Johnson/Goal/: no file that defines a part may build on
it; it states no goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FiveAtFirstThread
import Johnson.Desc.ProofFile.Honest.K4.Law.NextAtFirstThread
import Johnson.Desc.ProofFile.Honest.K4.Law.TwoAtFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstFalls seatGround)
open Johnson.AtFull.Shape (Tab.g Tab.vals firstZA ShA)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (parts : FirstThreadParts A)
  (w : Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

/-- **THE SIX STATEMENTS OF THE FORM WITH THE FAMILY "THE RUN ON SHAPES RETURNS THE STATE's SHAPE",
AT K4's BORDER 28 g + 4, AT THE BASE PROVER's FIRST THREAD.** CONDITIONAL: on h, hA, hg, hX, and on
hyes: the run on shapes over all 358 members says yes from a₀. -/
theorem k4_five_with_shapes_at_base_prover
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (a₀ : ShA)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes a₀ 358 = true)
    {g : ℕ} (hg : g < 12)
    (hX : ∀ i ∈ ((firstThread h parts w).row (28 * g + 4)).owes,
      ExchangeAtS (firstThread h parts w) Said (28 * g + 4) i) :
    FiveAtBorderJ (firstThread h parts w) Said
      (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) a₀)
      (fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder) (28 * g + 4) := by
  obtain ⟨⟨M, hM, hE⟩, ho⟩ := k4_lot_at_widerFillAtCPUOWM matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G
  exact k4_five_with_family_at_first_thread h parts w Said _ _ hg
    (k4_playsS_first_thread_base h parts w Said hA hg) hX
    (acceptedJ_of _ Said _ (k4_accepted_first_thread_base h parts w Said hA hg))
    (k4_next_at_first_thread h parts w Said hA _ _ _ hM hE ho a₀ hyes hg)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_five_with_shapes_at_base_prover

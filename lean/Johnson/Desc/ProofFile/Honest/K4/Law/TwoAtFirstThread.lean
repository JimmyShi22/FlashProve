-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/TwoAtFirstThread.lean: CONDITIONAL on h and hA, and the general
statements on hM, hE and ho too.

What is here. TWO OF THE FIVE STATEMENTS AT K4's BORDERS, member number 28 g + 4, g < 12, at the
threads' writers' one term for the first chain: `firstThread h parts w`
(Honest/Thread/TheFirstThread.lean): `PlaysS` (the column hP of `owesS_head_form`) and `AcceptedS`.
First general in the filling, with K4's lot among its lots; then at the wider filling at the index of
matrices, whose return is the base prover H₀, with no premise but the head at the return and the
return.

  `seatGround_at`   the ground of the kinds' clauses is the return's.
  `k4_falls_first`  the first chain's falls hold K4's.
  `k4Fall_in_first`  **each g < 12: `k4Fall (k4PubAt …)`, at the row's own public data, is in that list,
      at every value of the list's numbers.**
  `k4_playsS_first_thread`, `k4_accepted_first_thread_by`, `k4_accepted_first_thread`   **general in
      the filling; `AcceptedS` at any fall under the cover `k4_accepted_last` asks, then at the falls
      of the thread's own list.**
  `k4_playsS_first_thread_base`, `k4_accepted_first_thread_base`   **the two at the base prover.**

WHAT THE TWO DO NOT SAY. `PlaysS` reads neither `ThrS` nor the premise that nothing stops, and
nothing of what is sent: a part pads in silence (Honest/K4/Part.lean's head), so where a maker yields
nothing the part sends its mask entries over zeros. It has chainSteps = .ok l as a premise: that the
book lends K4's row at the base return is not shown here. `AcceptedS`: the member's step tests no
sent value, so it accepts every play of the right shape, a false one too. It speaks only where the
thread stands and no fall of the list at the member's place speaks: at the fall on the first element
of the round "PSC epsilon" of the second token sumcheck, `k4Fall`, it says nothing there. No stand
beyond border 0 is known to meet the thread. A row at wrong cells, weights or look meets both
general statements: telling the honest row from a wrong one is `ExchangeS`'s work. NOT COMPLETENESS.

Who pays the premises. h: part 5's `headAtReturn_base`, from scope, live and hA. hA of the `_base`
forms: `atPure_returns_fillW_at` at `range_matrixInput` (AtFullSide/K12/ReturnsAtAnyIndex.lean), or
part 5's `maker_returns_matrix`; at `VerifierAndGoals.storedPublicFiles` `base_met_zFull` (Law/BaseMetAtFull.lean) has both.
The fall's stated share is a stated number: no bound is shown here. `seatGround_at` and the cover by
membership have twins in IOP's E2E/TheFalls.lean (`speaks_of_mem`), which is not read here. It stands
over files that are no part of laws.14, and beneath `half_atPure_at` stand comparisons by Lean's
kernel that no independent checker has replayed (Law/HalfAtPureBy.lean). THE FULL SIZE ALONE, THE
FORMAT's EARLIER HASH ALONE. A LAW, NOT A PART: it rests on modules under Johnson/Goal/.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PlaysFive
import Johnson.Desc.ProofFile.Honest.K4.Law.LookJoinDear
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPureBy
import Johnson.Desc.ProofFile.Honest.K4.Law.FillFalls
import Johnson.Desc.ProofFile.Honest.K4.Law.FallsJoin
import Johnson.Desc.ProofFile.Honest.K4.Law.HgAtPure
import Johnson.Desc.ProofFile.Honest.K4.Law.LaidAtGroup
import Johnson.Desc.ProofFile.Honest.K4.Law.LotThrough
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block)
open P5J (TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4 laid_at)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstFalls seatGround
  seatGround_of_base)

variable {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}

/-- CONDITIONAL on h and hA. **The ground of the kinds' clauses is the return's.** -/
theorem seatGround_at (h : HeadAtReturn files A) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A) : seatGround A = A.G := by
  obtain ⟨Bs, base, O⟩ := h.head.laid.opened
  have eG := atPure_ground h.head hA
  rw [seatGround_of_base O.made]
  exact Option.some.inj (O.blank.symm.trans eG)

/-- CONDITIONAL on h and hA. **The first chain's falls hold the lot's own.** -/
theorem k4_falls_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A) :
    ∀ f ∈ k4LotFalls A.Z A.G, f ∈ firstFalls A parts.numbers := by
  refine k4LotFalls_sub h.head (atPure_ground h.head hA) parts.numbers.roundsBefore
    fun g hg hp e => ?_
  unfold firstFalls
  rw [seatGround_at h hA]
  exact fallsHead_k4 hg e

/-- CONDITIONAL on h and hA. **At each g < 12 the first chain's list of falls holds `k4Fall` at the very
public data at which K4's row stands at member number 28 g + 4**, at every value of the list's
numbers. -/
theorem k4Fall_in_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A) {g : ℕ} (hg : g < 12) :
    ∃ x blk, LaidK4 A.Z h.firstChain (28 * g + 4) (2 * g) g x blk ∧
      (k4Fall (k4PubAt h.firstChain (28 * g + 4) x) : Fall TS) ∈ firstFalls A parts.numbers := by
  obtain ⟨x, blk, Lh⟩ := laid_at h.head hg
  exact ⟨x, blk, Lh, k4_falls_first h parts hA _ (k4Fall_mem_atPure h.head Lh hA)⟩

variable (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)

/-- CONDITIONAL on h, hA, hM, hE and ho. **`PlaysS` AT K4's BORDER, AT THE FIRST THREAD**, general in
the filling. -/
theorem k4_playsS_first_thread {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    {g : ℕ} (hg : g < 12) : PlaysS (firstThread h parts w) Said (28 * g + 4) := by
  obtain ⟨x, blk, Lh⟩ := laid_at h.head hg
  exact k4_playsS_half h.head A.H _ _ _ _ _ _ _ _ _ _ w Said Lh
    (half_atPure_at h.head Lh hA cells weights look hM hE ho)

/-- CONDITIONAL on h, Lh, hA, hM, hE, ho and hf. **`AcceptedS` AT K4's BORDER, AT THE FIRST THREAD, AT
ANY FALL UNDER THE COVER**: where the fall says nothing at the member, `k4CoinZero` says nothing. -/
theorem k4_accepted_first_thread_by {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    {g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 A.Z h.firstChain (28 * g + 4) (2 * g) g x blk)
    {fall : Nat → TS → List Fmt.Drawn → Option String}
    (hf : ∀ s ds, fall (28 * g + 4) s ds = none →
      k4CoinZero (k4PubAt h.firstChain (28 * g + 4) x) ds = none) :
    AcceptedS (firstThread h parts w) Said fall (28 * g + 4) :=
  k4_accepted_last h.head A.H _ _ _ _ _ _ _ _ _ _ w Said Lh
    (half_atPure_at h.head Lh hA cells weights look hM hE ho) hf

/-- CONDITIONAL on h, hA, hM, hE and ho. **`AcceptedS` AT K4's BORDER, AT THE FIRST THREAD, AT THE
FALLS OF THAT THREAD's OWN LIST**, general in the filling. -/
theorem k4_accepted_first_thread {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    {g : ℕ} (hg : g < 12) :
    AcceptedS (firstThread h parts w) Said
      (fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder) (28 * g + 4) := by
  obtain ⟨x, blk, Lh⟩ := laid_at h.head hg
  exact k4_accepted_first_thread_by h parts w Said hA cells weights look hM hE ho Lh
    (hf_head Lh (k4_falls_first h parts hA _ (k4Fall_mem_atPure h.head Lh hA)))

end ProofFile.Honest.K4

namespace ProofFile.Honest.K4
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstFalls)
open OnBytes.Desc.First.K4.Honest (K4Pub)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (parts : FirstThreadParts A)
  (w : Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

/-- CONDITIONAL on h and hA. **`PlaysS` AT K4's BORDER, AT THE BASE PROVER.** -/
theorem k4_playsS_first_thread_base
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {g : ℕ} (hg : g < 12) : PlaysS (firstThread h parts w) Said (28 * g + 4) := by
  obtain ⟨⟨M, hM, hE⟩, ho⟩ := k4_lot_at_widerFillAtCPUOWM matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G
  exact k4_playsS_first_thread h parts w Said hA _ _ _ hM hE ho hg

/-- CONDITIONAL on h and hA. **`AcceptedS` AT K4's BORDER, AT THE BASE PROVER.** -/
theorem k4_accepted_first_thread_base
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {g : ℕ} (hg : g < 12) :
    AcceptedS (firstThread h parts w) Said
      (fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder) (28 * g + 4) := by
  obtain ⟨⟨M, hM, hE⟩, ho⟩ := k4_lot_at_widerFillAtCPUOWM matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G
  exact k4_accepted_first_thread h parts w Said hA _ _ _ hM hE ho hg

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Fall_in_first
#print axioms ProofFile.Honest.K4.k4_playsS_first_thread
#print axioms ProofFile.Honest.K4.k4_accepted_first_thread_by
#print axioms ProofFile.Honest.K4.k4_accepted_first_thread
#print axioms ProofFile.Honest.K4.k4_playsS_first_thread_base
#print axioms ProofFile.Honest.K4.k4_accepted_first_thread_base

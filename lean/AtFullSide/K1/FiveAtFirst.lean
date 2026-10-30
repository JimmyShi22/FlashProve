-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FiveAtFirst.lean: the shared sending (kind K1): the five statements in the form FiveAtBorderJ at
26 of the kind's 52 members of the first chain, at the first thread of the base prover as
Honest/Thread/TheFirstThread.lean writes it (firstThread h parts w), with the Script firstScriptAt.

  1  k1_fiveJ_two_first      at number 2
  2  k1_fiveJ_digits_first   at K1.noL l true, at each l below 25

Corollaries of k1_fiveJ_two and k1_fiveJ_digits (FiveAtBase.lean) by firstThread_is. The base that the public
part's seat makes is drawn from the head (reads_head_at, Johnson/AtFull/Shape/ReadsHeadAtHead.lean), so hB is
no hypothesis here. J is shapeJ at the table of steps and at the start's shape startShA.

Limits.
  * hyes is a hypothesis: the run on shapes returns over the 358 members, from startShA. It is proved at no
    public files here. The fields accepted and next rest on it.
  * hA (the maker returns A at the base filling), h (the head at that return) and hQ (the thread's Script is
    firstScriptAt) are hypotheses.
  * The fields accepted and next are asked with J in hand. That J begins at the chain's start, and that it is
    carried, which needs NextJ at every member in front, of every kind, is not shown here. At a fall that
    always speaks they are idle.
  * Each field stands under the thread's invariant in front of the member. That the invariant holds there at
    a run needs the five statements at every member in front, of every kind.
  * The thread's valid asks ReadyInput h.description A.H of the run's input. That the input of a served request
    meets it is a named proposition of E2E/TheHonestProver.lean (ReadyAtServedRequests), which is not shown
    here; at an input that does not meet it all six fields are idle.
  * The 25 members "reads" and number 356 are not here.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.FiveAtBase
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.AtFull.Shape.ReadsHeadAtHead
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The five statements at number 2, at the first thread.** -/
theorem k1_fiveJ_two_first
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I S Op A h.firstChain) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 =
      true) :
    FiveAtBorderJ (firstThread h parts w) Said
      (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
      2 := by
  obtain ⟨Bs, _, _, _, _, _, hB, -⟩ := reads_head_at h.head
  rw [firstThread_is, hQ]
  rw [seatGround_of_base hB] at hyes ⊢
  exact k1_fiveJ_two h.head hA hB _ _ _ _ _ _ _ _ _ _ _ _ _ _ w Said fall hyes

/-- **The five statements at each of the 25 members "digits", at the first thread.** -/
theorem k1_fiveJ_digits_first
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I S Op A h.firstChain) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 =
      true) {l : ℕ} (hl : l < 25) :
    FiveAtBorderJ (firstThread h parts w) Said
      (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
      (K1.noL l true) := by
  obtain ⟨Bs, _, _, _, _, _, hB, -⟩ := reads_head_at h.head
  rw [firstThread_is, hQ]
  rw [seatGround_of_base hB] at hyes ⊢
  exact k1_fiveJ_digits h.head hA hB _ _ _ _ _ _ _ _ _ _ _ _ _ _ w Said fall hyes hl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_fiveJ_two_first
#print axioms ProofFile.Honest.K1.k1_fiveJ_digits_first

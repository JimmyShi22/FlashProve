-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/WrowAtFirst.lean: THE TWO SHARES OF THE EXCHANGE AT NUMBER 356 AT THE FIRST THREAD, WITH THE
SCRIPT firstScriptAt: the premise hWrow of k1_fiveJ_first (FiveByKind.lean), and pileOne beside it.
Statements and proofs, by calls.

  `items_356_first`   pileOne and wrow: k13_items_at_356_at_firstThread at K1's record at 356
                        (k1Seated_first's third part), the cells by the Script's own text

Limits. hO: the filling's filler of the pile is pileAnyK3: a premise here. Nothing on any property.
-/
import AtFullSide.K1.FirstScript
import AtFullSide.K13.AtFirstThread356

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K13 (pileAnyK3)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The two shares at number 356, at the first thread.** -/
theorem items_356_first
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I S Op A h.firstChain) (w : LocB W₀)
    (hO : Op.pile = pileAnyK3)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop) :
    ExchangeAtS (firstThread h parts w) Said 356 .pileOne ∧
      ExchangeAtS (firstThread h parts w) Said 356 .wrow := by
  obtain ⟨-, -, blk, R⟩ := k1Seated_first h.head hA
    (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
    (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁
    h.description.t₂ 339 (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w
  unfold jobWAt at R
  rw [hO] at R
  have eL : firstLetters h parts w = lettersHead h.head A.H (firstScriptAt I S Op A h.firstChain)
      (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
      (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁
      h.description.t₂ 339 (ReadyInput h.description A.H)
      (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
      (kpBy (firstClauses h)) w := by
    unfold firstLetters
    rw [hQ]
  rw [← eL] at R
  exact AtFullSide.K13.k13_items_at_356_at_firstThread I OnBytes.secondHashFunction S Op hA h parts w R
    (by rw [hQ]; rfl) Said

/-- **The premise hWrow of k1_fiveJ_first.** -/
theorem hWrow_first
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I S Op A h.firstChain) (w : LocB W₀)
    (hO : Op.pile = pileAnyK3)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop) :
    ExchangeAtS (firstThread h parts w) Said 356 .wrow :=
  (items_356_first hA h parts hQ w hO Said).2

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.items_356_first
#print axioms ProofFile.Honest.K1.hWrow_first

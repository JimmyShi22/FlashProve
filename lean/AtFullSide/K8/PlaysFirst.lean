-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/PlaysFirst.lean: the debt «plays» at the smallness test's draw, at the first thread itself,
at the base prover: the prover that the maker returns at the wider filling.

  k8_playsS_first   PlaysS at firstThread, at a member of the kind, at every Said

Limits. The return is the base filling's: at the term's prover this file says nothing, and that the
head holds at that return is a premise: HeadAtReturn. That a stand exists is not shown.
-/
import AtFullSide.K8.FiveAtBase
import AtFullSide.K8.KeepsBehind
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open VerifiableInference.Desc (KindName Place)
open ProofFile.Honest
open ProofFile.Honest.FirstThread

variable {W₀ : Type} (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The kind's member plays at the first thread, at every Said.** -/
theorem k8_playsS_first (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o Sz O) = .ok A)
    (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    PlaysS (firstThread h parts w) Said b := by
  obtain ⟨l, hl, rfl⟩ := k8_number ha hk
  rw [firstThread_is, P1K8T.drawAt_place]
  exact AtFullSide.K8.playsS_at_base I o Sz O h.head hA parts.script _ _ _ _ _ _ _ _ _ w Said
    (by omega)

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_playsS_first

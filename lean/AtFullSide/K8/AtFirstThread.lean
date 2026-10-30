-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/AtFirstThread.lean: the debts «behind» and «rides past» at the smallness test's draw, at
the first thread at a return of the maker: the letters that the thread's own file names, not a copy
of them.

  k8_behindS_first, k8_ridesPastS_first   the two at firstThread

Limits. The head is the return's. Nothing here says that any stand meets the thread.
-/
import AtFullSide.K8.RidesPast
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open VerifiableInference.Desc (KindName Place)
open ProofFile.Honest
open ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The debt «behind» at the first thread, at every Said.** -/
theorem k8_behindS_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    BehindS (firstThread h parts w) Said b := by
  rw [firstThread_is]
  exact k8_behindS h.head A.H parts.script _ _ _ _ _ _ _ _ _ _ _ _ _ _ w Said ha hk

/-- **The debt «rides past» at the first thread, at every Said.** -/
theorem k8_ridesPastS_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    RidesPastS (firstThread h parts w) Said b := by
  rw [firstThread_is]
  exact k8_ridesPastS h.head A.H parts.script _ _ _ _ _ _ _ _ _ _ _ _ _ _ w Said ha hk

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_behindS_first
#print axioms AtFullSide.K8.Term.k8_ridesPastS_first

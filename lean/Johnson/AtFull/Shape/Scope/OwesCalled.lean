-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesCalled.lean: KindPaid at the kinds K6, K8 and K11, at the first thread at the return of the maker at
the base filling, with the Script firstScriptAt: the houses' theorems called.

  `k6_paid_base`    allFiveAtTheBaseProver
  `k8_paid_base`    k8_owes_baseMaker
  `k11_paid_base`   k11_five_at_matrix

Limits. Each called file's own limits stand. Nothing on any property.
-/
import Johnson.AtFull.Shape.Scope.OwesHeadKinds
import AtFullSide.E2E.OutputHeadFiveAtTheNamedFiles
import AtFullSide.K8.AllAtBaseMaker
import AtFullSide.K11.AtFirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput baseMaker)
open ProofFile.Honest.K1 (firstScriptAt)
open VerifiableInference.Desc (KindName)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- The first thread's letters at the named Script. -/
noncomputable abbrev baseLetters (hd : HeadAtReturn files A) (numbers : FallNumbers)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) :=
  firstLetters hd ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain, numbers⟩ w

/-- **K11's place is paid.** -/
theorem k11_paid_base (hM : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    (numbers : FallNumbers) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m) :
    KindPaid (baseLetters hd numbers w) Said KindName.K11 :=
  k11_paid (AtFullSide.K11.k11_five_at_matrix hM hd numbers w Said hS fun _ _ _ => none)

/-- **K8's places are paid.** -/
theorem k8_paid_base (hM : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    (numbers : FallNumbers) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m) :
    KindPaid (baseLetters hd numbers w) Said KindName.K8 := fun _ _ hb hk =>
  have F := AtFullSide.K8.Term.k8_owes_baseMaker hM hd numbers w Said hS hb hk
  ⟨fun _ => F.1, fun _ => owedAt_of_exchange F.2.2.1⟩

/-- **K6's place is paid.** -/
theorem k6_paid_base (hM : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    (numbers : FallNumbers) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    KindPaid (baseLetters hd numbers w) Said KindName.K6 :=
  k6_paid (AtPublicFiles.AtFiles.HonestTerm.OutputHead.allFiveAtTheBaseProver hM hd _ rfl w Said
    fun _ _ _ => none)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.k11_paid_base
#print axioms Johnson.AtFull.Shape.Scope.k8_paid_base
#print axioms Johnson.AtFull.Shape.Scope.k6_paid_base

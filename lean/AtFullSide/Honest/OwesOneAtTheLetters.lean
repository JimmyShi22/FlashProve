-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
AtFullSide/Honest/OwesOneAtTheLetters.lean: the first chain's four debts at every member (OwesS), at the first chain's named
letters thread₁ and said₁, with nothing of part 5's gather left as a premise. A joining; nothing is evaluated here.

  restOwed_at_letters    RestOwed (Johnson/AtFull/Shape/Scope/OwesGather.lean) at the letters, from the maker's return, the head and
                         hw: the run's own input is of a typed instance
  restOwed_at_tiedYes    the same with hw paid from the relation TiedYes and the return of ready
  owes_one_at_letters    OwesS (thread₁ h R) (said₁ h R) from the maker's return, the head, live and hw: part 5's owes_at_letters
  owes_one_at_tiedYes    the same at a run whose instance the relation ties

Limits. Premises: the maker's return, the head, the public test live, and hw or what pays it. OwesS says that the sender plays, what
lies behind, the exchange and what rides past, at the stands at which the thread's invariant and what is said hold; it does not say
that a step accepts, nor that a run stands at a border. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.Honest.RestOwedAtTheLetters
import Johnson.AtFull.Shape.Scope.OwesLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.OwesOne
open VerifiableInference.Desc (Chain)
open P5J (TS)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles WZ TiedYes descZ)
open LPFD.Full (XF)
open OnBytes (TableKey)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker)
open AtFullSide.Honest.TheLetters (numbers thread₁ said₁)
open AtFullSide.K2.Base (TypedAtRun)
open Johnson.AtFull.Shape.Scope (RestOwed owes_at_letters)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **What the gather leaves, at the letters.** -/
theorem restOwed_at_letters (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (hw : TypedAtRun R.own) (Bs : ProofFile.PureBase) :
    RestOwed h (numbers h) R.own (said₁ h R) Bs :=
  ⟨kindTwo_paid_at_letters made h R hw, kindTen_paid_at_the_letters made h R⟩

/-- **owes₁ at the letters**, from the maker's return, the head, live and hw. -/
theorem owes_one_at_letters (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (hw : TypedAtRun R.own) :
    OwesS (thread₁ h R) (said₁ h R) := by
  obtain ⟨Bs, _, O⟩ := h.head.laid.opened
  exact owes_at_letters made h R live O.made (restOwed_at_letters made h R hw Bs)

section Tied
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ X' : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Tr X₀ X')
  (Hp : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Tr X₀ X')
  {Yes : FullSizeMatrix → XF → Prop} {n : ℕ} {w : WZ files} {x : ProofFile.Inst}

/-- **What the gather leaves, at a run whose instance the relation ties.** -/
theorem restOwed_at_tiedYes (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (tied : TiedYes files Zp Np cF run₂ run₃ B G Hp Yes n w x)
    {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (returns : ready h.description A.B A.H w₀ rc x k = .ok R) (Bs : ProofFile.PureBase) :
    RestOwed h (numbers h) R.own (said₁ h R) Bs :=
  restOwed_at_letters made h R (typedAtRun_of_tiedYes files Zp Np cF run₂ run₃ B G Hp tied returns) Bs

/-- **owes₁ at a run whose instance the relation ties.** -/
theorem owes_one_at_tiedYes (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (tied : TiedYes files Zp Np cF run₂ run₃ B G Hp Yes n w x)
    {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (returns : ready h.description A.B A.H w₀ rc x k = .ok R) :
    OwesS (thread₁ h R) (said₁ h R) :=
  owes_one_at_letters made h live R (typedAtRun_of_tiedYes files Zp Np cF run₂ run₃ B G Hp tied returns)

end Tied

end AtFullSide.Honest.OwesOne

#print axioms AtFullSide.Honest.OwesOne.restOwed_at_letters
#print axioms AtFullSide.Honest.OwesOne.owes_one_at_letters
#print axioms AtFullSide.Honest.OwesOne.restOwed_at_tiedYes
#print axioms AtFullSide.Honest.OwesOne.owes_one_at_tiedYes

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
AtFullSide/Honest/OwesOneFilled.lean: the field owes₁ of TheThreadsHalf (AtFullSide/Honest/TheOneObject.lean), in the field's own type:
at every tied run the socket Socket.owes₁ at the first chain's letters.

  typed_at_a_tied_run    the run's own input is of a typed instance, from the run's own two fields tied and ready
  restOwed_at_a_tied_run part 5's RestOwed at a tied run: both of its fields
  owes₁_filled           ∀ r : TiedRun h hr, Socket.owes₁ h (TheLetters.first h) r.R
  withOwesOne            a value of TheThreadsHalf with that field laid in: a test that the type fits; it pays no other field

Limits. Premises: the maker's return, the head and the public test live. No value of TheThreadsHalf or of TheOneObject is read by
owes₁_filled. The socket says that the sender plays, what lies behind, the exchange and what rides past, at the stands at which the
thread's invariant and what is said hold; not that a step accepts, nor that a run stands at a border. That a tied run exists is not shown
here. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.Honest.OwesOneAtTheLetters
import AtFullSide.Honest.TheOneObject

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixFilling)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles)
open Johnson.AtFull.Shape.Scope (RestOwed)

local instance (priority := high) nonemptyPadZ_owesOneFilled : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_owesOneFilled : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_owesOneFilled : Inhabited RunValue := ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **At a tied run the run's own input is of a typed instance.** -/
theorem typed_at_a_tied_run (r : TiedRun h hr) : AtFullSide.K2.Base.TypedAtRun r.R.own :=
  OwesOne.typedAtRun_of_tiedYes Z _ _ _ _ _ _ _ _ r.tied.2 r.ready

/-- **What part 5's gather leaves, at a tied run.** -/
theorem restOwed_at_a_tied_run
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (r : TiedRun h hr)
    (Bs : ProofFile.PureBase) :
    RestOwed h (TheLetters.numbers h) r.R.own (TheLetters.said₁ h r.R) Bs :=
  OwesOne.restOwed_at_letters made h r.R (typed_at_a_tied_run r) Bs

/-- **THE FIELD owes₁.** -/
theorem owes₁_filled
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∀ r : TiedRun h hr, Socket.owes₁ h (TheLetters.first h) r.R :=
  fun r => OwesOne.owes_one_at_letters made h live r.R (typed_at_a_tied_run r)

/-- The field laid into a value: the type fits. -/
def TheThreadsHalf.withOwesOne
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (T : TheThreadsHalf h hr) :
    TheThreadsHalf h hr :=
  { T with owes₁ := owes₁_filled made live }

end AtFullSide.Honest

#print axioms AtFullSide.Honest.typed_at_a_tied_run
#print axioms AtFullSide.Honest.restOwed_at_a_tied_run
#print axioms AtFullSide.Honest.owes₁_filled
#print axioms AtFullSide.Honest.TheThreadsHalf.withOwesOne

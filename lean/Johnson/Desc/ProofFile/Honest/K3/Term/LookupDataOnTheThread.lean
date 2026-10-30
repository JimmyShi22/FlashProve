-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING. The index's type, its reader and the randomness's type are letters.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupDataOnTheThread.lean: the honest side of the kind
"lookup" (K3): the lookups' data at the input of a run's state that stands on a thread.

The laws of Honest/K3/Term/LookupDataAtTheHonestTrace.lean speak of an input t. The statements on a
thread bind a state m under the invariant Thr, whose last clause says that m's input is valid. This
file goes from that clause to these laws' premise on the input.

What is shown.
  inputOnTheThreadHoldsTheHonestTrace: at a state on a thread whose valid inputs hold the honest
    trace of a served request, the state's input does.
  lookupDataOnTheThread: at live files, at such a state, what each lookup's row is handed is a lawful
    lookup instance.
  lookupDataAtValidInputs: the same with no thread in sight, at every input of such a set.

The premise validInputsHoldTheHonestTrace is paid by nobody here: whoever gives a thread its clause
valid has to give one that holds it. Where the valid inputs are ones that ready could prepare, at a
return of the maker over the matrices, it is paid in
Honest/K3/Term/LookupDataAtReadyInputs.lean.

Not claimed: that a verifier's block accepts; anything on soundness, completeness or zero knowledge.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDataAtTheHonestTrace
import Johnson.Desc.ProofFile.Honest.Thread.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open Inst.Model (Instance ppref ScalesAndPolicy)

section AnyThread
variable {W₀ Rc : Type} {book : ProverCoinCounts} {State Claim Stop Own Public : Type}
  (thread : Thread book State Claim Stop (Local W₀ Rc Inst Cells) Own Public)
  (said : Nat → Coins book → Mid (Local W₀ Rc Inst Cells) Own → Prop)
  {publicPart : Pub} {weights : W₀ → Weights}

/-- **The input of a state on the thread holds the honest trace of a served request.** -/
theorem inputOnTheThreadHoldsTheHonestTrace
    (validInputsHoldTheHonestTrace : ∀ input, thread.valid input →
      ∃ index request, InputHoldsTheHonestTrace publicPart weights input index request)
    {border : Nat} {coins : Coins book} {state : State}
    {run : Mid (Local W₀ Rc Inst Cells) Own} {tables : Env}
    (onTheThread : ThrS thread said border coins state run tables) :
    ∃ index request,
      InputHoldsTheHonestTrace publicPart weights run.st.input index request :=
  validInputsHoldTheHonestTrace run.st.input onTheThread.1.2.2.2.2.2.2

/-- **At live files, at a state on the thread, what each lookup's row is handed is a lawful lookup
instance.** -/
theorem lookupDataOnTheThread {files : VerifierAndGoals.PublicFiles} {settings : ScalesAndPolicy}
    (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (filesAreLive : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (publicPartIsMade :
      ProofFile.pubPlain OnBytes.secondHashFunction files.pol files.lay files.KL = .ok publicPart)
    (validInputsHoldTheHonestTrace : ∀ input, thread.valid input →
      ∃ index request, InputHoldsTheHonestTrace publicPart weights input index request)
    {border : Nat} {coins : Coins book} {state : State}
    {run : Mid (Local W₀ Rc Inst Cells) Own} {tables : Env}
    (onTheThread : ThrS thread said border coins state run tables) :
    ∀ site ∈ lookSites publicPart,
      LookupDataIsLawful publicPart site (lookupWitness publicPart weights site run.st.input) := by
  obtain ⟨index, request, holds⟩ :=
    inputOnTheThreadHoldsTheHonestTrace thread said validInputsHoldTheHonestTrace onTheThread
  exact lookupDataAtLiveFiles filesAreInScope filesAreRead filesAreLive publicPartIsMade holds

/-- **The same with no thread in sight**: at every input of a set of inputs that hold the honest trace
of a served request. -/
theorem lookupDataAtValidInputs {files : VerifierAndGoals.PublicFiles} {settings : ScalesAndPolicy}
    (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (filesAreLive : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (publicPartIsMade :
      ProofFile.pubPlain OnBytes.secondHashFunction files.pol files.lay files.KL = .ok publicPart)
    (validInput : Local W₀ Rc Inst Cells → Prop)
    (validInputsHoldTheHonestTrace : ∀ input, validInput input →
      ∃ index request, InputHoldsTheHonestTrace publicPart weights input index request) :
    ∀ input, validInput input → ∀ site ∈ lookSites publicPart,
      LookupDataIsLawful publicPart site (lookupWitness publicPart weights site input) := by
  intro input valid
  obtain ⟨index, request, holds⟩ := validInputsHoldTheHonestTrace input valid
  exact lookupDataAtLiveFiles filesAreInScope filesAreRead filesAreLive publicPartIsMade holds

end AnyThread

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.inputOnTheThreadHoldsTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.lookupDataOnTheThread
#print axioms ProofFile.Honest.K3.Term.lookupDataAtValidInputs

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING whose index is a matrix of the full size's shape and whose trace goes through the
index that the matrix holds. The randomness's type and the sides' own states are letters.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupDataAtReadyInputs.lean: the honest side of the kind
"lookup" (K3): the lookups' data at an input that ready could prepare, at a return of the maker.

A return's prover computes the filling's trace. So an input whose trace is the one that the prover
computes for its index and its instance holds the honest trace of a served request, and the laws of
Honest/K3/Term/LookupDataAtTheHonestTrace.lean apply at it. That clause is the last one of ReadyInput
(Honest/Thread/ReadyInput.lean).

What is shown.
  inputWithTheProversTraceHoldsTheHonestTrace: from that one clause.
  readyInputsHoldTheHonestTrace: the same of an input that meets ReadyInput.
  askedReplyOfAReadyInputIsAToken: the reply that such an input's instance asks about is a token's
    image: the served request's own next token.
  lookupDataOnAThreadOfReadyInputs: at live files, at a state on a thread whose valid inputs meet
    ReadyInput, what each lookup's row is handed is a lawful lookup instance.

Not claimed: that the lot which a filling lays at the lookups' places has this reader; that a
verifier's block accepts; anything on soundness, completeness or zero knowledge.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDataOnTheThread
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import E2E.Lookup.InputAtTheMatrices

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open Inst.Model (ScalesAndPolicy ppref)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.OnPublicFiles (Flat.indexOf)

variable {Rc Shared Own : Type} {files : VerifierAndGoals.PublicFiles}
  {filling : ProofFile.Honest.OnlineProverParts FullSizeMatrix Rc Cells Shared Own} {returned : OnlineProverWithDescription FullSizeMatrix Rc Cells Shared Own}

/-- The reader of the weights at a matrix: the plain reader of its cells. -/
abbrev matrixWeights : FullSizeMatrix → Weights := fun matrix => ⟨AtPublicFiles.Key.cellsReader matrix⟩

/-- **An input whose trace is the one that the return's prover computes holds the honest trace of a
served request.** -/
theorem inputWithTheProversTraceHoldsTheHonestTrace
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL filling = .ok returned)
    (traceGoesThroughTheIndex : ∀ publicPart matrix asked,
      filling.trace publicPart matrix asked =
        (Flat.indexOf matrix).bind fun index => fullIn.trace publicPart index asked)
    (input : Local FullSizeMatrix Rc Inst Cells)
    (traceIsTheProvers : returned.H.trace input.w₀ input.x = some input.trace) :
    ∃ index request,
      InputHoldsTheHonestTrace returned.Z matrixWeights input index request := by
  rw [(atPure_ok makerReturns).2.2.2.1, traceGoesThroughTheIndex] at traceIsTheProvers
  exact AtPublicFiles.Lookup.inputHoldsTheHonestTraceAtTheMatrices returned.Z input traceIsTheProvers

/-- **An input that ready could prepare holds the honest trace of a served request.** -/
theorem readyInputsHoldTheHonestTrace
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL filling = .ok returned)
    (traceGoesThroughTheIndex : ∀ publicPart matrix asked,
      filling.trace publicPart matrix asked =
        (Flat.indexOf matrix).bind fun index => fullIn.trace publicPart index asked)
    {description : FileDescription Inst} (input : Local FullSizeMatrix Rc Inst Cells)
    (ready : ReadyInput description returned.H input) :
    ∃ index request,
      InputHoldsTheHonestTrace returned.Z matrixWeights input index request :=
  inputWithTheProversTraceHoldsTheHonestTrace makerReturns traceGoesThroughTheIndex input ready.2.2

/-- **The reply that a ready input's instance asks about is a token's image.** -/
theorem askedReplyOfAReadyInputIsAToken
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL filling = .ok returned)
    (traceGoesThroughTheIndex : ∀ publicPart matrix asked,
      filling.trace publicPart matrix asked =
        (Flat.indexOf matrix).bind fun index => fullIn.trace publicPart index asked)
    {description : FileDescription Inst} (input : Local FullSizeMatrix Rc Inst Cells)
    (ready : ReadyInput description returned.H input) :
    OnBytes.Desc.Reply.isToken ppref.V input.x.asked = true := by
  obtain ⟨_, _, holds⟩ :=
    readyInputsHoldTheHonestTrace makerReturns traceGoesThroughTheIndex input ready
  exact (ProofFile.asked_of_instOf holds.instanceIsTheRequest).2

/-- **At live files, at a state on a thread whose valid inputs are ready, what each lookup's row is
handed is a lawful lookup instance.** -/
theorem lookupDataOnAThreadOfReadyInputs {settings : ScalesAndPolicy} {book : ProverCoinCounts}
    {State Claim Stop Public : Type}
    (thread : Thread book State Claim Stop (Local FullSizeMatrix Rc Inst Cells) Own Public)
    (said : Nat → Coins book → Mid (Local FullSizeMatrix Rc Inst Cells) Own → Prop)
    (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (filesAreLive : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL filling = .ok returned)
    (traceGoesThroughTheIndex : ∀ publicPart matrix asked,
      filling.trace publicPart matrix asked =
        (Flat.indexOf matrix).bind fun index => fullIn.trace publicPart index asked)
    {description : FileDescription Inst}
    (validInputsAreReady : ∀ input, thread.valid input → ReadyInput description returned.H input)
    {border : Nat} {coins : Coins book} {state : State}
    {run : Mid (Local FullSizeMatrix Rc Inst Cells) Own} {tables : Env}
    (onTheThread : ThrS thread said border coins state run tables) :
    ∀ site ∈ lookSites returned.Z,
      LookupDataIsLawful returned.Z site
        (lookupWitness returned.Z matrixWeights site run.st.input) :=
  lookupDataOnTheThread thread said filesAreInScope filesAreRead filesAreLive
    (atPure_ok makerReturns).1
    (fun input valid => readyInputsHoldTheHonestTrace makerReturns traceGoesThroughTheIndex input
      (validInputsAreReady input valid))
    onTheThread

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.inputWithTheProversTraceHoldsTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.readyInputsHoldTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.askedReplyOfAReadyInputIsAToken
#print axioms ProofFile.Honest.K3.Term.lookupDataOnAThreadOfReadyInputs

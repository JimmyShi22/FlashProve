-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING.
Johnson/Desc/ProofFile/Honest/K3/Term/RequestAtTheLettersCoversTheSamePositions.lean: the honest
side of the kind "lookup" (K3), at the lookup on the calls of the output head: the premise
RequestCoversTheSamePositions (Term/HeadRiderVanishesAtTheHonestTrace.lean) is met by the request
that the words of an instance's request file spell (rqAt, Johnson/Desc/Kinds/Head/AtZ.lean), where
the instance is read as the request. P5J.At.rq, the letter of the first chain's data, is rqAt.

What is shown.
  wordsOfTheRequestFileAreTheInstances: the words of the request file are the request's words.
  requestAtTheLettersIsTheInstances: rqAt at the instance's public part is the library's reqX.
  requestAtTheLettersCoversTheSamePositions: so the premise holds of it.

Premise: the instance is read as the request (ProofFile.instOf).

Not claimed: anything on soundness, completeness or zero knowledge.
-/
import Johnson.Desc.ProofFile.InstOf
import Johnson.Desc.Kinds.Law.AtZReqX
import Johnson.Desc.ProofFile.Honest.K3.Term.HeadRiderVanishesAtTheHonestTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open Inst.Model (Instance ppref)
open VerifiableInference.Desc.Kinds.Head.AtZ (rqAt rq_is_reqX)
open VerifiableInference.Desc.Kinds.Head.Law (reqX)

/-- The words of the request file of an instance that is read as a request are that request's. -/
theorem wordsOfTheRequestFileAreTheInstances {givenInstance : ProofFile.Inst} {request : Instance ppref}
    (instanceIsTheRequest : ProofFile.instOf givenInstance = some request) :
    OnBytes.Model.Verify.words32 givenInstance.pub.request =
      OnBytes.Flat.requestWordsOf request := by
  rw [← (ProofFile.instOf_bytes instanceIsTheRequest).1]
  exact OnBytes.Flat.words32_bytesOfWords _

/-- **The request that the request file's words spell is the library's reqX at the request.** -/
theorem requestAtTheLettersIsTheInstances (publicPart : ProofFile.Pub) {givenInstance : ProofFile.Inst}
    {request : Instance ppref} (instanceIsTheRequest : ProofFile.instOf givenInstance = some request) :
    rqAt publicPart givenInstance.pub = reqX request :=
  rq_is_reqX publicPart givenInstance.pub request
    (wordsOfTheRequestFileAreTheInstances instanceIsTheRequest)

/-- **So it covers the positions that the request covers.** -/
theorem requestAtTheLettersCoversTheSamePositions (publicPart : ProofFile.Pub) {givenInstance : ProofFile.Inst}
    {request : Instance ppref} (instanceIsTheRequest : ProofFile.instOf givenInstance = some request) :
    RequestCoversTheSamePositions (rqAt publicPart givenInstance.pub) request := by
  rw [requestAtTheLettersIsTheInstances publicPart instanceIsTheRequest]
  exact requestOfTheInstanceCoversTheSamePositions request

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.wordsOfTheRequestFileAreTheInstances
#print axioms ProofFile.Honest.K3.Term.requestAtTheLettersIsTheInstances
#print axioms ProofFile.Honest.K3.Term.requestAtTheLettersCoversTheSamePositions

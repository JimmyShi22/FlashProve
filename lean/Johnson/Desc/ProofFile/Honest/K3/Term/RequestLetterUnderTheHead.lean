-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING.
Johnson/Desc/ProofFile/Honest/K3/Term/RequestLetterUnderTheHead.lean: the honest side of the kind
"lookup" (K3), at the lookup on the calls of the output head: under the head (P5J.AtMgA) the letter
rq of the first chain's data is the request that the request file's words spell (rqAt,
Johnson/Desc/Kinds/Head/AtZ.lean), and the public record of these data is the public part's.

What is shown.
  requestLetterUnderTheHeadIsTheWordsRequest: the letter is rqAt at the public part. By unfolding.
  publicRecordUnderTheHeadIsThePublicParts: P5J.At.X is the public part's record. By unfolding.
  requestLetterUnderTheHeadIsTheInstances: so, where an instance is read as a request, the letter at
    the instance's public part is the library's reqX at the request.
  requestLetterUnderTheHeadCoversTheSamePositions: so it meets RequestCoversTheSamePositions.

Not claimed: anything on soundness, completeness or zero knowledge.
-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.ProofFile.Honest.K3.Term.RequestAtTheLettersCoversTheSamePositions

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open Inst.Model (Instance ppref)
open VerifiableInference.Desc.Kinds.Head.AtZ (rqAt)
open VerifiableInference.Desc.Kinds.Head.Law (reqX)

variable {olderHash : ProofFile.SecondHashFunctionArgument} {files : VerifierAndGoals.PublicFiles} {whole : OnBytes.Maker.WholeD}
  {run : LPFD.Full.RunPF} {publicPart : ProofFile.Pub} {places : H2U.Places4}
  {firstChain : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {headsPlace : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head the letter rq is the request that the request file's words spell.** -/
theorem requestLetterUnderTheHeadIsTheWordsRequest
    (head : P5J.AtMgA olderHash files whole run publicPart places firstChain headsPlace) :
    head.𝔇.rq = rqAt publicPart :=
  rfl

/-- The public record of the first chain's data is the public part's. -/
theorem publicRecordUnderTheHeadIsThePublicParts (publicPart : ProofFile.Pub) :
    P5J.At.X publicPart = publicPart.p.X :=
  rfl

/-- **Where an instance is read as a request, the letter at its public part is the library's reqX at
the request.** -/
theorem requestLetterUnderTheHeadIsTheInstances
    (head : P5J.AtMgA olderHash files whole run publicPart places firstChain headsPlace)
    {givenInstance : ProofFile.Inst} {request : Instance ppref}
    (instanceIsTheRequest : ProofFile.instOf givenInstance = some request) :
    head.𝔇.rq givenInstance.pub = reqX request :=
  requestAtTheLettersIsTheInstances publicPart instanceIsTheRequest

/-- **So it covers the positions that the request covers.** -/
theorem requestLetterUnderTheHeadCoversTheSamePositions
    (head : P5J.AtMgA olderHash files whole run publicPart places firstChain headsPlace)
    {givenInstance : ProofFile.Inst} {request : Instance ppref}
    (instanceIsTheRequest : ProofFile.instOf givenInstance = some request) :
    RequestCoversTheSamePositions (head.𝔇.rq givenInstance.pub) request :=
  requestAtTheLettersCoversTheSamePositions publicPart instanceIsTheRequest

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.requestLetterUnderTheHeadIsTheWordsRequest
#print axioms ProofFile.Honest.K3.Term.publicRecordUnderTheHeadIsThePublicParts
#print axioms ProofFile.Honest.K3.Term.requestLetterUnderTheHeadIsTheInstances
#print axioms ProofFile.Honest.K3.Term.requestLetterUnderTheHeadCoversTheSamePositions

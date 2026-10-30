-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/CompleteAndServedInUse.lean

This file proves that, at all public files in use, some request is served, and states this beside
completeness of the interactive oracle proof on served requests at the same files. Completeness
"on served requests" would hold vacuously at files where no request is served; this file shows
that there is one.

Terms.
  * Public files are "in use" when FilesInUse files parameters holds
    (Johnson/Face/FinalStatement.lean): the files are in scope (InScope), they read as these
    parameters, their policy is exact match, and they pass protocolDataWellFormed, the verifier's first test on
    public files.
  * ServedRequest (E2E/CompleteAsIOPAtFiles.lean) relates an index and an instance: the index is
    that of some weights, a prompt and output tokens make a well-formed request, the model's
    result on that request is these output tokens, and the instance is what the verifier's builder
    makes of them.

Main statements.
  * some_request_is_served_in_use: at all public files in use there are an index and an instance
    with ServedRequest committerCoinCountLessOne files inUse.read index instance_.
  * complete_and_served_at_every_files_in_use: at all public files in use, that statement holds,
    and so does CompleteOnServedRequests files inUse.read ((termLetters thePartsAt).provers
    files).

Limits.
  * It is shown that one index and one instance are in the relation ServedRequest. It is not shown
    how many are, nor which requests the relation leaves out. A request at which the model has no
    result lies outside it.
  * The index is that of made-up weights. The example beneath (Meaning.served_met,
    Johnson/Goal/Meaning/ServedMeans.lean) uses the library's own weights under which the model
    answers 1 after any one token, with the prompt [0] and the output [1]. It says nothing of a
    real model's weights.
  * Both theorems begin "at all public files in use". That some files are in use is not shown in
    this file. That the stored full-size files are in use is shown in the library
    (filesTaken_stored, theLive_zFull).
  * AtFullSide/E2E/TheCompiledStepFilled.lean does not import this file, so finalAtT1_filled does
    not carry its first clause.
  * The proofs in this file only combine theorems of other files: servedRequest_met at the fields
    inScope and read of FilesInUse, and completeOnServedRequests_at_every_files_in_use. Every
    limit stated in the header of AtFullSide/E2E/CompleteAtEveryFilesInUse.lean holds here too.
  * At the level of the interactive oracle proof, before any hashing or compilation. Nothing on
    soundness, and nothing on what a proof hides.
  * The statements are about the honest prover as it is defined in Lean, default values included.
    It is a definition, not a program that runs. Nothing here is about the C++ programs.
  * The statements hold for the full-size layout alone (InScope: the layout file is that of the
    stored full-size example), and for the format's second hash function OnBytes.secondHashFunction alone.

Built on.
  * servedRequest_met (E2E/CompleteAsIOPServedLaws.lean).
  * completeOnServedRequests_at_every_files_in_use
    (AtFullSide/E2E/CompleteAtEveryFilesInUse.lean).
-/
import AtFullSide.E2E.CompleteAtEveryFilesInUse
import E2E.CompleteAsIOPServedLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm

/-- At all public files in use some request is served. The example beneath is at made-up weights.
-/
theorem some_request_is_served_in_use (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    ∃ index instance_, ServedRequest committerCoinCountLessOne files inUse.read index instance_ :=
  servedRequest_met committerCoinCountLessOne files inUse.inScope inUse.read

/-- At all public files in use, some request is served, and the interactive oracle proof is
complete on served requests, in the form of the first clause of TermLeft. -/
theorem complete_and_served_at_every_files_in_use (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    (∃ index instance_, ServedRequest committerCoinCountLessOne files inUse.read index instance_) ∧
      CompleteOnServedRequests files inUse.read ((termLetters thePartsAt).provers files) :=
  ⟨some_request_is_served_in_use files parameters inUse,
    completeOnServedRequests_at_every_files_in_use files parameters inUse⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.some_request_is_served_in_use
#print axioms VerifiableInference.Compilation.complete_and_served_at_every_files_in_use

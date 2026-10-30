-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/CompleteAtEveryFilesInUse.lean

This file proves completeness of the interactive oracle proof on served requests, at all public
files in use, in the form that the compilation theorem final_at_T1 (AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean)
takes as a hypothesis. It supplies the hypothesis CompleteUnderTheHead of
AtFullSide/E2E/TheCompiledStepFromTheHead.lean from complete_at_the_files
(AtFullSide/Honest/CompleteAtTheFiles.lean). It has no definition of its own.

Terms.
  * Public files are "in use" when FilesInUse files parameters holds
    (Johnson/Face/FinalStatement.lean): the files are in scope (InScope), they read as these
    parameters, their policy is exact match, and they pass protocolDataWellFormed, the verifier's first test on
    public files.
  * (termLetters thePartsAt).provers files is HonestProvers.ofThreeProvers (honestProvers files
    (thePartsAt files)): the honest provers of the interactive oracle proof as defined in Lean, at
    the argument thePartsAt (E2E/KeyArgumentsAt.lean).
  * CompleteOnServedRequests (E2E/CompleteAsIOPAtFiles.lean) is CompleteIOP on the relation
    ServedRequest at the error completenessTarget (2^-41).

Main statements.
  * completeUnderTheHead_paid: CompleteUnderTheHead holds.
  * completeOnServedRequests_at_every_files_in_use: at all public files in use,
    CompleteOnServedRequests files inUse.read ((termLetters thePartsAt).provers files) holds. This
    is the first clause of TermLeft, the hypothesis of final_at_T1.
  * final_from_T3: assume that at all public files in use there are numbers offlineStops,
    linkStops and onlineStops at which ZeroKnowledgeOnServedRequests holds of (termLetters
    thePartsAt).provers files and 2^-157 + (offlineStops + linkStops + 688127 * onlineStops) ≤
    stepError. Then FinalComplete (honestProversAndSettingsOf thePartsAt), FinalZeroKnowledge (honestProversAndSettingsOf
    thePartsAt) stepError and RepliesFit (honestProversAndSettingsOf thePartsAt) hold.

Limits.
  * The names of the definitions mean exactly what the definitions say. The sentences in this
    header summarise them and do not replace them.
  * The first two theorems are at the level of the interactive oracle proof, before any hashing or
    compilation. They are not the compiled statement FinalComplete.
  * final_at_T1 takes completeness and zero knowledge of the interactive oracle proof together, so
    final_from_T3 keeps the hypothesis on zero knowledge. That hypothesis is proved in
    AtFullSide/E2E/TheCompiledStepFilled.lean (termLeftLaterClauses_filled), for every stepError
    of at least stepErrorAtTheStops. The header of that file lists the limits on the three fields
    of FinalStatement that are reached.
  * On served requests alone: a request at which the model has no result, or a result other than
    the claimed output, lies outside ServedRequest, and the first two theorems say nothing about
    it. What else that relation leaves out is not examined here.
  * The statements are about the honest prover as it is defined in Lean, default values included.
    It is a definition, not a program that runs. Nothing here is about the C++ programs. It is not
    shown that the default values in that definition are never used.
  * The proofs in this file only combine theorems of other files. Every limit stated in the header
    of AtFullSide/Honest/CompleteAtTheFiles.lean holds here too, among them: closed facts beneath
    are checked by evaluation in Lean's kernel, and no independent checker has replayed them.
  * The proofs beneath use theOneObjectValue (AtFullSide/Honest/TheOneObjectValue.lean), whose
    parameter open₂ is set to zeros. The statements of this file do not name that value or that
    parameter. It is not shown here that nothing depends on that choice.
  * The statements hold for the full-size layout alone (InScope: the layout file is that of the
    stored full-size example), and for the format's second hash function OnBytes.secondHashFunction alone.
  * Nothing on soundness. This file adds no statement on what a proof hides beyond
    ZeroKnowledgeOnServedRequests, as defined in
    VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean, and FinalZeroKnowledge, as defined
    in Johnson/Face/FinalStatement.lean; both occur in final_from_T3 alone.

Built on.
  * complete_at_the_files (AtFullSide/Honest/CompleteAtTheFiles.lean).
  * CompleteUnderTheHead, complete_at_every_files_in_use, final_from_the_head
    (AtFullSide/E2E/TheCompiledStepFromTheHead.lean).
-/
import AtFullSide.E2E.TheCompiledStepFromTheHead
import AtFullSide.Honest.CompleteAtTheFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm

/-- CompleteUnderTheHead holds, by complete_at_the_files. -/
theorem completeUnderTheHead_paid : CompleteUnderTheHead :=
  fun _ _ _ live hr made h => (AtFullSide.Honest.complete_at_the_files live hr made h).1

/-- Completeness of the interactive oracle proof on served requests at all public files in use:
the first clause of TermLeft. -/
theorem completeOnServedRequests_at_every_files_in_use :
    ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      CompleteOnServedRequests files inUse.read ((termLetters thePartsAt).provers files) :=
  complete_at_every_files_in_use completeUnderTheHead_paid

/-- Conditional on the hypothesis on zero knowledge of the interactive oracle proof: the
conclusion of final_at_T1 at thePartsAt. -/
theorem final_from_T3 (stepError : ℝ≥0∞)
    (T3 : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      ∃ offlineStops linkStops onlineStops : ℝ≥0∞,
        ZeroKnowledgeOnServedRequests files inUse.read ((termLetters thePartsAt).provers files)
          offlineStops linkStops onlineStops ∧
        (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
          stepError) :
    (FinalComplete (honestProversAndSettingsOf thePartsAt) ∧
        FinalZeroKnowledge (honestProversAndSettingsOf thePartsAt) stepError) ∧
      RepliesFit (honestProversAndSettingsOf thePartsAt) :=
  final_from_the_head stepError completeUnderTheHead_paid T3

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.completeUnderTheHead_paid
#print axioms VerifiableInference.Compilation.completeOnServedRequests_at_every_files_in_use
#print axioms VerifiableInference.Compilation.final_from_T3

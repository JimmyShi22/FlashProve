-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/TheCompiledStepFilled.lean

This file proves finalAtT1_filled: three of the six fields of FinalStatement
(Johnson/Face/FinalStatement.lean), namely complete, zeroKnowledge and repliesFit, for the honest
part honestProversAndSettingsOf thePartsAt. The proof calls the compilation theorem final_at_T1
(AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean) and supplies both of its hypotheses on the interactive oracle
proof from theorems of other files.

Terms.
  * Public files are "in use" when FilesInUse files parameters holds: the files are in scope
    (InScope), they read as these parameters, their policy is exact match (the output must be the
    model's, token for token), and they pass protocolDataWellFormed, the verifier's first test on public files.
  * thePartsAt (E2E/KeyArgumentsAt.lean) gives, for each set of public files, the argument parts
    of the honest provers honestProvers files parts. (termLetters thePartsAt).provers files is
    HonestProvers.ofThreeProvers (honestProvers files (thePartsAt files)).
  * honestProversAndSettingsOf thePartsAt (AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean) is the honest part of the compiled
    system: these provers, made to refuse a request that is not served, together with the
    compilation settings.

Main statements.
  * stepErrorAtTheStops is the number 2^-157 + (0 + 0 + 688127 * 2^-174).
  * termLeftLaterClauses_filled: for every stepError with stepErrorAtTheStops ≤ stepError, and at
    all public files in use, there are three numbers offlineStops, linkStops and onlineStops (the
    proof takes 0, 0 and 2^-174) such that ZeroKnowledgeOnServedRequests holds of the provers
    (termLetters thePartsAt).provers files at these numbers, and 2^-157 + (offlineStops +
    linkStops + 688127 * onlineStops) ≤ stepError. These are the second and third clause of
    TermLeft, the hypothesis of final_at_T1.
  * finalAtT1_filled_withRoom: for every stepError with stepErrorAtTheStops ≤ stepError,
    FinalComplete (honestProversAndSettingsOf thePartsAt), FinalZeroKnowledge (honestProversAndSettingsOf thePartsAt) stepError
    and RepliesFit (honestProversAndSettingsOf thePartsAt) hold.
  * finalAtT1_filled: the same three at stepError := stepErrorAtTheStops. It has no hypothesis.

What the three conclusions say, by their definitions in Johnson/Face/FinalStatement.lean. Each is
about all public files in use and about the compiled system finalSystem at the honest part.
  * FinalComplete: for all weights and every well-formed request whose claimed output is the
    model's result, with the honest committer and prover, the verifier rejects with probability at
    most finalCompletenessError (2^-40). The probability is over a hash function drawn at random
    and the honest side's coins.
  * FinalZeroKnowledge at an error: the form ZeroKnowledgeShownBelowWhere
    (VerifiableInference/Labelled.lean) at told := requestLabel, for well-formed requests, up to
    finalVerifierQueries (2^64) hash queries and finalReplyCount (688127) proofs, with that error
    as the bar on the statistical distance.
  * RepliesFit: 688127 is at most onlineRunsPerCopy, the columns that the proofs open fit each
    table's budget (TableBudgetFits), and one run each of the honest sampler, committer and prover
    together make at most honestQueryBudget (2^48) hash queries.

Limits.
  * The names of the definitions mean exactly what the definitions say. The sentences in this
    header summarise them and do not replace them.
  * Three of the six fields of FinalStatement are reached: complete, zeroKnowledge, repliesFit.
    The fields sound, binding and handsOutNoProof are not reached in this file.
  * The bound of FinalZeroKnowledge is for one commitment, one copy of the committed table, and at
    most 688127 replies, against any verifier with at most 2^64 hash queries. Beyond these numbers
    the statement says nothing, and nothing in the compiled prover counts replies.
  * The hypothesis on the interactive oracle proof that is supplied here,
    ZeroKnowledgeOnServedRequests, is honest-verifier. The next three points are about that
    hypothesis and its definition, not about the compiled statement.
  * The relation in the statements is ServedRequest: the model's result on the request is the
    claimed output. A request that is not served, and so every request at which the model has no
    result, enters the definition in one way only: proversAtFiles makes the provers refuse it, the
    field refuses of RunByRun asks that the online prover withholds at every message there, and
    the simulators are told of each request whether it is served
    (VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean).
  * Whether a request is served depends on the weights. The definition does not hide it: its
    simulators are told it for each request.
  * The definition asks that simulators exist. It puts no bound on their running time.
  * The compiled statement FinalZeroKnowledge is not honest-verifier: it is against any verifier
    with at most 2^64 hash queries. The simulator answers the hash queries itself, and its running
    time is not bounded.
  * The public files' policy is exact match (FilesInUse).
  * In FinalZeroKnowledge the simulator is told requestLabel's value for each request, and on the
    real side that value is shown to the verifier beside each proof (ZeroKnowledgeShownWhere,
    VerifiableInference/Labelled.lean).
  * This file adds no statement on what a proof hides beyond FinalZeroKnowledge, as defined in
    Johnson/Face/FinalStatement.lean, and ZeroKnowledgeOnServedRequests, as defined in
    VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean.
  * FinalComplete is silent where the model's result is not the claimed output, and hence also
    where the model has no result: its premise is that the result is the request's output. What
    the prover does there is the subject of the field handsOutNoProof, which is not among the
    three fields reached.
  * All three conclusions begin "at all public files in use". That the stored full-size files are
    in use is shown in the library (filesTaken_stored, theLive_zFull) but is not called in this
    file.
  * The statements are about the honest prover as it is defined in Lean, default values included.
    It is a definition, not a program that runs. It is not shown that the default values in that
    definition are never used. Nothing here is about the C++ programs.
  * The statements hold for the full-size layout alone (InScope: the layout file is that of the
    stored full-size example), and for the format's second hash function OnBytes.secondHashFunction alone.
  * FinalComplete and FinalZeroKnowledge are statements in the random-oracle model: the hash
    function is drawn at random. The format's second hash function is a fixed public function
    inside the description and is not a random oracle (FinalStatement's docstring).
  * The proofs in this file only combine theorems of other files. Every limit stated in the
    headers of AtFullSide/Honest/CompleteAtTheFiles.lean and
    AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean holds here too. Among them: some of the
    intermediate statements (KindShare) that zkOnServedRequests_inScope combines speak only of the
    lists of their kind that are present and of the parts that a run calls, and hold vacuously
    where there are none; that such lists are present is not stated for every kind. The steps
    between use theOneObjectValue (AtFullSide/Honest/TheOneObjectValue.lean), which is a value at
    what onlineProverFromPublicFiles returns at baseFilling; most of its fields are implications whose premise is an
    invariant of a thread; its parameter open₂ is set to zeros. The statements of this file do not
    name that value or that parameter. It is not shown here that nothing depends on that choice.
    Closed facts beneath are checked by evaluation in Lean's kernel, and no independent checker
    has replayed them.

Built on.
  * final_from_T3 and completeUnderTheHead_paid (AtFullSide/E2E/CompleteAtEveryFilesInUse.lean):
    the call of final_at_T1 with completeness of the interactive oracle proof supplied.
  * zkOnServedRequests_inScope (AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean):
    ZeroKnowledgeOnServedRequests at 0, 0 and 2^-174.
  * final_at_T1, TermLeft, honestProversAndSettingsOf (AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean).
-/
import AtFullSide.E2E.CompleteAtEveryFilesInUse
import AtFullSide.E2E.ZeroKnowledgeFromTheRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm

/-- The left side of the inequality in TermLeft at offlineStops = 0, linkStops = 0 and onlineStops
= 2^-174. -/
def stepErrorAtTheStops : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ 157 + (0 + 0 + (688127 : ℕ) * ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)))

/-- The second and third clause of TermLeft at all public files in use, for every stepError that
is at least stepErrorAtTheStops. -/
theorem termLeftLaterClauses_filled (stepError : ℝ≥0∞)
    (room : stepErrorAtTheStops ≤ stepError) :
    ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      ∃ offlineStops linkStops onlineStops : ℝ≥0∞,
        ZeroKnowledgeOnServedRequests files inUse.read ((termLetters thePartsAt).provers files)
          offlineStops linkStops onlineStops ∧
        (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
          stepError :=
  fun _ _ inUse => ⟨0, 0, ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)),
    zkOnServedRequests_inScope inUse.inScope inUse.pass inUse.read, room⟩

/-- The fields complete, zeroKnowledge and repliesFit of FinalStatement for honestProversAndSettingsOf thePartsAt,
for every stepError that is at least stepErrorAtTheStops. The limits are in the header of this
file. -/
theorem finalAtT1_filled_withRoom (stepError : ℝ≥0∞)
    (room : stepErrorAtTheStops ≤ stepError) :
    (FinalComplete (honestProversAndSettingsOf thePartsAt) ∧
        FinalZeroKnowledge (honestProversAndSettingsOf thePartsAt) stepError) ∧
      RepliesFit (honestProversAndSettingsOf thePartsAt) :=
  final_from_T3 stepError
    (termLeftLaterClauses_filled stepError room)

/-- The same at stepError := stepErrorAtTheStops, with no hypothesis. The limits are in the header
of this file. -/
theorem finalAtT1_filled :
    (FinalComplete (honestProversAndSettingsOf thePartsAt) ∧
        FinalZeroKnowledge (honestProversAndSettingsOf thePartsAt) stepErrorAtTheStops) ∧
      RepliesFit (honestProversAndSettingsOf thePartsAt) :=
  finalAtT1_filled_withRoom stepErrorAtTheStops (le_refl _)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.termLeftLaterClauses_filled
#print axioms VerifiableInference.Compilation.finalAtT1_filled_withRoom
#print axioms VerifiableInference.Compilation.finalAtT1_filled

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheSixLines.lean: the six lines, each a theorem about compile at flashProveAtFiles,
and what stands beside them.

What the lines speak of:
  PublicSetup: the three public files that the verifier takes, at exact match, that pass the test
  on the files, with what they read as.
  flashProve: what compile takes, at such files.

The six lines:
 1. sound: an output that is not the model's, at the weights that an extractor reads off the
    commitment and the committer's hash queries, is rarely accepted.
 2. soundAndBinding: the same, and the commitment opens to those weights alone.
 3. completeOnCanServe: the general property CompleteOn, at the requests that can be served and
    whose output is the model's: the honest proof is accepted there.
 4. zeroKnowledgeOnCanServe: the general property ZeroKnowledgeOn, at the requests that can be
    served: a simulator makes what a verifier sees there, at outputs that are the model's.
 5. refusedHandsOutNoProof: at a refused request the prover returns the empty form alone.
 6. repliesFit: the numbers that the proof of zero knowledge reads, and a bound on the honest side's
    hash queries.

Lines 1 to 4 draw the hash function at random: they are statements in the random-oracle model.
Line 5 holds at every hash function.

Beside them:
  leanVerifier: the compiled verifier with BLAKE2b plugged in.
  completeAtWellFormedRequests: line 3 at a well-formed request whose result is its claimed output.
  zeroKnowledgeAtEveryRequest: a corollary of lines 4 and 5: at every request, a simulator told
  whether it is served makes what a verifier sees.
  storedSetup: the stored public files, and lines 1 to 4 at them.
  zeroKnowledgeWithLabel: zero knowledge with the request's label set beside each proof. It draws
  the hash function at random, as line 4 does. zeroKnowledgeWithLabel_of_atEveryRequest: it from
  zeroKnowledgeAtEveryRequest.
  completeWhereTheWorstCaseCheckPasses, completeWhereSomeWorstCaseCheckPasses: completeness at every
  prompt that fits a request, at weights that meet a stated condition. rejectsEmptyProof: the
  compiled verifier rejects the empty proof.
-/
import AtFullSide.CompletenessAndZeroKnowledge.RejectsTheEmptyForm
import AtFullSide.E2E.CompleteWhereSomeWorstCaseCheckPasses
import AtFullSide.E2E.CompleteWhereTheWorstCaseCheckPasses
import AtFullSide.Face.TheFinalStatementOneBitHolds
import AtFullSide.Face.FinalCompleteValue
import AtFullSide.Face.FinalBindingAtTheValue
import Johnson.Face.FinalSoundProof
import Johnson.Face.ExecutableVerifier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference
open VerifierAndGoals FlashProve VerifiableInference.AtEveryRequest VerifiableInference.Compilation AtPublicFiles.AtFiles
  AtPublicFiles.AtFiles.HonestTerm
open scoped ENNReal

/-- The public setup: three public files that a user holds beside the commitment, fixed before the
hash function is drawn: the parameter file (the model's sizes, the security settings and the
acceptance policy), the layout file and the scale file (the quantization scales; a fitted model's
are made from its weights). It fixes which model shape and which instance of the protocol is
meant. Only the scale file and five numbers of the parameter file are free. The verifier takes
them, at exact match, and they pass the test on the public files; other policies are not covered.
-/
structure PublicSetup where
  /-- The three public files. -/
  files : PublicFiles
  /-- What the reader returns at them. -/
  readParameters : Inst.Model.ScalesAndPolicy
  /-- They are in scope, read so, state exact match and pass the test. -/
  inUse : FilesInUse files readParameters

/-- flashProveAtFiles with its three arguments filled from the setup: what compile takes. It holds
the protocol, a linkable holographic IOP (an encoder and a decoder, an out-of-domain sample on each
encoding, and three IOPs: offline, link and online), with its layout into hash queries, its proof
format, and the honest provers and settings, which are one closed term. It holds a second, fixed
hash function, which is no random oracle. -/
def flashProve (setup : PublicSetup) : Compilable :=
  flashProveAtFiles setup.files (settingsOfRead setup.readParameters)
    (honestProversAndSettings setup.files (settingsOfRead setup.readParameters))

/-- The runs of the online IOP that one copy bears, which compile does not read. Nothing in the
prover counts them. -/
abbrev onlineRunsPerCopy (setup : PublicSetup) : ℕ :=
  (honestProversAndSettings setup.files (settingsOfRead setup.readParameters)).onlineRunsPerCopy

/-- **Soundness.** A provider that picks its public files after seeing the hash function is not
covered. Soundness itself needs only FilesTaken; the structure asks more for the other lines. -/
theorem sound (setup : PublicSetup) : Sound (compile (flashProve setup)) finalSoundnessError :=
  finalSound honestProversAndSettings setup.files setup.readParameters setup.inUse.toFilesTaken

/-- **Soundness and binding, with one extractor.** It holds whoever made the commitment, about the
weights, if any, that the extractor reads off it and its maker's hash queries; whose weights those
are, it does not say. -/
theorem soundAndBinding (setup : PublicSetup) :
    SoundAndBinding (compile (flashProve setup)) finalBindingError :=
  finalSoundAndBinding_value setup.files setup.readParameters setup.inUse

/-- **Completeness** as the general property CompleteOn (VerifiableInference/Steps.lean), at the
requests that can be served. Nothing is said of a request outside CanServe, among them those where
the model has no result, or of an output that is not the model's. -/
theorem completeOnCanServe (setup : PublicSetup) :
    CompleteOn (compile (flashProve setup)) (CanServe (settingsOfRead setup.readParameters))
      finalCompletenessError :=
  (served_at_T1 thePartsAt finalZeroKnowledgeError setup.files setup.readParameters setup.inUse
    (termLeft_value setup.files setup.readParameters setup.inUse)).1

/-- **Zero knowledge** on the requests that can be served and whose output tokens are the model's
(ZeroKnowledgeOn, VerifiableInference/MoreStatements.lean): its own simulator, which is handed
nothing of the weights in the experiment. It may depend on the public files; what these tell of
the weights is not counted. Whether a request can be served depends on the weights, and that is not
hidden: the chooser of requests may know the weights and is the same in both experiments. It says
nothing of a refused request by itself: with refusedHandsOutNoProof it gives
zeroKnowledgeAtEveryRequest, within the same bar, in which the simulator is told one bit for each
request: served or refused. One request to a proof and one commitment are covered, not batches. The
bound is not a named function: the statement says that there is one, and that it stays at or below
finalZeroKnowledgeError within the stated limits; ZeroKnowledgeOn takes it as an argument. -/
theorem zeroKnowledgeOnCanServe (setup : PublicSetup) :
    ∃ error : ℕ → ℕ → ℝ≥0∞,
      (∀ asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
        error asked replies ≤ finalZeroKnowledgeError) ∧
      ZeroKnowledgeOn (compile (flashProve setup))
        (CanServe (settingsOfRead setup.readParameters)) error :=
  (served_at_T1 thePartsAt finalZeroKnowledgeError setup.files setup.readParameters setup.inUse
    (termLeft_value setup.files setup.readParameters setup.inUse)).2

/-- **At a refused request every form that the prover can return is the empty form.** Nothing is
said of what a served request's proof shows. Proved more widely:
finalRefusedHandsOutNoProof_value. -/
theorem refusedHandsOutNoProof (setup : PublicSetup) :
    HandsOutNoProof (compile (flashProve setup))
      (fun weights request =>
        requestOutcome (settingsOfRead setup.readParameters) weights request = .refused)
      isNoProof :=
  finalRefusedHandsOutNoProof_value setup.files setup.readParameters setup.inUse.toFilesTaken

/-- **The replies fit**: each reply is one run of the online IOP, refused replies too, and one copy
bears as many runs as there are replies (finalReplyCount); the columns fit each table; and the
honest side stays within its budget. Nothing in the compiled prover counts the replies. -/
theorem repliesFit (setup : PublicSetup) :
    finalReplyCount ≤ onlineRunsPerCopy setup ∧
      (∀ reading, TableBudgetFits ((flashProve setup).settings reading).furtherCopies
        (onlineRunsPerCopy setup)) ∧
      WithinBudget (compile (flashProve setup)) honestQueryBudget :=
  repliesFit_value setup.files setup.readParameters setup.inUse

/-- **The Lean verifier**: the compiled verifier with BLAKE2b. It is a definition that cannot be
run: the command lean-verify runs an executable form of it: a second Lean text over the same
definitions of the protocol's data and decisions, proved to give the same verdict wherever the
commitment, the prompt and the output can be read off the user's files. -/
def leanVerifier (setup : PublicSetup) :
    Commitment → List Token → List Token → (compile (flashProve setup)).Proof → Bool :=
  (compile (flashProve setup)).accepts blake2bHash

/-- The Lean verifier is finalVerifierProgram, the value that the executable form computes. Nothing
is said here of a run of that form. -/
theorem leanVerifier_eq (setup : PublicSetup) (commitment : Commitment) (prompt output : List Token)
    (form : flashProveDescription.Form) :
    leanVerifier setup commitment prompt output form =
      finalVerifierProgram setup.files (settingsOfRead setup.readParameters) commitment prompt
        output form :=
  finalSystem_verifier_at_blake2b honestProversAndSettings setup.files (settingsOfRead setup.readParameters)
    commitment prompt output form

/-- **Completeness at a well-formed request whose result is its claimed output.** The line
completeOnCanServe is equivalent to it, by finalComplete_iff_completeOn. Nothing is said where the
model has no result or another result than the claimed output, or of a request that is not well
formed. -/
theorem completeAtWellFormedRequests (setup : PublicSetup) :
    ProofAcceptedWhere (compile (flashProve setup))
      (WellFormedRequest (settingsOfRead setup.readParameters))
      (modelResult (settingsOfRead setup.readParameters)) finalCompletenessError :=
  (finalComplete_iff_completeOn honestProversAndSettings setup.files setup.readParameters
    setup.inUse.toFilesTaken finalCompletenessError).2 (completeOnCanServe setup)

set_option maxHeartbeats 2000000 in
/-- At every honest part: zero knowledge on the requests that can be served, with the empty form at
every refused request, gives zero knowledge at every request, told the outcome, within the same
bar: zeroKnowledgeFollowsFromOn, with served_iff_canServe for the step from the one set of requests
to the other. -/
theorem zeroKnowledgeBelow_of_onCanServe (honest : HonestProversAndSettings) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (taken : FilesTaken files parameters) (bar : ℝ≥0∞)
    (onCanServe : ∃ error : ℕ → ℕ → ℝ≥0∞,
      (∀ asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
        error asked replies ≤ bar) ∧
      ZeroKnowledgeOn (finalSystem honest files (settingsOfRead parameters))
        (CanServe (settingsOfRead parameters)) error)
    (refused : HandsOutNoProof (finalSystem honest files (settingsOfRead parameters))
      (fun weights request => requestOutcome (settingsOfRead parameters) weights request = .refused)
      isNoProof) :
    ZeroKnowledgeBelowWhere (finalSystem honest files (settingsOfRead parameters)) (fun _ => True)
      (requestOutcome (settingsOfRead parameters)) finalVerifierQueries finalReplyCount bar := by
  obtain ⟨error, bounded, zeroKnowledge⟩ := onCanServe
  have refusedEmpty : HandsOutNoProof (finalSystem honest files (settingsOfRead parameters))
      (fun weights request => requestOutcome (settingsOfRead parameters) weights request = .refused)
      (· = noProofForm) :=
    fun weights randomness request hash form isRefused given =>
      refused weights randomness request hash form isRefused given
  refine ⟨error, bounded, ?_⟩
  exact zeroKnowledgeFollowsFromOn (finalSystem honest files (settingsOfRead parameters))
    (requestOutcome (settingsOfRead parameters)) noProofForm
    (finalServedIsModelOutput honest files parameters taken) refusedEmpty _
    (zeroKnowledgeOn_of_domain (fun weights prompt output served _ =>
      ((served_iff_canServe (valid_of_read taken.read) weights (prompt, output)).1 served).1)
      zeroKnowledge)

/-- **From the lines zeroKnowledgeOnCanServe and refusedHandsOutNoProof to zero knowledge at every
request**, within the same bar. -/
theorem zeroKnowledgeAtEveryRequest_of_lines (setup : PublicSetup)
    (onCanServe : ∃ error : ℕ → ℕ → ℝ≥0∞,
      (∀ asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
        error asked replies ≤ finalZeroKnowledgeError) ∧
      ZeroKnowledgeOn (compile (flashProve setup))
        (CanServe (settingsOfRead setup.readParameters)) error)
    (refused : HandsOutNoProof (compile (flashProve setup))
      (fun weights request =>
        requestOutcome (settingsOfRead setup.readParameters) weights request = .refused)
      isNoProof) :
    ZeroKnowledgeBelowWhere (compile (flashProve setup)) (fun _ => True)
      (requestOutcome (settingsOfRead setup.readParameters)) finalVerifierQueries finalReplyCount
      finalZeroKnowledgeError :=
  zeroKnowledgeBelow_of_onCanServe honestProversAndSettings setup.files setup.readParameters
    setup.inUse.toFilesTaken finalZeroKnowledgeError onCanServe refused

/-- **Zero knowledge at every request**, refused ones too, the simulator told one bit for each: the
request's outcome, served or refused. A corollary of zeroKnowledgeOnCanServe and
refusedHandsOutNoProof, by zeroKnowledgeAtEveryRequest_of_lines. The outcome depends on the weights
and is declared, not hidden; one request to a proof and one commitment are covered, not batches.
The simulator may depend on the public files; what these tell of the weights is not counted. That
this line gives zeroKnowledgeOnCanServe back is not proved. -/
theorem zeroKnowledgeAtEveryRequest (setup : PublicSetup) :
    ZeroKnowledgeBelowWhere (compile (flashProve setup)) (fun _ => True)
      (requestOutcome (settingsOfRead setup.readParameters)) finalVerifierQueries finalReplyCount
      finalZeroKnowledgeError :=
  zeroKnowledgeAtEveryRequest_of_lines setup (zeroKnowledgeOnCanServe setup)
    (refusedHandsOutNoProof setup)

/-- The stored public files, storedPublicFiles, in use; storedParameters is what they read as,
picked by choice. That these are the files that ship is not said here. -/
def storedSetup : PublicSetup := ⟨storedPublicFiles, storedParameters, filesInUse_stored⟩

/-- **Soundness, at the stored files.** The bound at q queries is about q / 2^124 + 2^-101. -/
theorem sound_stored : Sound (compile (flashProve storedSetup)) finalSoundnessError :=
  sound storedSetup

/-- **Soundness and binding, at the stored files.** The bound at q queries is about
q / 2^124 + 2^-100. -/
theorem soundAndBinding_stored :
    SoundAndBinding (compile (flashProve storedSetup)) finalBindingError :=
  soundAndBinding storedSetup

/-- **Completeness, at the stored files**, on the requests that can be served, with failure at most
2^-40. -/
theorem complete_stored :
    CompleteOn (compile (flashProve storedSetup))
      (CanServe (settingsOfRead storedSetup.readParameters)) finalCompletenessError :=
  completeOnCanServe storedSetup

/-- **Zero knowledge, at the stored files**, on the requests that can be served, at or below
2^-154. -/
theorem zeroKnowledge_stored :
    ∃ error : ℕ → ℕ → ℝ≥0∞,
      (∀ asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
        error asked replies ≤ finalZeroKnowledgeError) ∧
      ZeroKnowledgeOn (compile (flashProve storedSetup))
        (CanServe (settingsOfRead storedSetup.readParameters)) error :=
  zeroKnowledgeOnCanServe storedSetup

/-! ## Each proof beside the request's label -/

/-- **Zero knowledge with the label shown follows from zeroKnowledgeAtEveryRequest's statement**, at
the same files and the same error: a simulator told the label can work out the request's outcome.
This line gives no bound of its own: its error is the one that it is handed. -/
theorem zeroKnowledgeWithLabel_of_atEveryRequest (setup : PublicSetup) (error : ℝ≥0∞)
    (toldTheOutcome : ZeroKnowledgeBelowWhere (compile (flashProve setup)) (fun _ => True)
      (requestOutcome (settingsOfRead setup.readParameters)) finalVerifierQueries finalReplyCount
      error) :
    ZeroKnowledgeShownBelowWhere (compile (flashProve setup))
      (WellFormedRequest (settingsOfRead setup.readParameters))
      (requestLabel (settingsOfRead setup.readParameters)) finalVerifierQueries finalReplyCount
      error :=
  zeroKnowledgeAtFiles_of_oneBit honestProversAndSettings error setup.files setup.readParameters toldTheOutcome

/-- **Zero knowledge with the label shown**, at well-formed requests: each proof stands beside the
request's label (served, failed or other tokens), and the simulator is told that label. The
compiled prover does not emit the label: the property sets it beside each proof (labelled). The
label depends on the weights and is declared, not hidden; it tells more than the bit of
zeroKnowledgeAtEveryRequest, and no verifier checks it; no statement bounds what many labels reveal
together. A request that is not well formed is not covered; one request to a proof and one
commitment are covered, not batches. The simulator may depend on the public files; what these tell
of the weights is not counted. -/
theorem zeroKnowledgeWithLabel (setup : PublicSetup) :
    ZeroKnowledgeShownBelowWhere (compile (flashProve setup))
      (WellFormedRequest (settingsOfRead setup.readParameters))
      (requestLabel (settingsOfRead setup.readParameters)) finalVerifierQueries finalReplyCount
      finalZeroKnowledgeError :=
  zeroKnowledgeWithLabel_of_atEveryRequest setup finalZeroKnowledgeError
    (zeroKnowledgeAtEveryRequest setup)

/-! ## Completeness at every prompt, and the empty proof -/

/-- **Completeness at every prompt, at weights that pass the worst-case check.** For a prompt that
is not empty, with its tokens in the vocabulary, and a length of at least 1 that fits with it into
1,025 tokens, exactly one output of that length is the model's own, and at that request the honest
proof is rejected with probability at most finalCompletenessError. It covers no request that the
line completeOnCanServe does not cover: the check adds that such a request exists at every such
prompt and length: every prompt, not every request. Weights that do not pass are not covered, and
nothing is said of a request whose claimed output is not the model's own. The check is this
library's own, sufficient and not necessary: weights that do not pass may still never fail, and no
theorem here relates it to a check that any program makes. Shown to pass: made-up weights only (all
zeros, at every public setup; at the stored files, all weights whose layers' matrices have every
entry in -200 .. 200); no theorem says that a real model's converted weights pass, and nothing in a
commitment, a proof or the verifier shows that the committed weights do. -/
theorem completeWhereTheWorstCaseCheckPasses (setup : PublicSetup)
    (weights : ModelWeights (settingsOfRead setup.readParameters))
    (passes : PassesWorstCaseCheck (settingsOfRead setup.readParameters) weights)
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead setup.readParameters).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ output : List Token, output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead setup.readParameters) weights prompt output ∧
      (∀ other : List Token, other.length = length →
        IsTheModelsOwnOutput (settingsOfRead setup.readParameters) weights prompt other →
          other = output) ∧
      HonestProofRejectedAtMost (compile (flashProve setup)) weights (prompt, output)
        finalCompletenessError :=
  theHonestPart_complete_where_the_worst_case_check_passes setup.files setup.readParameters
    setup.inUse weights passes prompt length notEmpty inVocabulary positive fits

/-- **The same, at weights that pass the first worst-case check, or the least-bound check with
numbers that hold.** The second arm says that such numbers exist: a statement, not a test. Weights
that pass neither are not covered, and nothing is said of a request whose claimed output is not
the model's own. The checks are sufficient, not necessary, and this library's own. Shown to meet
the second arm: at the stored files, all weights whose layers' matrices have every entry in
-800 .. 800, made up too; of a real model's weights nothing is shown. -/
theorem completeWhereSomeWorstCaseCheckPasses (setup : PublicSetup)
    (weights : ModelWeights (settingsOfRead setup.readParameters))
    (passes : PassesSomeWorstCaseCheck (settingsOfRead setup.readParameters) weights)
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead setup.readParameters).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ output : List Token, output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead setup.readParameters) weights prompt output ∧
      (∀ other : List Token, other.length = length →
        IsTheModelsOwnOutput (settingsOfRead setup.readParameters) weights prompt other →
          other = output) ∧
      HonestProofRejectedAtMost (compile (flashProve setup)) weights (prompt, output)
        finalCompletenessError :=
  theHonestPart_complete_where_some_worst_case_check_passes setup.files setup.readParameters
    setup.inUse weights passes prompt length notEmpty inVocabulary positive fits

/-- **The compiled verifier rejects the empty proof**, at every hash function, commitment, prompt
and output. Nothing is said of whether a served request's proof is empty, and an empty proof does
not show that the request was refused. Proved at all public files and settings:
rejectsNoProof_value. -/
theorem rejectsEmptyProof (setup : PublicSetup) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) :
    ((compile (flashProve setup)).verify commitment prompt output noProofForm).evaluate hash =
      false :=
  rejectsNoProof_value setup.files (settingsOfRead setup.readParameters) hash commitment prompt
    output

end VerifiableInference

#print axioms VerifiableInference.completeOnCanServe
#print axioms VerifiableInference.zeroKnowledgeOnCanServe
#print axioms VerifiableInference.completeAtWellFormedRequests
#print axioms VerifiableInference.zeroKnowledgeBelow_of_onCanServe
#print axioms VerifiableInference.zeroKnowledgeAtEveryRequest_of_lines
#print axioms VerifiableInference.zeroKnowledgeAtEveryRequest
#print axioms VerifiableInference.storedSetup
#print axioms VerifiableInference.sound_stored
#print axioms VerifiableInference.soundAndBinding_stored
#print axioms VerifiableInference.complete_stored
#print axioms VerifiableInference.zeroKnowledge_stored
#print axioms VerifiableInference.PublicSetup
#print axioms VerifiableInference.flashProve
#print axioms VerifiableInference.onlineRunsPerCopy
#print axioms VerifiableInference.sound
#print axioms VerifiableInference.soundAndBinding
#print axioms VerifiableInference.refusedHandsOutNoProof
#print axioms VerifiableInference.repliesFit
#print axioms VerifiableInference.leanVerifier
#print axioms VerifiableInference.leanVerifier_eq
#print axioms VerifiableInference.zeroKnowledgeWithLabel
#print axioms VerifiableInference.zeroKnowledgeWithLabel_of_atEveryRequest
#print axioms VerifiableInference.completeWhereTheWorstCaseCheckPasses
#print axioms VerifiableInference.completeWhereSomeWorstCaseCheckPasses
#print axioms VerifiableInference.rejectsEmptyProof

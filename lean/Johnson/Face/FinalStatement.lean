-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalStatement.lean: the final statements: flashProveAtFiles, compiled.

  Sound (compile flashProveAtFiles) finalSoundnessError
  SoundAndBinding (compile flashProveAtFiles) finalBindingError
  ProofAcceptedWhere (compile flashProveAtFiles) WellFormedRequest modelResult finalCompletenessError
  ZeroKnowledgeShownBelowWhere (compile flashProveAtFiles) WellFormedRequest requestLabel (2^64) 688127
    zeroKnowledgeError
  FinalHandsOutNoProof: the reply is the word of requestLabel beside the prover's form, which outside
    served holds no proof
  RepliesFit: numbers that the proof of zero knowledge reads: the replies are at most a stated number
    of sessions a copy, at which the opened columns fit each table; and the honest side stays within
    2^48 queries. Nothing in the compiled prover counts
  finalVerifierProgram: (compile flashProveAtFiles).verify at BLAKE2b
    (finalSystem_verifier_at_blake2b, verdictOf_eq_finalVerifierProgram)

What is proved of each line is on the audit page, which goes with these files.

flashProveAtFiles here is the protocol at the public files, with the model's settings read off them and
an honest part as an argument. The part of which the lines are meant is honestProversAndSettings
(AtFullSide/Face/HonestProversAndSettingsValue.lean), which holds named stand-in values for cases that shouldn't
arise at the files in use, and three numbers fixed at the full-size files' sizes. finalSound holds at
every honest part.

The hash function is no argument of compile: the lines on soundness, binding, completeness and zero
knowledge draw it at random, so they are statements in the random-oracle model, and
finalVerifierProgram plugs BLAKE2b in. A second, fixed hash function, made
of BLAKE2b's compression function with another counter, stands inside the protocol's description in
all of them: that one is no random oracle.
finalSoundnessError q = 16 (q + 1 + 2^23) / 2^128 + (q + 2^23 + 3)^2 / 2^256, about q / 2^124 + 2^-101.
finalBindingError q = max (soundnessErrorInQueries q 2^23) (bindingErrorInQueries q), about q / 2^124 + 2^-100 (in the binding line
the parser's queries are allowed 2^23, in the soundness line 1; the rate is the same).
finalCompletenessError = 2^-40. zeroKnowledgeError is a parameter.

 1. flashProveAtFiles is what compile takes, at public files and settings of the model: it holds the protocol
    and the format of bytes on which the Lean verifier runs, and takes the provers.
 2. finalSystem is flashProveAtFiles, compiled: one argument system, with no public parameters, of which all
    the lines speak; in zero knowledge the verifier is also shown the word beside each proof.
 3. Sound: under a random hash function, an output that is not that of the weights that an extractor
    reads off the commitment and the committer's queries is rarely accepted; q counts the committer's
    and the prover's queries.
 4. A well-formed request: its tokens are in the vocabulary, neither list is empty, and together they
    have at most 1,025 tokens.
 5. Complete: for one commitment and one well-formed request, if the model's result is the claimed
    tokens, the honest proof is accepted, except with probability at most 2^-40.
 6. The result is read on the zero-filled window, the claimed tokens and the padding after them
    included. The word is served at that case, failed where the window has no value, and other tokens
    where the result is others; so a true output can be told failed on account of the padding.
 7. ZeroKnowledge: a simulator that may depend on the public files and is told, of each well-formed
    request, only the word makes the commitment, the replies and the hash answers; for one commitment,
    up to so many replies and queries, its view is within the error of the real one. What that hides is
    as good as the number. The compiled prover's own proofs show two forms, a proof or the empty form;
    the statement declares three values because the reply shows the word; the one-bit statement at
    compile flashProveAtFiles is the stronger one and stands beneath, with the same statement at every
    request, where an ill-formed request is told other tokens, from the request alone.
 8. One request to a proof; batches are a further statement, though the programs serve batches. The
    prover keeps no state: it draws its copy at random, nothing counts the replies, and all its coins
    are fresh and uniform.
 9. One commitment; nothing on what is published beside it, or on what the public files tell.
10. The files are those that the verifier takes, at the exact-match policy: the output must be the
    model's; a release that serves under another policy is outside these lines. All but Sound and the
    reply also ask the test on the public files that gates the verifier.
-/
import Johnson.Face.Compiler
import VerifiableInference.AtEveryRequest
import VerifiableInference.WellFormedRequests
import VerifiableInference.RequestLabel
import VerifiableInference.Labelled
import VerifiableInference.Bridge
import Johnson.FrontRoad.AtBuiltNamed
import Johnson.Goal.Conditions.HonestAtDescriptionDataAtFiles
import Johnson.FrontRoad.RangeOf
import Johnson.Prover.Print.Form
import Ladder.PackageBits
import E2E.PremisesAtFiles
import Johnson.Top.Fire.Code.FastFamProbe

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve VerifiableInference.OnPublicFiles OnBytes.FrontRoad OnBytes.WholeKey
open TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.AtEveryRequest (Label Request requestLabel modelResult WellFormedRequest
  WithinBudget ProofAcceptedWhere ZeroKnowledgeShownBelowWhere)
open IntegerTransformer (Settings)
open scoped ENNReal

/-! ## 1. flashProveAtFiles -/

/-- flashProveAtFiles's public side, at public files and settings. -/
def flashProvePublic (files : PublicFiles) (settings : Settings) : PublicSide :=
  ofDescription flashProveDescription files settings (backThe files settings)

/-- flashProveAtFiles's wiring, with the instance that stands where a request builds none. -/
def flashProveWiring (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X) :
    CompilerWiring (flashProvePublic files settings) :=
  wiringOf flashProveDescription files settings (backThe files settings) allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
    Prod.mk (familyLaws_the files).eq fallbackInstance

/-- The form that holds no proof: five empty parts. -/
def noProofForm : FlashProve.FormBytes := ⟨[], .empty, .empty, .empty, .empty, .empty⟩

/-- A form holds no proof. -/
def isNoProof (form : FlashProve.FormBytes) : Prop := form = noProofForm

/-- The writer of the three files, at the letters of one set of public files; where a proof string is
missing, an empty form. -/
def bytesWriterAt {Zk : OnBytes.K.Pub} (S : FlashProve.DescriptionDataAtFiles Zk) : S.Typed → FlashProve.FormBytes
  | (aux, ⟨cm, rcd⟩, ⟨copy, some keyProof, (cm', rcd', some linkProof), some sessionProof⟩) =>
      Johnson.Prover.Print.formOf S
        ⟨aux, cm, rcd, copy, keyProof, cm', rcd', linkProof, sessionProof⟩
  | _ => noProofForm

/-- The writer of the three files. -/
def bytesWriter (files : PublicFiles) :
    TypedProof ((flashProveDescription.F files).withProvers (flashProveDescription.P files)) (flashProveDescription.F files).annT (flashProveDescription.F files).annL → flashProveDescription.Form :=
  bytesWriterAt (FlashProve.dataAtFiles flashProveData files)

/-- The honest part of flashProveAtFiles at public files and settings. -/
structure HonestProversAndSettingsAtFiles (files : PublicFiles) (settings : Settings) where
  /-- The instance that stands where a request builds none. -/
  fallbackInstance : (flashProveDescription.C files).X
  /-- The honest provers. -/
  provers : HonestProvers ((flashProveDescription.F files).withProvers (flashProveDescription.P files))
  /-- What the honest side chooses beside them, at each value of the public reading. -/
  compiledSettings : (reading : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D) →
    CompiledSettings ((flashProveWiring files settings fallbackInstance).layoutAtReading reading)
      provers
  /-- The honest committer samples one number from 0 to this. -/
  coinBound : ℕ
  /-- The sessions that one copy bears: a number that compile does not read. -/
  onlineRunsPerCopy : ℕ

/-- The test on first hash blocks at public files: a try of a search is asked whole only if its first
block passes. -/
abbrev flashFirstBlockTest (files : PublicFiles) : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D →
    Rom.More (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (flashProveDescription.input files allZeroDigest []).queryLayout.K
      (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier (flashProveDescription.input files allZeroDigest []).protocol
        (flashProveDescription.input files allZeroDigest []).LeafBody (flashProveDescription.input files allZeroDigest []).offlineRoundSplits (flashProveDescription.input files allZeroDigest []).linkRoundSplits)) 256 :=
  fun _ => OnBytes.Prover.moreP (FlashProve.firstBlockTestAtDescriptionData (FlashProve.dataAtFiles flashProveData files) allZeroDigest [])

/-- **flashProveAtFiles.** -/
def flashProveAtFiles (files : PublicFiles) (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings) :
    Compilable where
  publicSide := flashProvePublic files settings
  wiring := flashProveWiring files settings honest.fallbackInstance
  provers := honest.provers
  settings := honest.compiledSettings
  firstBlockTest := flashFirstBlockTest files
  coinBound := honest.coinBound
  format := formatOf flashProveDescription files flashProveDescription.Form (flashProveDescription.parse files) (bytesWriter files)

/-- The test on first hash blocks lets through all that the honest side's runs read: it is what the
theorems on hiding and completeness ask of the search's early exit. -/
def FirstBlockFits (files : PublicFiles) (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings) :
    Prop :=
  FactorsAt (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
    (fun reading => (honestSide
      ((flashProveWiring files settings honest.fallbackInstance).layoutAtReading reading)
      honest.provers (honest.compiledSettings reading)).side)
    (flashFirstBlockTest files)

/-- The honest part at every set of public files and settings. -/
abbrev HonestProversAndSettings := (files : PublicFiles) → (settings : Settings) → HonestProversAndSettingsAtFiles files settings

/-- **The final system.** -/
abbrev finalSystem (honest : HonestProversAndSettings) (files : PublicFiles) (settings : Settings) : ArgumentSystem :=
  compile (flashProveAtFiles files settings (honest files settings))

/-- **The verifier of the final system.** It reads no honest part. -/
def finalVerifier (files : PublicFiles) (settings : Settings) :
    Commitment → List Token → List Token → flashProveDescription.Form → DeterministicAlgorithm Bool :=
  compiledVerifier (flashProvePublic files settings) (flashProveDescription.parse files)

/-- The final verifier is VerifierAndGoals.verify, at the description of the soundness theorem. -/
theorem finalVerifier_eq (files : PublicFiles) (settings : Settings) :
    finalVerifier files settings = verify flashProveDescription files (flashProveDescription.parse files) :=
  compiledVerifier_eq_verify flashProveDescription files settings (backThe files settings) flashProveDescription.Form (flashProveDescription.parse files)

/-- compile flashProveAtFiles's verifier is VerifierAndGoals.verify, at the description of the soundness theorem
(theDescription_eq). -/
theorem compile_flashProve_verify_eq (files : PublicFiles) (settings : Settings)
    (honest : HonestProversAndSettingsAtFiles files settings) :
    (compile (flashProveAtFiles files settings honest)).verify = verify flashProveDescription files (flashProveDescription.parse files) :=
  compile_verify flashProveDescription files settings (backThe files settings) allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq
    honest.fallbackInstance honest.provers
    honest.compiledSettings (flashFirstBlockTest files) honest.coinBound flashProveDescription.Form
    (flashProveDescription.parse files) (bytesWriter files)

/-- The verifier of compile flashProveAtFiles is the final verifier: no honest part reaches it. -/
theorem compile_flashProve_verify (files : PublicFiles) (settings : Settings)
    (honest : HonestProversAndSettingsAtFiles files settings) :
    (compile (flashProveAtFiles files settings honest)).verify = finalVerifier files settings := rfl

/-- Sound of compile flashProveAtFiles is Sound of the verifier's own system at the description, whatever
the honest part. -/
theorem compile_flashProve_sound_iff (files : PublicFiles) (settings : Settings)
    (honest : HonestProversAndSettingsAtFiles files settings) (ε : ℕ → ℝ≥0∞) :
    Sound (compile (flashProveAtFiles files settings honest)) ε ↔
      Sound (systemOfRecord flashProveDescription files settings) ε :=
  compile_sound_iff flashProveDescription files settings (backThe files settings) allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq
    honest.fallbackInstance honest.provers
    honest.compiledSettings (flashFirstBlockTest files) honest.coinBound flashProveDescription.Form
    (flashProveDescription.parse files) (bytesWriter files) (flashProveDescription.prove files settings) ε

/-! ## 2. The numbers -/

/-- The bound on completeness: 2 ^ -40. -/
abbrev finalCompletenessError : ℝ≥0∞ := completenessErrorBound

/-- The honest side's budget: 2 ^ 48 queries. -/
abbrev honestQueryBudget : ℕ := honestBudget

/-- The bound on soundness, for an adversary with queries queries to the hash function. -/
abbrev finalSoundnessError (queries : ℕ) : ℝ≥0∞ := soundnessErrorInQueries queries 1

/-- The bound on binding, for an adversary with queries queries to the hash function. -/
abbrev finalBindingError (queries : ℕ) : ℝ≥0∞ := levelError queries

/-- The verifier's queries up to which the bound on zero knowledge is asked. -/
abbrev finalVerifierQueries : ℕ := queryBudget

/-- The replies under one commitment up to which the bound on zero knowledge is asked. -/
abbrev finalReplyCount : ℕ := 688127

/-! ## 3. The top lines -/

/-- The public files of the top lines: the verifier takes them, they read as parameters, and their
policy is that the output must be the model's, token for token. -/
structure FilesTaken (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop where
  inScope : InScope files = true
  read : readFiles files = .ok parameters
  exactMatch : parameters.pol = Inst.Model.AcceptancePolicy.exact

/-- The same, and they pass the test `protocolDataWellFormed` on the public files. -/
structure FilesInUse (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop extends
    FilesTaken files parameters where
  pass : protocolDataWellFormed (asDescriptionFiles files) = true

/-- Soundness at given files. -/
def SoundAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  Sound (finalSystem honest files (settingsOfRead parameters)) finalSoundnessError

/-- **Soundness.** -/
def FinalSound (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesTaken files parameters →
    SoundAtFiles honest files parameters

/-- Completeness at given files, at every well-formed request. -/
def CompleteAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  ProofAcceptedWhere (finalSystem honest files (settingsOfRead parameters))
    (WellFormedRequest (settingsOfRead parameters)) (modelResult (settingsOfRead parameters))
    finalCompletenessError

/-- **Completeness**, at every well-formed request. -/
def FinalComplete (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    CompleteAtFiles honest files parameters

/-- Zero knowledge at given files, at every well-formed request, within an error. -/
def ZeroKnowledgeAtFiles (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  ZeroKnowledgeShownBelowWhere (finalSystem honest files (settingsOfRead parameters))
    (WellFormedRequest (settingsOfRead parameters)) (requestLabel (settingsOfRead parameters))
    finalVerifierQueries finalReplyCount zeroKnowledgeError

/-- **Zero knowledge**, at every well-formed request, within an error. An error says something only
as a number: at 1/2 a prover that sends one bit of the weights meets it. -/
def FinalZeroKnowledge (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    ZeroKnowledgeAtFiles honest zeroKnowledgeError files parameters

/-- Binding at given files, with soundness, of the same committer. -/
def BindingAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  SoundAndBinding (finalSystem honest files (settingsOfRead parameters)) finalBindingError

/-- **Binding**, with soundness, of the same committer. -/
def FinalSoundAndBinding (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    BindingAtFiles honest files parameters

/-- The reply at given files: at every request its word is requestLabel's, and outside served the
form beside it holds no proof. -/
def ReplyAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  ∀ (weights : ModelWeights (settingsOfRead parameters))
    (randomness : (finalSystem honest files (settingsOfRead parameters)).CommitmentRandomness)
    (request : Request) (hash : Hash) (answer : Label × flashProveDescription.Form),
    (reply (finalSystem honest files (settingsOfRead parameters))
        (requestLabel (settingsOfRead parameters)) weights randomness request.1 request.2).run
        hash answer ≠ 0 →
      answer.1 = requestLabel (settingsOfRead parameters) weights request ∧
        (answer.1 ≠ .served → isNoProof answer.2)

/-- **The reply**, at every request. -/
def FinalHandsOutNoProof (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesTaken files parameters →
    ReplyAtFiles honest files parameters

/-- The columns that the proofs open fit each table's budget of 44,040,191 (`AtPublicFiles.Premises.indexPrivacyNumbers`):
on the first table the offline proof's and one link's for each copy, on a copy its link's and its
sessions'. No link hangs on a copy but the one that made it. -/
def TableBudgetFits (furtherCopies onlineRunsPerCopy : ℕ) : Prop :=
  (AtPublicFiles.Premises.indexPrivacyNumbers onlineRunsPerCopy 0 0 0 0 0 0).qT +
      (furtherCopies + 1) * (AtPublicFiles.Premises.indexPrivacyNumbers onlineRunsPerCopy 0 0 0 0 0 0).qpar ≤
    (AtPublicFiles.Premises.indexPrivacyNumbers onlineRunsPerCopy 0 0 0 0 0 0).b ∧
  (AtPublicFiles.Premises.indexPrivacyNumbers onlineRunsPerCopy 0 0 0 0 0 0).qch +
      (AtPublicFiles.Premises.indexPrivacyNumbers onlineRunsPerCopy 0 0 0 0 0 0).s1 *
        (AtPublicFiles.Premises.indexPrivacyNumbers onlineRunsPerCopy 0 0 0 0 0 0).qon ≤
    (AtPublicFiles.Premises.indexPrivacyNumbers onlineRunsPerCopy 0 0 0 0 0 0).b

/-- The replies fit at given files: one copy's sessions bear them, since the prover draws its copy at
random and counts nothing; the columns fit each table; and the honest side stays within its budget. -/
def RepliesFitAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  finalReplyCount ≤ (honest files (settingsOfRead parameters)).onlineRunsPerCopy ∧
    (∀ reading, TableBudgetFits
      ((honest files (settingsOfRead parameters)).compiledSettings reading).furtherCopies
      (honest files (settingsOfRead parameters)).onlineRunsPerCopy) ∧
    WithinBudget (finalSystem honest files (settingsOfRead parameters)) honestQueryBudget

/-- **The replies fit.** -/
def RepliesFit (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    RepliesFitAtFiles honest files parameters

/-- **The final statement**, of one honest part within one error on zero knowledge. The part of which it
is meant is honestProversAndSettings (AtFullSide/Face/HonestProversAndSettingsValue.lean). The format's second hash function, a fixed public
function inside the description, is no random oracle. -/
structure FinalStatement (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) : Prop where
  sound : FinalSound honest
  complete : FinalComplete honest
  zeroKnowledge : FinalZeroKnowledge honest zeroKnowledgeError
  binding : FinalSoundAndBinding honest
  handsOutNoProof : FinalHandsOutNoProof honest
  repliesFit : RepliesFit honest

/-- BLAKE2b, under the format's parser of queries. -/
abbrev blake2bHash : Hash := hashOf _root_.Fmt.oracle

/-- The final verifier at BLAKE2b: the value that the executable form computes. It reads no honest
part. -/
def finalVerifierProgram (files : PublicFiles) (settings : Settings) (commitment : Commitment)
    (prompt output : List Token) (form : flashProveDescription.Form) : Bool :=
  (finalVerifier files settings commitment prompt output form).evaluate blake2bHash

end VerifiableInference.Compilation

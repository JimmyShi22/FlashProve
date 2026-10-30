-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InnerCompiledVerifier.lean: soundness of the argument system made from an object with records by
the compiled verifier of Johnson/TypedOracleCompiler/RecCompile/, under named hypotheses on its three protocols.

Definitions, two structures of hypotheses, and theorems with their proofs. This is
Johnson/Top/OnFilesAt.lean over the compiled verifier with a record
(Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean, FrontRootAns.lean): the key file's and the entry file's
protocols have marks of their own; each call has its own depth of the request tree; the first
queries' lists hold the roots and the code of the records' ANSWERS, not their seeds; both seeds are
drawn under one tag by two nested queries and compared at every call; a part of an instance may be
named late.
What the verifier reads and what the theorems need beside it are two records.
Main names (namespace `VerifiableInference.OnPublicFiles`):
  `InnerCompilerInput`: what `innerCompiledVerifier` reads: the object, the marks, the wires, the coding of the typed
    oracles in one hash function, the code of a key, how an instance is built; the model; the
    honest committer and prover.
  `SoundnessAnalysisData r`: what the hypotheses and the theorems name beside: the relaxed relation; the
    extractor behind the commitment and its stated cost; an instance; the stated bound on a round's
    error.
  `schemeOverTypedOracles r`, `innerSystem r`, `innerCompiledVerifier r`; `compiledIndexExtractor b`, `compiledSoundnessError b`.
  `CompilerSoundnessConditionStatements.‹name› b`: the named hypotheses, one definition each, with one sentence each.
  `CompilerSoundnessConditions b`: the 15 hypotheses that name no claim. `CompilerSoundnessConditionsWithMeaning b`: these and `CompilerSoundnessConditionStatements.sound b`.
  `CompilerSoundnessConditions.binds`: index binding of `schemeOverTypedOracles r`.
  `innerCompiledVerifier_soundFor`, `innerCompiledVerifier_sound`: `SoundForWith` for a claim; for "the output tokens are
    the model's".
Limits: those of Johnson/Top/OnFilesAt.lean, read here. No object is given, and none is shown to
  meet `CompilerSoundnessConditionsWithMeaning b`. No hypothesis says that εs is small, or that `innerCompiledVerifier r` accepts anything.
  `r.oracleCoding`, `r.queryLayout` and `r.protocol` hold laws and instances in their types. The hash function is one random
  function with 256-bit answers. `CompilerSoundnessConditionStatements.wires` asks an exactly uniform verifier message of every
  round: to meet it an object must have blocks of digests for messages. No field names bits of
  proof of work: the three hypotheses on soundness bound every round's error of the object as it
  stands, so where an error is small only with its work counted, the object's rounds must hold
  that work (nonce and test). If `buildInstance` itself refuses every output that is not the model's,
  `CompilerSoundnessConditionStatements.sound` holds whatever the relation is, and the theorems say nothing on the protocol.
  That the typed queries are the strings that a program hashes is not said here.
  Does not say: completeness; zero knowledge; that the extractor returns an honest committer's
  index.

-/
import Johnson.TypedOracleCompiler.RecCompile.FrontRootAns
import Johnson.Top.FrontCommit
import Johnson.Top.BlocksOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What `innerCompiledVerifier` reads; the model; the honest side's algorithms. -/
structure InnerCompilerInput where
  /-- Indices. -/
  Index : Type
  /-- Instances. -/
  Instance : Type
  /-- The protocol: three IOPs (offline, link, online), the encoder and decoder of an index, the
  out-of-domain sample, and which part of an instance is named early and which late. -/
  protocol : HolographicProtocol Index Instance
  /-- What a query's body may hold beside. -/
  LeafBody : Type
  /-- The offline IOP's marks: which rounds are shared, which are a chain's own. -/
  offlineRoundSplits : RoundSplits protocol.offline.shape
  /-- The link IOP's marks. -/
  linkRoundSplits : RoundSplits protocol.link.shape
  /-- The wire of the protocol: how rounds and openings are laid into hash queries. -/
  queryLayout : QueryLayout 256 (typedOracleCarrier protocol LeafBody offlineRoundSplits linkRoundSplits)
  /-- The wire of the out-of-domain sample: the seeds' two queries, the stored copy's number. -/
  seedQueries : OutOfDomainSampleQueryLayout 256 queryLayout.K protocol LeafBody offlineRoundSplits linkRoundSplits
  /-- How an out-of-domain sample's answers are written as a list of digests. -/
  answerCode : protocol.OutOfDomainAnswer → List (Dig 256)
  /-- A fixed out-of-domain sample: it fills the two places for one in a run's first query. -/
  fixedSample : protocol.Rec
  compilerParameters : Params
  /-- The typed oracles in one hash function. -/
  oracleCoding : OracleCoding (typedOracleFamily 256 queryLayout.K (typedOracleCarrier protocol LeafBody offlineRoundSplits linkRoundSplits)) 256
  /-- The code of a key: the hash function's answer at it is the commitment. -/
  keyCode : KeyRoot 256 protocol → Option ZKCP.Str
  /-- From a prompt with output tokens, and further tokens that the proof brings, an instance. -/
  buildInstance : List Token × List Token → List Token → Option Instance
  /-- The model. `innerCompiledVerifier` does not read it; the claim does. -/
  nextToken : Index → List Token → Option Token
  /-- The honest side. Nothing is asked of these five, nor of the honest provers that `protocol` holds. -/
  ProverKey : Type
  commit : Index → Rom.OComp (typedOracleFamily 256 queryLayout.K (typedOracleCarrier protocol LeafBody offlineRoundSplits linkRoundSplits)) (KeyRoot 256 protocol × ProverKey)
  prove : ProverKey → (b : List (Instance × Unit)) →
    Rom.OComp (typedOracleFamily 256 queryLayout.K (typedOracleCarrier protocol LeafBody offlineRoundSplits linkRoundSplits)) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 protocol offlineRoundSplits linkRoundSplits) b)
  coinBound : ℕ
  fallbackProof : KeyRoot 256 protocol × OfflineLinkOnlineProof 256 protocol offlineRoundSplits linkRoundSplits

/-- What the hypotheses and the theorems name beside the input. `innerCompiledVerifier` reads none of it. -/
structure SoundnessAnalysisData (r : InnerCompilerInput) where
  /-- Witnesses. -/
  Wn : Type
  /-- The relaxed relation. -/
  Rno : r.Index → r.Instance → Wn → Prop
  /-- The extractor behind the commitment. For the index it reads the commitment and the
  committer's query log. -/
  ext : ZKCP.Extractor 256 r.Index r.Instance Unit (ZKCP.Digest 256)
    (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits)
  /-- The stated cost of the commitment, in the sum of the two bounds on queries. -/
  εId : ℕ → ℝ≥0∞
  /-- Any instance. -/
  x₀ : r.Instance
  /-- The stated bound on a round's error. -/
  εs : ℝ≥0∞

variable (r : InnerCompilerInput)

/-- The scheme. Its verifier is the compiled verifier with a record, the key being the root and the
record. -/
def schemeOverTypedOracles : ZKCP.Gen.Arg (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Index r.Instance Unit
    (KeyRoot 256 r.protocol) r.ProverKey (OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) :=
  ⟨r.commit, r.prove, verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters⟩

/-- The argument system made from the input. -/
def innerSystem : ArgumentSystem :=
  Rec.tokenArgumentSystem (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r)) r.keyCode r.coinBound r.buildInstance r.fallbackProof r.nextToken

/-- The verifier. -/
def innerCompiledVerifier := (innerSystem r).verify

variable {r} (b : SoundnessAnalysisData r)

/-- The named extractor. It reads the commitment and the committer's query log alone. -/
def compiledIndexExtractor : Commitment → QueryLog → Option r.Index :=
  (b.ext.buildInstance : ZKCP.Extractor 256 r.Index (List Token × List Token) Unit (ZKCP.Digest 256)
    (List Token × (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits))).Ei

/-- The bound, in t, the sum of the bounds on the committer's and the prover's queries to the hash
function: n · εs + 2 (n + 1)² / 2^256 + εId t with n = 5 (t + tVC + 1), where tVC bounds the typed
queries of the compiled verifier. The factor 5 covers an analysis in which up to four queries for
seeds are laid in before a query: they are laid in before a chain's first query alone; the count
allows for every query. -/
def compiledSoundnessError : ℕ → ℝ≥0∞ :=
  fun t => soundnessBoundOverTypedOracles r.queryLayout b.εs t 0 + b.εId t

/-- An instance is true at an index: some witness meets the relaxed relation. -/
def HasRelaxedRelationWitness (i : r.Index) (x : r.Instance) : Prop := ∃ w, b.Rno i x w

/-! ## The named hypotheses -/

namespace CompilerSoundnessConditionStatements

/-- The decoder gives no index at a word and a record at whose seed the word has a collision. -/
def noneColl : Prop := ∀ y (rec : r.protocol.Rec), r.protocol.hasCollisionAt y rec.1 → r.protocol.decodeIndex y rec = none
/-- Key file: its protocol is round-by-round sound for "the word has a collision at the record's
seed, or decodes with the record"; every round's error, a shared round's counted once for each leaf
of the call's request tree, is at most εs. -/
def keySound : Prop :=
  ∃ ε, Err.Below (Err.timesShared (2 ^ r.queryLayout.depthReqT) r.offlineRoundSplits ε) b.εs ∧
    r.protocol.offline.Sound (fun rec y => r.protocol.hasCollisionAt y rec.1 ∨ r.protocol.decodeIndex y rec ≠ none) ε
/-- Entry file: its protocol is round-by-round sound for "the first word does not decode, or the
further word has a collision, or both decode to the same index"; every round's error, a shared
round's counted once for each leaf of the call's request tree, is at most εs. -/
def entrySound : Prop :=
  ∃ ε, Err.Below (Err.timesShared (2 ^ r.queryLayout.depthReqL) r.linkRoundSplits ε) b.εs ∧ r.protocol.link.Sound
    (fun rr y =>
      r.protocol.decodeIndex y.1 rr.1 = none ∨ r.protocol.hasCollisionAt y.2 rr.2.1 ∨ r.protocol.decodeIndex y.2 rr.2 = r.protocol.decodeIndex y.1 rr.1) ε
/-- Proof file: for each record its protocol has round-by-round knowledge soundness in the form for
batches, with the object's own early and late parts of an instance, every round's error at most εs,
for the relaxed relation at the decoded index. -/
def proofSound : Prop :=
  ∃ (wit : r.Instance × r.protocol.Rec → (oneExternalString r.protocol.wordLength r.protocol.Symbol).Str → Tr r.protocol.onlineBatch.loc.shape → b.Wn) (ε : _),
    Err.Below ε b.εs ∧ ∀ rec, (r.protocol.batAt rec).SndBKT r.protocol.maxBatchSize r.protocol.early r.protocol.late
      (r.protocol.relB b.Rno rec) (fun x y τ => wit (x, rec) y τ) ε
/-- The key file's verifier reads its oracles at the positions that it declares alone. -/
def keyLocal : Prop := r.protocol.offline.IsLocal
/-- The entry file's verifier reads its oracles at the declared positions alone. -/
def entryLocal : Prop := r.protocol.link.IsLocal
/-- The proof file's verifier reads its oracles at the declared positions alone. -/
def proofLocal : Prop := r.protocol.onlineBatch.loc.IsLocal
/-- The key file's marks fit together round by round. -/
def keyCoherent : Prop := r.offlineRoundSplits.Coherent
/-- The entry file's marks fit together round by round. -/
def entryCoherent : Prop := r.linkRoundSplits.Coherent
/-- The proof file's marks fit together round by round. -/
def proofCoherent : Prop := r.protocol.onlineBatch.ann.Coherent
/-- The record: for every word, the seed made from uniform digests is a seed at which that word has
a collision with probability at most εs. -/
def seedLaw : Prop := r.seedQueries.Law b.εs
/-- The layout: the laws `OKG` of the object's wire and of the three protocols' wires
(OnBytes/TypedOracleCompiler/Iop/BatchWire.lean); among them: in every round the verifier's message is made from
hash answers so that uniform answers give an exactly uniform message. -/
def wires : Prop := r.queryLayout.OKG ∧ (wTC r.queryLayout).OKG ∧ (wLC r.queryLayout).OKG ∧ (wBC r.queryLayout).OKG
/-- The record: no two lists of answers are written as the same list of digests. -/
def answersCode : Prop := Function.Injective r.answerCode
/-- The record: all lists of answers are written with one number of digests. With `answersCode` this
forces the type of answers `r.protocol.OutOfDomainAnswer` to be finite: an object whose answers are lists of any length
cannot meet the two. -/
def answersLength : Prop := ∀ c c', (r.answerCode c).length = (r.answerCode c').length
/-- The commitment: index binding of the compiled scheme, whose verifier holds the key itself, gives
index binding of the scheme whose verifier holds the hash function's answer at the key's code, with
the extractor `b.ext`, at the cost of `b.εId (tC + tP)` (`Rec.CommitmentBinds`,
Johnson/Top/FrontCommit.lean). Its premise follows from the other hypotheses (`CompilerSoundnessConditions.binds`), so
under them it asserts its conclusion outright. If no two keys have the same code it holds with the
library's extractor at (tC + tP + 2)² / 2^256 (`Rec.commitmentBinds_of_code`). The format's
commitment ID holds the record's seed (`Fmt.publishedBytes`, Fmt/Rules4.lean), and the code that
spells that string is of that kind (`idCodeSeed_oneToOne`, Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean, if the
two spellings are one to one). Where `r.keyCode` is that code, `b.ext` the library's extractor and
`b.εId` its cost, the hypothesis holds, if the two spellings are one to one
(`CompilerSoundnessConditionStatements.commitment_idSeed`, Johnson/Top/CommitCodeAtInnerCompilerInput.lean). At the two sizes of
Johnson/Flat/TwoSizes.lean it is met in that way, by setting five free fields of the parameter
record, not by a proof about a given record (`commitment_withIdFull`, `commitment_withIdSmall`,
Johnson/Flat/CommitCodeSizes.lean). In that code the public files' digest is a constant, fixed
before the hash function is drawn, which the format's specification rules out for a model of the
format (the limits of Johnson/Top/CommitCodeAtInnerCompilerInput.lean). At other values of these fields the
hypothesis stays. At the key that also holds the public digest an input has a code that spells that
string as its `enc`, and the like hypothesis is proved there (`inputIdS`, `encId_oneToOne`,
`commitment_inputIdS`, Johnson/TypedOracleCompiler/Top/IdSeedAt.lean). A code that leaves the record's seed out is
not of that kind. For such a code this library has no proof, which does not say that there is none:
the extractor of the index-binding game sees the commitment and the committer's query log and has no
access to the hash function, so it cannot compute a seed that the committer never asked for. What
would give a proof there: an extractor that needs no seed, or a game whose extractor may query the
hash function. Johnson/Top/GameO.lean defines such a game (`ZKCP.HasIndexBindingWithO`); a bound in
it is no proof of this hypothesis. -/
def commitment : Prop :=
  Rec.CommitmentBinds (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r)) (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout)) r.keyCode b.ext
    (HasRelaxedRelationWitness b) (soundnessBoundOverTypedOracles r.queryLayout b.εs) b.εId
/-- The meaning, for a claim: if an instance is built from a prompt with output tokens and is true
at an index (some witness meets the RELAXED relation), then the claim holds at that index of the
prompt and the output tokens. -/
def soundFor (claim : r.Index → List Token → List Token → Prop) : Prop :=
  ∀ i (x' : List Token × List Token) a x, r.buildInstance x' a = some x → HasRelaxedRelationWitness b i x →
    claim i x'.1 x'.2
/-- The meaning: `soundFor` at the claim "the output tokens are the model's". -/
def sound : Prop := soundFor b (innerSystem r).IsModelOutput

end CompilerSoundnessConditionStatements

/-- The 15 named hypotheses that name no claim. Each field's type is the definition of that name. -/
structure CompilerSoundnessConditions : Prop where
  noneColl      : CompilerSoundnessConditionStatements.noneColl (r := r)
  keySound      : CompilerSoundnessConditionStatements.keySound b
  entrySound    : CompilerSoundnessConditionStatements.entrySound b
  proofSound    : CompilerSoundnessConditionStatements.proofSound b
  keyLocal      : CompilerSoundnessConditionStatements.keyLocal (r := r)
  entryLocal    : CompilerSoundnessConditionStatements.entryLocal (r := r)
  proofLocal    : CompilerSoundnessConditionStatements.proofLocal (r := r)
  keyCoherent   : CompilerSoundnessConditionStatements.keyCoherent (r := r)
  entryCoherent : CompilerSoundnessConditionStatements.entryCoherent (r := r)
  proofCoherent : CompilerSoundnessConditionStatements.proofCoherent (r := r)
  seedLaw       : CompilerSoundnessConditionStatements.seedLaw b
  wires         : CompilerSoundnessConditionStatements.wires (r := r)
  answersCode   : CompilerSoundnessConditionStatements.answersCode (r := r)
  answersLength : CompilerSoundnessConditionStatements.answersLength (r := r)
  commitment    : CompilerSoundnessConditionStatements.commitment b

/-- The 16 named hypotheses: `CompilerSoundnessConditions b` and the meaning at "the output tokens are the model's". -/
structure CompilerSoundnessConditionsWithMeaning : Prop extends CompilerSoundnessConditions b where
  sound : CompilerSoundnessConditionStatements.sound b

/-- Index binding of `schemeOverTypedOracles r`, for the language of the relaxed relation. Two premises of
`cmsRA_binding_at` are met on the spot, since its conclusion does not read them: the count of seeds
at which a word has a collision, at the number of all seeds; the exact relation, taken to be the
relaxed one. -/
theorem CompilerSoundnessConditions.binds {b : SoundnessAnalysisData r} (h : CompilerSoundnessConditions b) :
    ZKCP.Gen.HasIndexBindingWith (relPair (HasRelaxedRelationWitness b) (HasRelaxedRelationWitness b) fun _ _ hw => hw)
      (schemeOverTypedOracles r) (indexExtractorAtRootAndOutOfDomainSample r.queryLayout) (soundnessBoundOverTypedOracles r.queryLayout b.εs) :=
  let ⟨_, bT, sT⟩ := h.keySound
  let ⟨_, bL, sL⟩ := h.entrySound
  let ⟨_, _, bB, sB⟩ := h.proofSound
  cmsRA_binding_at r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters b.Rno b.Rno _ (Fintype.card r.protocol.OutOfDomainSeed) _ _ _ b.εs _
    ⟨h.noneColl, fun _ => Prob.cnt_le_card _, sT, sL, sB⟩ h.seedLaw bT bL bB h.keyLocal
    h.entryLocal h.proofLocal h.keyCoherent h.entryCoherent h.proofCoherent
    ⟨h.wires.1, h.wires.2.1, h.wires.2.2.1, h.wires.2.2.2, ⟨h.answersCode, h.answersLength⟩⟩
    (schemeOverTypedOracles r) rfl

/-- Under 16 hypotheses, the 15 of `CompilerSoundnessConditions b` and `CompilerSoundnessConditionStatements.soundFor b claim` (hypotheses of the
theorem: Lean's list of axioms does not show them): soundness of `innerCompiledVerifier r` for the claim, with
the extractor named. The steps from index binding on are `Rec.soundForWith_systemE_ext`
(Johnson/Top/FrontCommit.lean). -/
theorem innerCompiledVerifier_soundFor (claim : r.Index → List Token → List Token → Prop) (h : CompilerSoundnessConditions b)
    (hs : CompilerSoundnessConditionStatements.soundFor b claim) :
    SoundForWith (innerSystem r) (compiledIndexExtractor b) claim (compiledSoundnessError b) :=
  Rec.soundForWith_systemE_ext (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r)) (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout)) r.keyCode
    b.ext r.coinBound r.fallbackProof r.nextToken
    (bindingR_one r.queryLayout r.oracleCoding (r.oracleCoding.blocks_eq_one (by norm_num) OracleName.leaf (Equiv.refl _))
      (r.oracleCoding.blocks_eq_one (by norm_num) OracleName.node (Equiv.refl _))
      (ZKCP.Special.toPair (ZKCP.languageRelation (HasRelaxedRelationWitness b))) (schemeOverTypedOracles r) _
      (fun tC tP St Ct Pt hC hP => h.binds tC tP St Ct Pt hC hP))
    (fun k x π => noCoin_overOne r.oracleCoding _
      (noCoin_of_detBound _ _ (detBound_VRA r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters k x π)))
    h.commitment claim b.x₀ hs
    (fun tC tP => le_of_eq (congrArg (fun e => e + b.εId (tC + tP))
      (epsA_sum r.queryLayout b.εs tC tP)))

/-- Under the 16 named hypotheses `CompilerSoundnessConditionsWithMeaning b` (hypotheses of the theorem: Lean's list of axioms
does not show them): for every committer and every prover with at most t queries to the hash
function together, the probability that `innerCompiledVerifier r` accepts while the extractor gives no index, or
an index at which the output tokens are not the model's, is at most `compiledSoundnessError b t`. -/
theorem innerCompiledVerifier_sound (h : CompilerSoundnessConditionsWithMeaning b) :
    SoundForWith (innerSystem r) (compiledIndexExtractor b) (innerSystem r).IsModelOutput (compiledSoundnessError b) :=
  innerCompiledVerifier_soundFor b _ h.toCompilerSoundnessConditions h.sound

/-- The scheme's verifier is the compiled verifier with a record, the key being the root and the
record (`verifyAtKeyRoot`, Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean: `verifyAtFullKey` at the key made whole from the key
and what the proof brings). -/
example : (schemeOverTypedOracles r).V = verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters := rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_soundFor
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound

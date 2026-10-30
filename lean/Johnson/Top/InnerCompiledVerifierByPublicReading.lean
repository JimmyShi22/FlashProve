-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InnerCompiledVerifierByPublicReading.lean: soundness of `innerCompiledVerifier`'s compiled verifier
(Johnson/Top/InnerCompiledVerifier.lean) where the coding of typed queries into hash calls, the record's wire,
the code of the answers and the code of a key hang on public digests that the verifier gets from the
hash function itself. Under named hypotheses. The public files are fixed before the hash function is
drawn, and no member of the family is built (Does not show, 1 and 4). Definitions, statements and
proofs.

Why. `innerCompiledVerifier_sound` speaks of an input that is fixed before the hash function is drawn. The
format's strings hold digests that the same hash function has made (the configuration's digest at
the start of every vertex and of stored leaves; the parameters' digests in the chains' first calls;
a run's value too, which is not cured here: 12). A fixed input cannot name them. So a coding that
writes the format's strings hangs on the function, and is no field of a fixed input.

Words. The public reading: an algorithm without coins that asks the hash function and gives a value
d (the digests). A public string: a string that the public reading can ask, at some answers of the
function. The told part: the part of d that stands in a key and in the key's code. The ladder's
form: the verifier "the public reading and a parser, then `innerCompiledVerifier`". The top's form: any system
whose verifier's yes gives that verifier's yes, with its own weights and model.

States.
  `LayoutsByPublicReading R`: over an input R: the type D of the reading's values; the public reading `Pub`; the
    public strings Pt; the fields Sd, cA, m as functions of d; the told part; the code `encT` of a
    pair (told part, key); an honest side (ISK, commit, prove, π₀). `T.at d`: the input at a fixed
    d.
  `T.scheme`, `T.system`: the verifier: the instance is built from the tokens; the commitment is the
    hash function's answer at the code of (c, key); the public reading; the test that d's part is c;
    then the compiled verifier at d through the coding at d, which is the verifier of `innerCompiledVerifier`'s
    own scheme at `T.at d` (by rfl). `T.noCoin_scheme`: it tosses no coin, if the reading tosses
    none.
  `told_binds_core`, `told_binds`: index binding of that scheme, with an extractor that reads the
    key and the committer's log alone (`T.ext`), at the bound of a fixed input.
  **`innerCompiledVerifier_sound_byPublicReading`**, `innerCompiledVerifier_soundFor_byPublicReading`: `Sound` of `T.system`, and `SoundForWith`
    for a claim that is a parameter, with the extractor `T.extractor`, at the error soundnessBoundOverTypedOracles R.queryLayout εs t 0
    + epsCode t: that of `innerCompiledVerifier_sound` at the library's own cost of the code.
  `T.verifyBehindReadingAndParser`, `T.readerBehindReadingAndParser`, `T.ladder_yes`, **`verifyBehindReadingAndParser_sound`**,
    `verifyBehindReadingAndParser_soundFor`: the same of the verifier "the public reading; a parser, which sees
    d; then `innerCompiledVerifier (T.at d)`", whose typed key holds no told part, at that error with n queries
    more: n bounds the reading's and the parser's queries together.
  `verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor`: `SoundForWith` alone, for a claim newClaim that is a parameter, of any
    system (weights, honest side, type of forms) whose verifier's yes gives that verifier's yes at
    every hash function, along a map φ from indices to weights that carries the claim to newClaim;
    extractor: `T.extractor`, then φ; at the ladder's error. That system's model stands in no
    premise and the conclusion does not read it.
  `verifierAcceptingNoMoreThanBehindReadingAndParser_sound`: `Sound` of such a system: the case newClaim := "the output tokens are that
    system's model's", where `carries` is asked against that model; same extractor and error.
  `T.commitment_of_code`, `T.core_of`, `T.readD`, `T.readD_reads`: what thins or meets hypotheses.
  `sound_honest_side`, `soundForWith_honest_side`: these two statements do not read the honest
    side's fields of a system.

Under. At EVERY d of the type T.D, reached by the reading or not: the named hypotheses of
`innerCompiledVerifier_sound` at `T.at d`, with one relation, one instance and one εs for all d, and the
library's extractor and cost of the code (`T.beside`): `innerCompiledVerifier_sound` leaves these two free. Of
the sixteen, eleven are one proposition at all d (by rfl: the term of `T.core_of` shows it), and so
is `sound` (by rfl too; no theorem here states it), which is used at one d; `seedLaw`, `answersCode`
and `answersLength` read Sd d and cA d; `commitment` follows from `code` (`T.commitment_of_code`)
and no proof here reads it. So "at every d" thins to these three (`T.core_of`). Beside them, six
(the count "sixteen and six" is of named hypotheses: for the laws in types see 11): `noCoin`,
`asks`, `once`: the reading has no coins; at every answer of the function it asks strings of T.Pt
alone, and none twice; `spare`: at every d every string of T.Pt codes a point of the spare oracle
under the coding at d; `word`: the extractor's reading of a log is the same at two values with the
same told part; `code`: no two pairs (told part, key) have one code. The ladder's forms also:
`reads`: at every hash function readD has `Pub`'s value; `within`: the bound n, one for all forms
that a prover can put out. The forms for a claim: `meaning` at that claim in place of `sound`. The
top's forms, both: the ladder's `reads` and `within` also; `meaning` at a claim that is a parameter
(not `sound`); and `yes`, `carries`: twelve names in each statement (core, meaning, noCoin, asks,
once, spare, word, code, reads, within, yes, carries), of which core holds the fifteen at every d:
twenty-six in the count of "sixteen and six".

Does not show.
 1. THE PUBLIC FILES ARE FIXED BEFORE THE HASH FUNCTION IS DRAWN: R, T and with them `Pub` and the
    public strings are parameters. A PROVIDER THAT PICKS OR GRINDS ITS PUBLIC FILES WITH THE HASH
    FUNCTION IN HAND, AS EVERY PROVIDER CAN, IS NOT COVERED. The method does not reach that case: it
    resamples the function at strings that no maker chooses, and the step from typed oracles to the
    one hash function (`binding_overOne`, Rom/ExitBind.lean) takes one coding that is fixed before
    the function is drawn.
 2. OF `innerCompiledVerifier_sound`'S PREMISES IT REMOVES ONE ALONE, that the digests in seedQueries, answerCode, oracleCoding and keyCode are
    fixed; a digest that stands in R.protocol, R.queryLayout, R.offlineRoundSplits, R.linkRoundSplits, R.fixedSample, R.compilerParameters or R.buildInstance stays a constant (6).
    It narrows two (the extractor and the cost of the code are the library's: `code` stands where
    `commitment` stood) and adds five on the reading and the codings. The soundness of the key
    file's and of the proof file's protocol, the meaning and the rest stay as open at every d as
    they were at one.
 3. NOTHING FORCES `Pub`, m OR `encT` TO BE THE FORMAT'S. At D := Unit, `Pub := .pure ()` and Pt
    empty, five of the six (`noCoin`, `asks`, `once`, `spare`, `word`) hold for free; `code` is a
    hypothesis on `encT` alone and stays. The statement then says no more than `innerCompiledVerifier_sound` at
    the one input T.at (), at the library's extractor and cost, of a verifier whose key also names a
    constant (an argument: no theorem here). `spare` also holds at any coding under which the
    format's strings are escapes to the spare oracle; `code` at a code that gives no key a code;
    four (`noCoin`, `asks`, `once`, `word`) at D := Unit and a reading that asks different strings
    and throws the answers away: `spare` then asks that m () decodes these strings to the spare
    oracle. That the digests are the hash function's values, and that m d writes what a program
    hashes, is seen at the terms that are laid in; a run that accepts a prover's proofs shows it of
    that run's strings alone.
 4. No member: no T is built here. The hypotheses are laws of parameters, asked at every d of the
    type T.D, reached by `Pub` or not. That they can be met together is not shown: the
    theorems may be true and empty. T.Pt holds every string that `Pub` can ask, at every answer of
    the function, and `spare` is asked of each. Whether a member asks too little cannot be told
    before one is written: a T that asks and throws the answers away, with true digests typed as
    constants into R or m, meets every hypothesis that a true member meets and passes every
    acceptance test (an argument). THE GATE FOR A MEMBER IS A READING OF ITS TERMS, NOT THIS
    THEOREM. Nothing makes the configuration's digest in Sd the one in d; `Pub`'s strings are pinned
    by nothing.
 5. No hypothesis asks that the verifier ever says yes, or that εs is small. If `R.buildInstance` itself
    refuses every output that is not the model's, or every output, the meaning holds whatever the
    relation is, and the theorems say nothing on the protocol (the head of
    Johnson/Top/InnerCompiledVerifier.lean).
 6. FIXED, NOT FUNCTIONS OF d: in R: Index, Instance, protocol, LeafBody, offlineRoundSplits, linkRoundSplits, queryLayout, fixedSample, compilerParameters, buildInstance, coinBound, nextToken; in T:
    encT, Pt, Pub, and the way in which part, Sd, cA, m are made of d. THE THEOREMS SAY SOMETHING OF
    A HASH FUNCTION THAT IS DRAWN ONLY WHERE R AND T NAME NO ANSWER OF IT. That is no hypothesis
    here and cannot be one: it is seen at the term that is laid in. A description whose protocols or
    wiring turn with the digests is outside this file; and the descriptions of this library at a
    plan's chains do hold the public files' digest, in each chain's given data: so, as they stand,
    none of them is an R of which these theorems say something (an argument).
 7. In `T.system` the reading's queries stand in no log and in no budget. In the ladder's form they
    are counted, in n: the step counts a reader to the prover; n stands in both terms of the error,
    so a parser that hashes much pays 5 n εs.
 8. The weights' type and the model are R.Index and R.nextToken, except in the two top's forms, where a
    map φ is a parameter and that it carries the claim a hypothesis; no φ is built. In
    `verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor` the new model is read by nothing. In `verifierAcceptingNoMoreThanBehindReadingAndParser_sound` nt is tied
    by `carries` alone, at φ's values and where the claim holds: if no built instance is true at any
    index, any model passes. `yes` is one direction: a verifier that never says yes meets it.
 9. `T.system`'s verifier is `innerCompiledVerifier` at no input: its key has a told part, its code is `encT`,
    and a reading and a test stand in front. The term `innerCompiledVerifier` stands in `T.verifyBehindReadingAndParser` alone,
    and the tie between the two is one direction (`T.ladder_yes`), which is what soundness needs.
    That `T.verifyBehindReadingAndParser` is the verifier of any other statement of this library is not said.
10. Soundness alone: nothing on an honest side, on hiding, or on two openings of one commitment.
11. Laws in types, beside the named hypotheses: T.m d is a coding that is one to one AND ONTO all
    bit strings, at every d of the type (`OracleCoding`: `inv_code`, `code_inv`, Rom/Family.lean); R.oracleCoding,
    which is overwritten, has to be filled too. Each oracle's answers are as many digests as the
    coding's blocks there (`OracleCoding`: `rng`). `spare` bites only because m d is onto (an argument): a
    family of onto codings is the first thing that a member owes. R.protocol holds four instances: its
    randomness and its seeds are finite and not empty (`HolographicProtocol`, Hiop/RecInterface.lean); R.queryLayout holds
    laws of its own. All limits of the heads of Johnson/Top/InnerCompiledVerifier.lean,
    Johnson/TypedOracleCompiler/RecCompile/PublicLift.lean, Johnson/Top/SoundVia.lean and Johnson/Top/FrontEnc.lean
    stand.
12. On a member that is meant, not on the theorems, where T.D is any type: digests under the
    format's second hash function are no part of d. Nor is a run's value, which the hash function
    makes of bytes of the proof: no public reading can hold it, and T.m d sees d and the typed query
    alone: this file does not reach it.

How. At a fixed d: `CompilerSoundnessConditions.binds` and `bindingR_one`. From every fixed d to the reading's value:
`pub_lift` (Johnson/TypedOracleCompiler/RecCompile/PublicLift.lean) at a committer and a prover (`run2`), with the
whole compiled verifier behind the told test as the verdict: it asks no public string, by `spare`
and `asksIn_VRA`; the event survives the striking of a public string from the logs, by
`extEnc_strike`. `word` makes the reading of the log at any d' with the told part the reading at d.
Then `Rec.soundForWith_systemE` at `code`. The ladder's form: `soundForWith_via`
(Johnson/Top/SoundVia.lean) at the reader that lays d's part into the key; `frontV_is_innerCompiledVerifier`
(Johnson/Top/InnerCompiledVerifierParts.lean), `front_yes_only`, `front_yes` (Johnson/Top/FrontGeneral.lean).
The top's form: `SoundForWith.mapWeights` (VerifiableInference/MapWeights.lean). For proofs only: no
program imports this file.

Terms: lean/GLOSSARY.md; "Words" above.

-/
import Johnson.Top.InnerCompiledVerifier
import Johnson.Top.FrontGeneral
import Johnson.Top.InnerCompiledVerifierParts
import Johnson.Top.ArmsWiderKey
import Johnson.Top.SoundVia
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublic
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublicArm
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsTwoStage
import Johnson.TypedOracleCompiler.RecCompile.ProofAnsPublic
import Johnson.TypedOracleCompiler.RecCompile.PublicLift
import OnBytes.TypedOracleCompiler.Compile.Batch.NoOther
import OnBytes.TypedOracleCompiler.Joined.Cut
import VerifiableInference.MapWeights
import ZKCP.GenKeyTag
import ZKCP.GenSameRun
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What of an input hangs on the public digests, as functions of them (Sd, cA, m); the type D of
what the public reading gives; the public reading; the public strings Pt; the told part; the told
code; and an honest side over the one hash function (ISK, commit, prove, π₀), of which nothing is
asked. R: the input's part that does not hang on the digests. Its fields seedQueries, answerCode, oracleCoding, keyCode are
overwritten in `T.at d`; its ProverKey, commit, prove, fallbackProof ride on there, where no verifier and no bound
reads them. -/
structure LayoutsByPublicReading (R : InnerCompilerInput) where
  /-- what the public reading gives -/
  D : Type
  /-- the public reading: it asks the hash function at the public strings -/
  Pub : Rom.OComp (rom 256) D
  /-- the public strings -/
  Pt : List Bool → Prop
  /-- the part of d that the key's code tells -/
  part : D → Dig 256
  Sd : D → OutOfDomainSampleQueryLayout 256 R.queryLayout.K R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits
  cA : D → R.protocol.OutOfDomainAnswer → List (Dig 256)
  /-- the one coding of all typed queries, at d -/
  m : D → OracleCoding (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) 256
  /-- the code of a key with the told part -/
  encT : Dig 256 × KeyRoot 256 R.protocol → Option ZKCP.Str
  /-- the honest side, over the one hash function: nothing is asked of these -/
  ISK : Type
  commit : R.Index → Rom.OComp (rom 256) ((Dig 256 × KeyRoot 256 R.protocol) × ISK)
  prove : ISK → (l : List (R.Instance × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) l)
  π₀ : (Dig 256 × KeyRoot 256 R.protocol) × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R)

/-- The input at a fixed d: an `InnerCompilerInput`, of which `innerCompiledVerifier_sound` speaks. -/
def LayoutsByPublicReading.at (d : T.D) : InnerCompilerInput :=
  { R with seedQueries := T.Sd d, answerCode := T.cA d, oracleCoding := T.m d, keyCode := fun k => T.encT (T.part d, k) }

/-- The scheme: the public reading; the test of the key's told part; then the compiled verifier at
d, over the one hash function through the coding at d. -/
def LayoutsByPublicReading.scheme : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (Dig 256 × KeyRoot 256 R.protocol) T.ISK
    (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) where
  C := T.commit
  P := T.prove
  V := ZKCP.Gen.toldPart T.Pub T.part fun d k x π =>
    (verifyAtKeyRoot R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters k x π).overOne (T.m d)

/-- The argument system: the commitment is the hash function's answer at the told code. -/
def LayoutsByPublicReading.system : ArgumentSystem :=
  Rec.tokenArgumentSystem T.scheme T.encT R.coinBound R.buildInstance T.π₀ R.nextToken

/-- What the hypotheses name beside the input at d: one relation, one bound on a round's error; the
library's extractor and cost at the code with the told part fixed. -/
def LayoutsByPublicReading.beside (Wn : Type) (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞) (d : T.D) :
    SoundnessAnalysisData (T.at d) where
  Wn := Wn
  Rno := Rno
  ext := (Special.extOf (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout))).digestKey
    fun k => T.encT (T.part d, k)
  εId := epsCode
  x₀ := x₀
  εs := εs

/-- The hypothesis on the commitment at a fixed d follows from `code`. No proof in this file reads
it: it stands in `CompilerSoundnessConditions`. The like for any input at its own code: `CompilerSoundnessConditionStatements.commitment_of_code`
(Johnson/Top/CommitCodeAtInnerCompilerInput.lean), at the cost `commitmentErrorOfKeyCode`, which is `epsCode` under another name;
that file is not imported here for what stands beneath it. -/
theorem LayoutsByPublicReading.commitment_of_code (code : ZKCP.CodeIsOneToOne T.encT) (Wn : Type)
    (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞) (d : T.D) :
    CompilerSoundnessConditionStatements.commitment (T.beside Wn Rno x₀ εs d) :=
  Rec.commitmentBinds_of_code _ _ _
    (fun k k' s h h' => (Prod.mk.inj (code (T.part d, k) (T.part d, k') s h h')).2) _ _

/-- **"At every d" thins to three.** Eleven of the fifteen hypotheses that name no claim are one
proposition at all d (by rfl): they speak of R.protocol, R.offlineRoundSplits, R.linkRoundSplits, R.queryLayout, the relation and εs. So the
fifteen at one d₀, with `seedLaw`, `answersCode` and `answersLength` at every d and `code`, give the
fifteen at every d. -/
theorem LayoutsByPublicReading.core_of (code : ZKCP.CodeIsOneToOne T.encT) (Wn : Type)
    (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞) (d₀ : T.D)
    (h₀ : CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d₀))
    (seed : ∀ d, CompilerSoundnessConditionStatements.seedLaw (T.beside Wn Rno x₀ εs d))
    (ansCode : ∀ d, CompilerSoundnessConditionStatements.answersCode (r := T.at d))
    (ansLength : ∀ d, CompilerSoundnessConditionStatements.answersLength (r := T.at d)) (d : T.D) :
    CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d) where
  noneColl := h₀.noneColl
  keySound := h₀.keySound
  entrySound := h₀.entrySound
  proofSound := h₀.proofSound
  keyLocal := h₀.keyLocal
  entryLocal := h₀.entryLocal
  proofLocal := h₀.proofLocal
  keyCoherent := h₀.keyCoherent
  entryCoherent := h₀.entryCoherent
  proofCoherent := h₀.proofCoherent
  seedLaw := seed d
  wires := h₀.wires
  answersCode := ansCode d
  answersLength := ansLength d
  commitment := T.commitment_of_code code Wn Rno x₀ εs d

/-- The public reading as an algorithm of VerifiableInference/. -/
def LayoutsByPublicReading.readD : DeterministicAlgorithm T.D := deterministicOf (ofRom T.Pub)

/-- At every hash function it has the reading's value: the hypothesis `reads` of the ladder's form
can always be met. The bound `within` stays a hypothesis at it: no lemma here bounds its queries. -/
theorem LayoutsByPublicReading.readD_reads (hash : Hash) : T.readD.evaluate hash = T.Pub.det fun _ => hash :=
  OnBytes.K.evaluate_ofRom hash T.Pub

/-- The scheme's verifier behind the reading and the test IS `innerCompiledVerifier`'s scheme at d. -/
example (d : T.D) (k : KeyRoot 256 R.protocol) (x : R.Instance) (π : OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) :
    (schemeOverOneHashFunction (T.at d).oracleCoding (schemeOverTypedOracles (T.at d))).V k x π =
      (verifyAtKeyRoot R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters k x π).overOne (T.m d) := rfl

/-- The extractor of the scheme whose verifier holds the key itself: a function of the key and the
committer's log alone: it asks no oracle. At the told part c it reads the log through the coding at
some d with that part, picked by choice, not by an algorithm; where there is none it gives no index.
-/
def LayoutsByPublicReading.ext : ZKCP.Gen.Extractor (rom 256) R.Index R.Instance Unit (Dig 256 × KeyRoot 256 R.protocol)
    (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) where
  Ei k tr := by
    classical
    exact if h : ∃ d, T.part d = k.1 then
      (extractorOverOneHashFunction (T.m h.choose) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei k.2 tr else none
  Ew := fun _ _ _ _ _ => ()

/-- The compiled verifier at the key (root, record) asks no point of the spare oracle. -/
theorem asksIn_VRA {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (k : KeyRoot lam L) (x : X)
    (π : OfflineLinkOnlineProof lam L aT aL) :
    (verifyAtKeyRoot W S cA r₀ p k x π).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  unfold verifyAtKeyRoot verifyAtFullKey
  split
  · refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
    intro _
    refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
    intro _
    refine OComp.AsksIn.bind ?_
      (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
    intro _
    refine OComp.AsksIn.bind ?_
      (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
    intro _
    refine OComp.AsksIn.bind ?_
      (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
    intro _
    trivial
  · trivial

/-- **Under named hypotheses, the public files fixed first: index binding of the scheme with the
reading in front**, with the extractor `T.ext`, at the bound of a fixed d. Hypotheses: at every d
the fifteen that name no claim (core; `commitment` among them is a surplus here: nothing reads it);
the reading has no coins (noCoin), asks public strings alone (asks) and none twice (once); at every
d a public string codes a point of the spare oracle (spare); the extractor's reading of a log hangs
on d through the told part alone (word). The public files, and so `T.Pub` and the public strings,
are fixed before the hash function is drawn. -/
theorem told_binds_core (Wn : Type) (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d))
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei) :
    ZKCP.Gen.HasIndexBindingWith
      (ZKCP.Special.toPair (ZKCP.languageRelation fun i x => ∃ w, Rno i x w)) T.scheme T.ext
      (soundnessBoundOverTypedOracles R.queryLayout εs) := by
  classical
  intro tC tP St Ct Pv₀ hC hP
  -- the relation, the extractor at d, the verdict at d, the event at d
  let Rp := ZKCP.Special.toPair (ZKCP.languageRelation fun (i : R.Index) (x : R.Instance) => ∃ w, Rno i x w)
  let Y := (((Dig 256 × KeyRoot 256 R.protocol) × St) × Trace (rom 256)) ×
    ((R.Instance × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) × Trace (rom 256))
  let eiD : T.D → KeyRoot 256 R.protocol → Trace (rom 256) → Option R.Index :=
    fun d => (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei
  let vD : T.D → Y → OComp (rom 256) Bool := fun d y =>
    (verifyAtKeyRoot R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters y.1.1.1.2 y.2.1.1 y.2.1.2).overOne (T.m d)
  let verd : T.D → Y → OComp (rom 256) Bool := fun d y =>
    if T.part d = y.1.1.1.1 then vD d y else .pure false
  let Bad : T.D → Y → Prop := fun d y => T.part d = y.1.1.1.1 →
    (y.2.1.1 ∉ Rp.L (eiD d y.1.1.1.2 y.1.2) ∨ ¬ Rp.no' (eiD d y.1.1.1.2 y.1.2) y.2.1.1 ())
  have lift := pub_lift
    (M := OComp (rom 256) ((Dig 256 × KeyRoot 256 R.protocol) × St) ×
      (St → OComp (rom 256) (R.Instance × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)))
    (run2 Prod.snd) wire2 strike2 (fun s r M g => run2_wire Prod.snd s r M g)
    (fun M => M.1.QueryBound tC ∧ ∀ st, (M.2 st).QueryBound tP)
    (fun s r M h => ⟨queryBound_wire s r M.1 tC h.1, fun st => queryBound_wire s r _ tP (h.2 st)⟩)
    verd (fun _ _ _ => rfl) T.Pt
    (fun d y => by
      show (if T.part d = y.1.1.1.1 then vD d y else .pure false).AsksIn fun _ s => ¬ T.Pt s
      split
      · exact (asksIn_overOne (T.m d) (NotOther 256 (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) _
          (asksIn_VRA R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters _ _ _)).mono fun _ s h hp => h (spare d s hp)
      · trivial)
    Bad
    (fun d s y hs hb => by
      intro hc
      have e : eiD d y.1.1.1.2 (strike s y.1.2) = eiD d y.1.1.1.2 y.1.2 := by
        show R.protocol.decodeIndex (extEnc R.queryLayout (singleTr (T.m d) (strike s y.1.2)) y.1.1.1.2.cm) y.1.1.1.2.rcd =
          R.protocol.decodeIndex (extEnc R.queryLayout (singleTr (T.m d) y.1.2) y.1.1.1.2.cm) y.1.1.1.2.rcd
        rw [extEnc_strike (T.m d) s (isOther_tree (T.m d) s (spare d s hs))]
      show _ ∉ Rp.L (eiD d y.1.1.1.2 (strike s y.1.2)) ∨
        ¬ Rp.no' (eiD d y.1.1.1.2 (strike s y.1.2)) _ ()
      rw [e]
      exact hb hc)
    (soundnessBoundOverTypedOracles R.queryLayout εs tC tP) ?_ T.Pub noCoin asks once (Ct, Pv₀) ⟨hC, hP⟩
  · -- the experiment is the image of the lifted one
    have e : ZKCP.Gen.bindingExp T.scheme T.ext Ct Pv₀ =
        (expP verd T.Pub (run2 Prod.snd (Ct, Pv₀))).bind fun z =>
          .pure (⟨z.2.2, T.ext.Ei z.1.1.1.1 z.1.1.2, z.1.2.1.1, ()⟩ :
            ZKCP.Gen.BindingOutcome R.Index R.Instance Unit) := by
      have e0 : ZKCP.Gen.bindingExp T.scheme T.ext Ct Pv₀ =
          Ct.withTrace.bind fun a => (Pv₀ a.1.2).withTrace.bind fun a1 =>
            (T.Pub.bind fun d => verd d (a, a1)).bind fun c =>
              Rom.OComp.pure (⟨c, T.ext.Ei a.1.1 a.2, a1.1.1, ()⟩ :
                ZKCP.Gen.BindingOutcome R.Index R.Instance Unit) := rfl
      rw [e0]
      simp only [expP, verdP, run2, Rom.OComp.bind_assoc, Rom.OComp.bind]
    rw [e, Rom.Pr_bind_pure]
    refine le_trans (Rom.Pr_mono _ fun _ => ?_) lift
    rintro z ⟨hz, hbad⟩
    refine ⟨hz, fun hc => ?_⟩
    have hex : ∃ d, T.part d = z.1.1.1.1.1 := ⟨z.2.1, hc⟩
    have e2 : T.ext.Ei z.1.1.1.1 z.1.1.2 = eiD z.2.1 z.1.1.1.1.2 z.1.1.2 := by
      show (if h : ∃ d, T.part d = z.1.1.1.1.1 then
        (extractorOverOneHashFunction (T.m h.choose) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei z.1.1.1.1.2 z.1.1.2 else none) = _
      rw [dif_pos hex, word hex.choose z.2.1 (hex.choose_spec.trans hc.symm)]
    have hbad' : z.1.2.1.1 ∉ Rp.L (T.ext.Ei z.1.1.1.1 z.1.1.2) ∨
        ¬ Rp.no' (T.ext.Ei z.1.1.1.1 z.1.1.2) z.1.2.1.1 () := hbad
    rw [e2] at hbad'
    exact hbad'
  · -- at a fixed d
    rintro d ⟨Ct, Pv⟩ ⟨hC, hP⟩
    have hb := bindingR_one R.queryLayout (T.m d)
      ((T.m d).blocks_eq_one (by norm_num) OracleName.leaf (Equiv.refl _))
      ((T.m d).blocks_eq_one (by norm_num) OracleName.node (Equiv.refl _)) Rp (schemeOverTypedOracles (T.at d)) _
      (fun tC tP St Ct Pt hC hP => (core d).binds tC tP St Ct Pt hC hP)
    have h1 := hb tC tP ((Dig 256 × KeyRoot 256 R.protocol) × St)
      (ZKCP.Gen.mapO (fun o => (o.1.2, o)) Ct) (fun o => Pv o.2)
      (ZKCP.Gen.queryBound_mapO _ Ct tC hC) (fun o => hP o.2)
    -- one richer experiment, of which both are images
    let Xp : OComp (rom 256) (Y × Bool) :=
      (run2 Prod.snd (Ct, Pv)).bind fun y => (vD d y).bind fun b => .pure (y, b)
    have eA : ∀ g, (expD verd d (run2 Prod.snd (Ct, Pv))).runEager g =
        (Xp.bind fun z => .pure (z.1, d, decide (T.part d = z.1.1.1.1.1) && z.2)).runEager g := by
      intro g
      simp only [expD, Xp, Rom.OComp.bind_assoc, Rom.OComp.runEager_bind]
      refine congrArg _ (funext fun y => ?_)
      by_cases hc : T.part d = y.1.1.1.1
      · simp [verd, hc, Rom.OComp.runEager]
      · simp [verd, hc, Rom.OComp.runEager]
    have eB : ZKCP.Gen.bindingExp (schemeOverOneHashFunction (T.m d) (schemeOverTypedOracles (T.at d)))
        (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)) (ZKCP.Gen.mapO (fun o => (o.1.2, o)) Ct)
        (fun o => Pv o.2) =
        Xp.bind fun z => .pure (⟨z.2, eiD d z.1.1.1.1.2 z.1.1.2, z.1.2.1.1, ()⟩ :
          ZKCP.Gen.BindingOutcome R.Index R.Instance Unit) := by
      have e0 : ZKCP.Gen.bindingExp (schemeOverOneHashFunction (T.m d) (schemeOverTypedOracles (T.at d)))
          (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)) (ZKCP.Gen.mapO (fun o => (o.1.2, o)) Ct)
          (fun o => Pv o.2) =
          (ZKCP.Gen.mapO (fun o : (Dig 256 × KeyRoot 256 R.protocol) × St => (o.1.2, o)) Ct).withTrace.bind
            fun a => (Pv a.1.2.2).withTrace.bind fun a1 =>
              ((verifyAtKeyRoot R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters a.1.1 a1.1.1 a1.1.2).overOne (T.m d)).bind
                fun c => Rom.OComp.pure (⟨c, eiD d a.1.1 a.2, a1.1.1, ()⟩ :
                  ZKCP.Gen.BindingOutcome R.Index R.Instance Unit) := rfl
      rw [e0, ZKCP.Gen.withTrace_mapO]
      simp only [Xp, vD, run2, ZKCP.Gen.mapO, Rom.OComp.bind_assoc, Rom.OComp.bind]
    rw [ZKCP.Gen.Pr_congr eA, Rom.Pr_bind_pure]
    have h2 : Rom.Pr (Xp.bind fun z => .pure (⟨z.2, eiD d z.1.1.1.1.2 z.1.1.2, z.1.2.1.1, ()⟩ :
        ZKCP.Gen.BindingOutcome R.Index R.Instance Unit)) (fun _ => ZKCP.Gen.bindingBad Rp) ≤
        soundnessBoundOverTypedOracles R.queryLayout εs tC tP := by
      rw [← eB]
      exact h1
    rw [Rom.Pr_bind_pure] at h2
    refine le_trans (Rom.Pr_mono _ fun _ => ?_) h2
    rintro z ⟨hz, hbad⟩
    have hz' : (decide (T.part d = z.1.1.1.1.1) && z.2) = true := hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hz'
    exact ⟨hz'.2, hbad hz'.1⟩

/-- The same from the sixteen at every d (each), with noCoin, asks, once, spare, word. -/
theorem told_binds (Wn : Type) (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞)
    (each : ∀ d, CompilerSoundnessConditionsWithMeaning (T.beside Wn Rno x₀ εs d))
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei) :
    ZKCP.Gen.HasIndexBindingWith
      (ZKCP.Special.toPair (ZKCP.languageRelation fun i x => ∃ w, Rno i x w)) T.scheme T.ext
      (soundnessBoundOverTypedOracles R.queryLayout εs) :=
  told_binds_core T Wn Rno x₀ εs (fun d => (each d).toCompilerSoundnessConditions) noCoin asks once spare word

/-- The scheme's verifier tosses no coin, if the reading tosses none. -/
theorem LayoutsByPublicReading.noCoin_scheme (noCoin : T.Pub.NoCoin) (k : Dig 256 × KeyRoot 256 R.protocol) (x : R.Instance)
    (π : OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) : (T.scheme.V k x π).NoCoin := by
  refine OComp.NoCoin.bind noCoin fun d => ?_
  by_cases h : T.part d = k.1
  · simp only [if_pos h]
    exact noCoin_overOne (T.m d) _
      (noCoin_of_detBound _ _ (detBound_VRA R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters k.2 x π))
  · simp only [if_neg h]
    trivial

/-- The named extractor: a function of the commitment and the committer's log alone: it asks no
oracle. It finds the key by its code in the log and picks by choice, not by an algorithm
(ZKCP/DigestKey.lean; `T.ext`). -/
def LayoutsByPublicReading.extractor : Commitment → QueryLog → Option R.Index :=
  (Rec.tokenExtractorE (X := R.Instance) T.ext T.encT).Ei

/-- **`innerCompiledVerifier_sound_byPublicReading` (below) for a claim that is a parameter**, with the extractor named.
Under: at every d the fifteen hypotheses that name no claim (core); the meaning at that claim
(meaning; it reads no d); the six on the reading, the codings and the code (noCoin, asks, once,
spare, word, code). The public files are fixed before the hash function is drawn. Only seedQueries, answerCode, oracleCoding and
keyCode hang on the digests: one that stands in R.protocol, R.queryLayout, R.offlineRoundSplits, R.linkRoundSplits, R.fixedSample, R.compilerParameters or R.buildInstance stays a
constant (the head, 6). It says as much as the claim says (VerifiableInference/MoreStatements.lean,
at `SoundFor`). -/
theorem innerCompiledVerifier_soundFor_byPublicReading (claim : R.Index → List Token → List Token → Prop) (Wn : Type)
    (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, R.buildInstance x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT) :
    SoundForWith T.system T.extractor claim fun t => soundnessBoundOverTypedOracles R.queryLayout εs t 0 + epsCode t :=
  Rec.soundForWith_systemE (ε' := fun t => soundnessBoundOverTypedOracles R.queryLayout εs t 0 + epsCode t) T.scheme T.ext T.encT
    R.coinBound T.π₀ R.nextToken code
    (told_binds_core T Wn Rno x₀ εs core noCoin asks once spare word)
    (T.noCoin_scheme noCoin) claim x₀ meaning
    (fun tC tP => by rw [epsA_sum R.queryLayout εs tC tP]; exact le_rfl)

/-- **Under named hypotheses, the public files fixed first: soundness of `T.system`: `innerCompiledVerifier`'s
compiled verifier at digests that the verifier asks for.** Under the sixteen named hypotheses at
every d (each) and six on the reading, the codings and the code (noCoin, asks, once, spare, word,
code): hypotheses of the theorem: Lean's list of axioms does not show them. d₀: any value of the
reading's type: `sound` is read there. The extractor is `T.extractor`. The public files are fixed
before the hash function is drawn. Of `innerCompiledVerifier_sound`'s premises it removes that the digests in
seedQueries, answerCode, oracleCoding and keyCode are fixed, and no other; it narrows two: the extractor and the cost of the code
are the library's (`T.beside`). Only seedQueries, answerCode, oracleCoding and keyCode hang on the digests: one that stands in R.protocol,
R.queryLayout, R.offlineRoundSplits, R.linkRoundSplits, R.fixedSample, R.compilerParameters or R.buildInstance stays a constant (the head, 6). -/
theorem innerCompiledVerifier_sound_byPublicReading (d₀ : T.D) (Wn : Type) (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance)
    (εs : ℝ≥0∞)
    -- at every fixed d: the sixteen named hypotheses of `innerCompiledVerifier_sound`
    (each : ∀ d, CompilerSoundnessConditionsWithMeaning (T.beside Wn Rno x₀ εs d))
    -- the public reading: no coins; public strings alone; none twice
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    -- at every d every public string codes a point of the spare oracle under the coding at d
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    -- the extractor's reading of a log hangs on d through the told part alone
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    -- no two pairs (told part, key) have one code
    (code : ZKCP.CodeIsOneToOne T.encT) :
    Sound T.system fun t => soundnessBoundOverTypedOracles R.queryLayout εs t 0 + epsCode t :=
  ⟨T.extractor, innerCompiledVerifier_soundFor_byPublicReading T _ Wn Rno x₀ εs (fun d => (each d).toCompilerSoundnessConditions)
    (each d₀).sound noCoin asks once spare word code⟩

/-! ## The ladder's form: the reading, a parser, then innerCompiledVerifier at the reading's value -/

/-- The verifier in the ladder's form: the public reading; a parser, which sees its value; then
`innerCompiledVerifier` at the input at that value. The key in the typed proof is (root, record): it holds
no told part. -/
def LayoutsByPublicReading.verifyBehindReadingAndParser {Form : Type} (readD : DeterministicAlgorithm T.D)
    (parse : (d : T.D) → List Token → List Token → Form →
      DeterministicAlgorithm (List Token × (KeyRoot 256 R.protocol × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)))
    (commitment : Commitment) (prompt output : List Token) (form : Form) :
    DeterministicAlgorithm Bool :=
  readD.andThen fun d => (parse d prompt output form).andThen fun proof =>
    innerCompiledVerifier (T.at d) commitment prompt output proof

/-- The reader of the step to the ladder's form: the reading, the parser, and the told part laid
into the key. -/
def LayoutsByPublicReading.readerBehindReadingAndParser {Form : Type} (readD : DeterministicAlgorithm T.D)
    (parse : (d : T.D) → List Token → List Token → Form →
      DeterministicAlgorithm (List Token × (KeyRoot 256 R.protocol × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)))
    (prompt output : List Token) (form : Form) : DeterministicAlgorithm T.system.Proof :=
  readD.andThen fun d => (parse d prompt output form).andThen fun proof =>
    .done (proof.1, ((T.part d, proof.2.1), proof.2.2))

/-- At every hash function, if readD has `T.Pub`'s value there (reads): the ladder's verifier's yes
gives the told system's yes at the proof that the reader makes. One direction. -/
theorem LayoutsByPublicReading.ladder_yes {Form : Type} (readD : DeterministicAlgorithm T.D)
    (reads : ∀ hash : Hash, readD.evaluate hash = T.Pub.det fun _ => hash)
    (parse : (d : T.D) → List Token → List Token → Form →
      DeterministicAlgorithm (List Token × (KeyRoot 256 R.protocol × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)))
    (hash : Hash) (commitment : Commitment) (prompt output : List Token) (form : Form)
    (hy : (T.verifyBehindReadingAndParser readD parse commitment prompt output form).evaluate hash = true) :
    T.system.accepts hash commitment prompt output
      ((T.readerBehindReadingAndParser readD parse prompt output form).evaluate hash) = true := by
  unfold LayoutsByPublicReading.verifyBehindReadingAndParser at hy
  rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen] at hy
  unfold LayoutsByPublicReading.readerBehindReadingAndParser
  rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen]
  generalize hd : readD.evaluate hash = d at hy ⊢
  generalize (parse d prompt output form).evaluate hash = proof at hy ⊢
  obtain ⟨aux, k, π⟩ := proof
  rw [← OnBytes.K.frontV_is_innerCompiledVerifier] at hy
  obtain ⟨x, cd, hb, hc, hh, hv⟩ := OnBytes.K.front_yes_only
    (schemeOverOneHashFunction (T.at d).oracleCoding (schemeOverTypedOracles (T.at d))) (T.at d).keyCode (T.at d).coinBound (T.at d).buildInstance
    (T.at d).fallbackProof hash commitment prompt output aux k π hy
  refine OnBytes.K.front_yes T.scheme T.encT R.coinBound R.buildInstance T.π₀ hash commitment prompt output
    aux (T.part d, k) π x cd hb hc hh ?_
  show (T.Pub.bind fun d' => if T.part d' = T.part d then
    (verifyAtKeyRoot R.queryLayout (T.Sd d') (T.cA d') R.fixedSample R.compilerParameters k x π).overOne (T.m d') else .pure false).det
      (fun _ => hash) = true
  rw [Rom.OComp.det_bind, ← reads hash, hd, if_pos rfl]
  exact hv

/-- **`verifyBehindReadingAndParser_sound` (below) for a claim that is a parameter**, with the extractor
`T.extractor`. Under the premises of `innerCompiledVerifier_soundFor_byPublicReading` (core, meaning, noCoin, asks, once,
spare, word, code), and: readD has `T.Pub`'s value at every hash function (reads); n bounds the
reading's and the parser's queries together (within). At that law's error with n queries more. The
public files are fixed before the hash function is drawn. Only seedQueries, answerCode, oracleCoding and keyCode hang on the
digests: one that stands in R.protocol, R.queryLayout, R.offlineRoundSplits, R.linkRoundSplits, R.fixedSample, R.compilerParameters or R.buildInstance stays a constant (the head,
6). -/
theorem verifyBehindReadingAndParser_soundFor (claim : R.Index → List Token → List Token → Prop) (Wn : Type)
    (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, R.buildInstance x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    {Form : Type}
    (prove' : T.system.Weights → T.system.CommitmentRandomness → List Token → List Token →
      RandomizedAlgorithm Form)
    (readD : DeterministicAlgorithm T.D)
    (reads : ∀ hash : Hash, readD.evaluate hash = T.Pub.det fun _ => hash)
    (parse : (d : T.D) → List Token → List Token → Form →
      DeterministicAlgorithm (List Token × (KeyRoot 256 R.protocol × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)))
    (n : ℕ)
    (within : ∀ prompt output form,
      (T.readerBehindReadingAndParser readD parse prompt output form).toRandomized.QueryBound n) :
    SoundForWith (T.system.withVerifier Form prove' (T.verifyBehindReadingAndParser readD parse)) T.extractor claim
      fun t => soundnessBoundOverTypedOracles R.queryLayout εs (t + n) 0 + epsCode (t + n) := by
  have key := soundForWith_via T.system prove' (T.verifyBehindReadingAndParser readD parse)
    (T.readerBehindReadingAndParser readD parse) n (fun _ _ _ _ => DeterministicAlgorithm.done false)
    (fun hash commitment prompt output form hy =>
      Or.inl (T.ladder_yes readD reads parse hash commitment prompt output form hy))
    within
    (innerCompiledVerifier_soundFor_byPublicReading T claim Wn Rno x₀ εs core meaning noCoin asks once spare word code)
    exceptionBound_never
  have e : (fun t => (fun t => soundnessBoundOverTypedOracles R.queryLayout εs t 0 + epsCode t) (t + n) + (fun _ => (0 : ℝ≥0∞)) t) =
      fun t => soundnessBoundOverTypedOracles R.queryLayout εs (t + n) 0 + epsCode (t + n) := by
    funext t
    simp
  rw [← e]
  exact key

/-- **The top's form, for a claim that is a parameter**: any weights and honest side; any type of
forms; any verifier whose yes, at every hash function, gives the yes of "the reading; a parser;
innerCompiledVerifier at the reading's value". φ carries an index to weights, and the claim with it; the
extractor is `T.extractor` followed by φ. Conclusion: `SoundForWith` of that system for newClaim, a
parameter, at the ladder's error (n queries more). It says as much as newClaim says; it does not
read the model nt. Hypotheses: those of `verifyBehindReadingAndParser_soundFor` (core, meaning, noCoin, asks,
once, spare, word, code, reads, within); the verifier's yes gives that verifier's yes (yes); φ
carries the claim (carries). The parser does not see the commitment. By `soundForWith_via` and
`SoundForWith.mapWeights` (VerifiableInference/MapWeights.lean). The public files are fixed before
the hash function is drawn. Only seedQueries, answerCode, oracleCoding and keyCode hang on the digests: one that stands in R.protocol, R.queryLayout,
R.offlineRoundSplits, R.linkRoundSplits, R.fixedSample, R.compilerParameters or R.buildInstance stays a constant (the head, 6). -/
theorem verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor (claim : R.Index → List Token → List Token → Prop) (Wn : Type)
    (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, R.buildInstance x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    {Form NW PP CR : Type} (pp : NW → PP) (nt : NW → List Token → Option Token)
    (smp : RandomizedAlgorithm CR) (cm : NW → CR → DeterministicAlgorithm Commitment)
    (pr : NW → CR → List Token → List Token → RandomizedAlgorithm Form)
    (verify' : Commitment → List Token → List Token → Form → DeterministicAlgorithm Bool)
    (readD : DeterministicAlgorithm T.D)
    (reads : ∀ hash : Hash, readD.evaluate hash = T.Pub.det fun _ => hash)
    (parse : (d : T.D) → List Token → List Token → Form →
      DeterministicAlgorithm (List Token × (KeyRoot 256 R.protocol × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)))
    (n : ℕ)
    (within : ∀ prompt output form,
      (T.readerBehindReadingAndParser readD parse prompt output form).toRandomized.QueryBound n)
    (yes : ∀ hash commitment prompt output form,
      (verify' commitment prompt output form).evaluate hash = true →
        (T.verifyBehindReadingAndParser readD parse commitment prompt output form).evaluate hash = true)
    (φ : R.Index → NW) (newClaim : NW → List Token → List Token → Prop)
    (carries : ∀ i prompt output, claim i prompt output → newClaim (φ i) prompt output) :
    SoundForWith
      { Weights := NW, PublicParameters := PP, publicParameters := pp, CommitmentRandomness := CR,
        Proof := Form, nextToken := nt, sampleCommitmentRandomness := smp, commit := cm,
        prove := pr, verify := verify' }
      (fun commitment queryLog => (T.extractor commitment queryLog).map φ) newClaim
      fun t => soundnessBoundOverTypedOracles R.queryLayout εs (t + n) 0 + epsCode (t + n) := by
  -- the told system with the new randomness: soundness does not read it
  let S₀ : ArgumentSystem :=
    { T.system with
      CommitmentRandomness := CR, sampleCommitmentRandomness := smp,
      commit := fun i r => cm (φ i) r,
      prove := fun _ _ _ _ => RandomizedAlgorithm.done ([], T.π₀) }
  have h0 : SoundForWith S₀ T.extractor claim fun t => soundnessBoundOverTypedOracles R.queryLayout εs t 0 + epsCode t :=
    innerCompiledVerifier_soundFor_byPublicReading T claim Wn Rno x₀ εs core meaning noCoin asks once spare word code
  have key := soundForWith_via S₀ (fun i r p o => pr (φ i) r p o) verify'
    (T.readerBehindReadingAndParser readD parse) n (fun _ _ _ _ => DeterministicAlgorithm.done false)
    (fun hash commitment prompt output form hy =>
      Or.inl (T.ladder_yes readD reads parse hash commitment prompt output form
        (yes hash commitment prompt output form hy)))
    within h0 exceptionBound_never
  have e : (fun t => (fun t => soundnessBoundOverTypedOracles R.queryLayout εs t 0 + epsCode t) (t + n) + (fun _ => (0 : ℝ≥0∞)) t) =
      fun t => soundnessBoundOverTypedOracles R.queryLayout εs (t + n) 0 + epsCode (t + n) := by
    funext t
    simp
  rw [e] at key
  exact SoundForWith.mapWeights _ _ _ _ key NW PP pp nt cm pr φ newClaim carries

/-- **Under named hypotheses, the public files fixed first: `Sound` of any system whose verifier's
yes gives the ladder's verifier's yes, if φ carries the claim to that system's model.**
`verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor` at newClaim := "the output tokens are the model nt's" (`IsModelOutput`'s
body); `claim` stays a parameter. Error: the ladder's (n queries more). Extractor behind the ∃:
`T.extractor`, then φ. Hypotheses: core, meaning, noCoin, asks, once, spare, word, code, reads,
within, yes, carries. The public files are fixed before the hash function is drawn. Only seedQueries, answerCode, oracleCoding
and keyCode hang on the digests: one that stands in R.protocol, R.queryLayout, R.offlineRoundSplits, R.linkRoundSplits, R.fixedSample, R.compilerParameters or R.buildInstance stays a
constant (the head, 6). -/
theorem verifierAcceptingNoMoreThanBehindReadingAndParser_sound (claim : R.Index → List Token → List Token → Prop) (Wn : Type)
    (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance) (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, R.buildInstance x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    {Form NW PP CR : Type} (pp : NW → PP) (nt : NW → List Token → Option Token)
    (smp : RandomizedAlgorithm CR) (cm : NW → CR → DeterministicAlgorithm Commitment)
    (pr : NW → CR → List Token → List Token → RandomizedAlgorithm Form)
    (verify' : Commitment → List Token → List Token → Form → DeterministicAlgorithm Bool)
    (readD : DeterministicAlgorithm T.D)
    (reads : ∀ hash : Hash, readD.evaluate hash = T.Pub.det fun _ => hash)
    (parse : (d : T.D) → List Token → List Token → Form →
      DeterministicAlgorithm (List Token × (KeyRoot 256 R.protocol × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)))
    (n : ℕ)
    (within : ∀ prompt output form,
      (T.readerBehindReadingAndParser readD parse prompt output form).toRandomized.QueryBound n)
    (yes : ∀ hash commitment prompt output form,
      (verify' commitment prompt output form).evaluate hash = true →
        (T.verifyBehindReadingAndParser readD parse commitment prompt output form).evaluate hash = true)
    (φ : R.Index → NW)
    (carries : ∀ i prompt output, claim i prompt output →
      ∀ position (h : position < output.length),
        nt (φ i) (prompt ++ output.take position) = some output[position]) :
    Sound
      { Weights := NW, PublicParameters := PP, publicParameters := pp, CommitmentRandomness := CR,
        Proof := Form, nextToken := nt, sampleCommitmentRandomness := smp, commit := cm,
        prove := pr, verify := verify' }
      fun t => soundnessBoundOverTypedOracles R.queryLayout εs (t + n) 0 + epsCode (t + n) := by
  have key := verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor T claim Wn Rno x₀ εs core meaning noCoin asks once spare word
    code pp nt smp cm pr verify' readD reads parse n within yes φ
    (fun w prompt output => ∀ position (h : position < output.length),
      nt w (prompt ++ output.take position) = some output[position]) carries
  exact (sound_iff_soundFor _ _).2 ⟨_, key⟩

/-- **`Sound` does not read the honest side**: the public parameters, the committer's randomness,
the committer and the prover can be any. For whoever lays a system with an honest side of its own
beside one of this file's; no theorem here calls it. What `Sound` does read (the weights' type, the
model, the proofs' type, the verifier) is seen at its body, not stated here. -/
theorem sound_honest_side (S : ArgumentSystem) (PP : Type) (pp : S.Weights → PP) (CR : Type)
    (smp : RandomizedAlgorithm CR) (cm : S.Weights → CR → DeterministicAlgorithm Commitment)
    (pr : S.Weights → CR → List Token → List Token → RandomizedAlgorithm S.Proof)
    (ε : ℕ → ℝ≥0∞) :
    Sound { S with PublicParameters := PP, publicParameters := pp, CommitmentRandomness := CR,
                   sampleCommitmentRandomness := smp, commit := cm, prove := pr } ε ↔ Sound S ε :=
  Iff.rfl

/-- The same of `SoundForWith`. -/
theorem soundForWith_honest_side (S : ArgumentSystem) (PP : Type) (pp : S.Weights → PP) (CR : Type)
    (smp : RandomizedAlgorithm CR) (cm : S.Weights → CR → DeterministicAlgorithm Commitment)
    (pr : S.Weights → CR → List Token → List Token → RandomizedAlgorithm S.Proof)
    (extractor : Commitment → QueryLog → Option S.Weights)
    (claim : S.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞) :
    SoundForWith { S with PublicParameters := PP, publicParameters := pp,
                          CommitmentRandomness := CR, sampleCommitmentRandomness := smp,
                          commit := cm, prove := pr } extractor claim ε ↔
      SoundForWith S extractor claim ε :=
  Iff.rfl

/-- **The ladder's form.** Under the premises of `innerCompiledVerifier_sound_byPublicReading`: the system whose verifier
is "the reading; a parser; innerCompiledVerifier at the reading's value" is `Sound`, at that theorem's error
with n queries more: n bounds the reading's and the parser's queries together. readD is the public
reading as an algorithm of VerifiableInference/: at every hash function it has `T.Pub`'s value
(reads); the bound n is `within`. Open beside it: the weights' type and the model are R.Index and
R.nextToken; the typed proof's type does not turn with d; the parser does not see the commitment.
The public files are fixed before the hash function is drawn. Only seedQueries, answerCode, oracleCoding and keyCode hang on the
digests: one that stands in R.protocol, R.queryLayout, R.offlineRoundSplits, R.linkRoundSplits, R.fixedSample, R.compilerParameters or R.buildInstance stays a constant (the head,
6). -/
theorem verifyBehindReadingAndParser_sound (d₀ : T.D) (Wn : Type) (Rno : R.Index → R.Instance → Wn → Prop) (x₀ : R.Instance)
    (εs : ℝ≥0∞)
    (each : ∀ d, CompilerSoundnessConditionsWithMeaning (T.beside Wn Rno x₀ εs d))
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei = (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample R.queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    {Form : Type}
    (prove' : T.system.Weights → T.system.CommitmentRandomness → List Token → List Token →
      RandomizedAlgorithm Form)
    (readD : DeterministicAlgorithm T.D)
    (reads : ∀ hash : Hash, readD.evaluate hash = T.Pub.det fun _ => hash)
    (parse : (d : T.D) → List Token → List Token → Form →
      DeterministicAlgorithm (List Token × (KeyRoot 256 R.protocol × OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)))
    (n : ℕ)
    (within : ∀ prompt output form,
      (T.readerBehindReadingAndParser readD parse prompt output form).toRandomized.QueryBound n) :
    Sound (T.system.withVerifier Form prove' (T.verifyBehindReadingAndParser readD parse)) fun t =>
      soundnessBoundOverTypedOracles R.queryLayout εs (t + n) 0 + epsCode (t + n) :=
  ⟨T.extractor, verifyBehindReadingAndParser_soundFor T _ Wn Rno x₀ εs (fun d => (each d).toCompilerSoundnessConditions)
    (each d₀).sound noCoin asks once spare word code prove' readD reads parse n within⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.asksIn_VRA
#print axioms VerifiableInference.OnPublicFiles.told_binds_core
#print axioms VerifiableInference.OnPublicFiles.told_binds
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound_byPublicReading
#print axioms VerifiableInference.OnPublicFiles.verifyBehindReadingAndParser_sound
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_soundFor_byPublicReading
#print axioms VerifiableInference.OnPublicFiles.verifyBehindReadingAndParser_soundFor
#print axioms VerifiableInference.OnPublicFiles.verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor
#print axioms VerifiableInference.OnPublicFiles.verifierAcceptingNoMoreThanBehindReadingAndParser_sound
#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.ladder_yes
#print axioms VerifiableInference.OnPublicFiles.sound_honest_side
#print axioms VerifiableInference.OnPublicFiles.soundForWith_honest_side
#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.commitment_of_code
#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.core_of
#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.readD_reads

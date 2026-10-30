-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/CompilerTheoremsAtVerify.lean: the two compiler theorems at compile, at any
description: one hash function, a 256-bit commitment, the verifier verify. No value is plugged in
here. The values are plugged in at FinalStatement.lean.

1.  WHAT IS CLAIMED, OF WHAT: this file proves neither completeness nor zero knowledge of the
    protocol. Two propositions are stated of compile, each an implication from named premises.
2.  THE PROVERS: completeness and honest-verifier zero knowledge as interactive oracle proofs, of
    one value, the provers of what compile takes.
3.  THE PUBLIC PREMISES read no prover: PublicPremises.
4.  THE SETTINGS: SettingsPremises.
5.  THE MODEL: ModelTie. THE FORMAT, WITH THE PROVERS: ProversMeetTheFormat.
6.  THE SIMULATOR IS NAMED: index privacy at compiledSimulatorAtVerify, a second clause of the
    proposition on zero knowledge. Public parameters of compile are Unit.
7.  PARAMETERS HERE, TO BE FIXED BEFORE THESE TWO SAY ANYTHING OF THE PROTOCOL: the domain named, with a request in it; Served the served
    requests' instances; the errors as numbers, well below 1; the built description; the byte
    format's own parser, form and writer.
8.  NOT CLAIMED: requests outside the domain · binding at this committer.
-/
import VerifiableInference.Final.CompilerTheorems
import VerifiableInference.MoreStatements
import VerifiableInference.AtEveryRequest
import Johnson.FrontRoad.Front
import Johnson.FrontRoad.CoinsEnough
import Johnson.PV.Fit

set_option autoImplicit false
noncomputable section

namespace VerifiableInference.Compilation
open OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open TypedOracleCompiler.Compile.Batch.Cms (NoRepeat IsOther)
open VerifiableInference.AtEveryRequest (WithinBudget)
open scoped ENNReal

variable (input : Compilable)

/-- The honest side of the compiled scheme at a value of the public reading. -/
abbrev Compilable.sideAt (reading : input.wiring.family.D) :
    AtRecs 256 input.publicSide.protocol (input.wiring.layoutAtReading reading).LeafBody
      input.publicSide.offlineRoundSplits input.publicSide.linkRoundSplits :=
  honestSide (input.wiring.layoutAtReading reading) input.provers (input.settings reading)

/-- What the premises are handed at the base readings. -/
abbrev Compilable.baseInput : VerifiableInference.OnPublicFiles.InnerCompilerInput :=
  (input.publicSide.layoutAt input.wiring.baseDigest input.wiring.baseFurther).input

/-- **What is public**, on the protocol and its layouts alone. -/
structure PublicPremises (N : Budget) (sessionsPerCopy : ℕ) : Prop where
  noCoin : input.wiring.family.Pub.NoCoin
  asks : input.wiring.family.Pub.AsksIn fun _ s => input.wiring.family.Pt s
  once : NoRepeat input.wiring.family.Pub
  spare : ∀ d s, input.wiring.family.Pt s → IsOther (input.wiring.family.m d) s
  reads : ∀ hash : Hash,
    (input.publicSide.filesDigest.andThen fun c => (input.publicSide.furtherReading c).andThen
      fun m => .done (input.wiring.pair c m)).evaluate hash =
      input.wiring.family.Pub.det fun _ => hash
  total : ∀ ck, ∃ code, input.wiring.family.encT ck = some code
  inScope : input.publicSide.filesInScope = true
  /-- At every honest side the first-block test reads a failed try through its first block alone. -/
  firstBlockFits : ∀ side, FactorsAt input.wiring.family side input.firstBlockTest
  forIndexPrivacy : ∀ d, PublicForIndexPrivacy (input.wiring.layoutAtReading d) N
    (input.settings d).furtherCopies sessionsPerCopy (input.settings d).searchLimitOffline
    (input.settings d).searchLimitLink (input.settings d).searchLimitOnline
  forCompleteness : ∀ d, PublicForCompleteness (input.wiring.layoutAtReading d)
    (input.settings d).searchLimitOffline (input.settings d).searchLimitLink
    (input.settings d).searchLimitOnline

/-- **The compiler's settings.** -/
structure SettingsPremises (budget : ℕ) : Prop where
  fit : ∀ d, SettingsFit (input.wiring.layoutAtReading d) input.provers (input.settings d)
  coinRange : ∀ d, coinsRange (input.sideAt d).side ∣ input.coinBound + 1
  withinBudget : WithinBudget (compile input) budget

/-- **The model**: every weight's index is in range, every index that serves is in range, and every
request of the domain whose output is the model's builds an instance, with no further tokens, that
Served holds of at the index of the weights, and from which back reads the request. -/
structure ModelTie (inRange : input.publicSide.Index → Prop)
    (Served : input.publicSide.Index → input.publicSide.Instance → Prop)
    (domain : (compile input).Weights → List Token → List Token → Prop)
    (back : input.publicSide.Instance → List Token × List Token) : Prop where
  range : ∀ weights, inRange (input.publicSide.indexOf weights)
  servedInRange : ∀ i x, Served i x → inRange i
  tie : ∀ w p o, domain w p o → (compile input).IsModelOutput w p o →
    ∃ x, input.baseInput.buildInstance (p, o) [] = some x ∧ Served (input.publicSide.indexOf w) x ∧
      back x = (p, o)

/-- One honest run of a scheme: commit, prove, verify; the key, the proof and the verdict. -/
def honestRunOf {lam : ℕ} {I X W IVK ISK Pf : Type} (A : ZKCP.Arg lam I X W IVK ISK Pf) (i : I) (x : X)
    (w : W) : ZKCP.OComp lam (IVK × Pf × Bool) :=
  (A.C i).bind fun keys => (A.P keys.2 x w).bind fun π =>
    (A.V keys.1 x π).mapO fun b => (keys.1, π, b)

/-- **The provers with the settings and the format**: the run values are sent, and the parser undoes
the writer on what the honest side produces, but for a chance parserError: in an honest run that the
verifier accepts, at every weights and request that builds a served instance. -/
structure ProversMeetTheFormat (inRange : input.publicSide.Index → Prop)
    (Served : input.publicSide.Index → input.publicSide.Instance → Prop)
    (parserError : ℝ≥0∞) : Prop where
  runValues : ∀ d, RunValuesAreSent (input.wiring.layoutAtReading d) input.provers
    (input.settings d) inRange
  parserUpTo : ∀ (w : input.publicSide.model.Weights) (x' : List Token × List Token) x,
    input.baseInput.buildInstance x' [] = some x → Served (input.publicSide.indexOf w) x →
    ZKCP.Pr (honestRunOf (readOne input.wiring.family fun d => (input.sideAt d).side)
        (input.publicSide.indexOf w) x ())
      (fun f => {o | o.2.2 = true ∧
        (input.format.parse x'.1 x'.2
          (input.format.write ([], (lowKey o.1.2, lowPrf o.1.2 o.2.1)))).evaluate f ≠
          ([], (lowKey o.1.2, lowPrf o.1.2 o.2.1))}) ≤ parserError

/-- **THE SIMULATOR AT verify**, by name: the compiled simulators at each reading, wrapped as the
committer and prover are. -/
def compiledSimulatorAtVerify (simulators : RunSimulators input.publicSide.protocol)
    (fixedIndex : input.publicSide.Index) (sessionsPerCopy : ℕ)
    (back : input.publicSide.Instance → List Token × List Token) :=
  frontSimK (PP' := Unit) input.wiring.family input.wiring.fallbackInstance back (fun id _ => id)
    (fun k π => input.format.write ([], (lowKey k, lowPrf k π)))
    (fun d => compiledSimulator (input.wiring.layoutAtReading d) input.provers (input.settings d)
      simulators fixedIndex sessionsPerCopy) fun _ => ()

/-- **COMPLETENESS OF compile**, on a stated set of requests, from the named premises. CompilerAtVerifyProofs.lean
shows it at every description; of a public side that is no description it shows nothing. -/
def CompleteOfCompile (budget : ℕ) : Prop :=
  ∀ (N : Budget) (sessionsPerCopy : ℕ) (inRange : input.publicSide.Index → Prop)
    (Served : input.publicSide.Index → input.publicSide.Instance → Prop)
    (E : CompletenessErrors) (domain : (compile input).Weights → List Token → List Token → Prop)
    (back : input.publicSide.Instance → List Token × List Token) (α parserError : ℝ≥0∞),
    (∀ d, CompleteBeforeHashingAt (input.wiring.layoutAtReading d) input.provers Served E) →
    PublicPremises input N sessionsPerCopy → SettingsPremises input budget →
    ModelTie input inRange Served domain back →
    ProversMeetTheFormat input inRange Served parserError →
    (∀ d, completenessError (input.wiring.layoutAtReading d) input.provers (input.settings d) E ≤ α) →
    CompleteOn (compile input) domain (α + parserError)

/-- **ZERO KNOWLEDGE OF compile**, on a stated set of requests, from the named premises, with the
simulator named in the second clause. CompilerAtVerifyProofs.lean shows it at every description; of a public side that is no description it shows nothing. -/
def ZeroKnowledgeOfCompile (budget : ℕ) : Prop :=
  ∀ (N : Budget) (sessionsPerCopy : ℕ) (inRange : input.publicSide.Index → Prop)
    (Served : input.publicSide.Index → input.publicSide.Instance → Prop)
    (simulators : RunSimulators input.publicSide.protocol) (fixedIndex : input.publicSide.Index)
    (domain : (compile input).Weights → List Token → List Token → Prop)
    (back : input.publicSide.Instance → List Token × List Token) (ζ : ℕ → ℕ → ℝ≥0∞)
    (parserError : ℝ≥0∞),
    (∀ d, HonestVerifierZeroKnowledge (input.wiring.layoutAtReading d).work input.provers simulators
      inRange Served N) →
    PublicPremises input N sessionsPerCopy → SettingsPremises input budget →
    ModelTie input inRange Served domain back →
    ProversMeetTheFormat input inRange Served parserError →
    (∀ d t n, indexPrivacyError (input.wiring.layoutAtReading d) input.provers (input.settings d) N
      sessionsPerCopy t n ≤ ζ t n) →
    ZeroKnowledgeOn (compile input) domain (fun t n => ζ (t + 1) n) ∧
      ZKCP.HasStrongIndexPrivacyWith
        (ZKCP.languageRelation fun w (x : List Token × List Token) =>
          domain w x.1 x.2 ∧ (compile input).IsModelOutput w x.1 x.2)
        (compiledScheme input)
        (compiledSimulatorAtVerify input simulators fixedIndex sessionsPerCopy back)
        fun t n => ζ (t + 1) n

end VerifiableInference.Compilation

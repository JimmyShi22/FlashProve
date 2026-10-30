-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Spec.lean: the statement that index privacy passes, at one query more, to the
shell frontAt, if the scheme with the whole key published has it, with one bound, at every value d
of the type of the public reading's values, and under the further premises of "What is required".
Conditional, of a shell. Two statements (proved in FrontProof.lean), a definition and a lemma.
This head is the home of the terms (at its end), and of the limits that go with any quote, for the
files of Johnson/FrontRoad/ whose heads point here right after their title. Bare file names are
files of that folder.

What this file has.
  Spec.frontPrivacy   the statement for arbitrary parameters: for the scheme frontArg and the
                      simulator frontSim (Front.lean), whatever its verifier is.
  frontAt             frontArg with the definition of VerifierAndGoals.verify (Ladder.lean, at the library's
                      root) as its verifier, at a description D, public files Z, a type of forms
                      with its parser, and an encoder encF of typed proofs into forms. At the key
                      (ID, whole key), the prompt, the output tokens and the proof π it runs verify
                      D Z parse ID prompt output (encF ([], (root key, root proof))). The root key
                      and the root proof are computed from the whole key and π (lowKey, lowPrf,
                      Johnson/WholeKey/Defs.lean).
  frontAt_V           that verifier is the verifier of the library's system of D (VerifierAndGoals.system), in
                      the form of ZKCP/Defs.lean (ArgumentSystem.uploadArgument,
                      VerifiableInference/Agreement.lean), for every prove. By unfolding.
  Spec.frontPrivacyAt
                      the same statement at frontAt.
None of these is one of the release's goal statements, and neither is any statement of a file whose
head points here. Spec.frontPrivacyAt could be read as one: it counts as none.

What is concluded. ZKCP.HasStrongIndexPrivacyWith (ZKCP/Defs.lean), over one hash function, with one
request a call. Written out: for every index of the type J, every valid environment (it chooses each
request from the adversary's whole view so far, only requests of which Rel holds at that index, and
may decline), every adversary with at most t hash queries and every bound N on the number of
requests, the view in the real experiment is within statistical distance ζ (t + 1) N of the view in
the ideal experiment. There the simulator (it has a state) makes the key from Rel.pp of the index
and N, makes each proof from its request, and answers all hash queries itself, with probability 1
none in two ways. The simulator is an explicit term (frontSim).

What is required.
  - Of the public reading: it has no coins; it queries public strings only; none twice; and at every
    d every public string codes a point of the spare oracle under the coding at d. (Four of the
    premises of the library's step for soundness, Johnson/PV/FitO.lean.)
  - At every value d of the type T.D, whether or not the public reading can return it: index privacy
    of the scheme with the whole key published, over the typed oracles, at the input at d (typedAt,
    Johnson/PublicAt/Whole.lean), with one request a call, on a range ok of indices, with one bound
    ζ for all d. The honest sides h d and the simulators Sim d are families in d.
  - Of the map idx of indices: idx w is in the range ok, and R₁.pp (idx w) = hp (Rel.pp w).
  - Of the relation Rel on prompts and outputs: wherever it holds of w and a request x', the inner
    relation R₁ holds of idx w and the instance instOf x' (built from x' with no further tokens; x₀
    where none is built), and back returns x' from that instance.

What must go with any quote of it.
  - Index privacy does not read a scheme's verifier: the two experiments run the committer and the
    prover only. So "its verifier is the definition of VerifierAndGoals.verify" is true of frontAt by
    definition, whatever its committer and prover do. What connects them with that verifier is
    completeness of the same scheme, together with a bound on the honest side's queries. (Without
    such a bound, a prover that finds an accepted proof by search could be complete under a key that
    does not read the index.) Neither is stated here. Without them this statement is easy to
    satisfy: honest sides that send nothing satisfy it (argued; for the premises on provers proved:
    silent_good, Johnson/WholeKey/Foes.lean).
  - frontAt is a shell around the library's verifier. Its committer and prover are this folder's,
    with strategies that are variables, not the description's own (D.commit, D.prove). At the
    description that the release's goal statements use, these two are placeholders: a commitment of
    zeros, and a prover that returns empty files (Johnson/Goal/Description/Honest.lean). frontAt's
    key is (ID, whole key), not a commitment.
  - In Spec.frontPrivacyAt only the verifier is connected with the description. The family T, the
    values c₀ and m₀, the settings s, the map idx and the relation Rel are variables. Nothing here
    says that T's inputs are the description's at (c, m), that s are the files' settings, that idx
    is the library's map from weights, or that Rel speaks of the model. (For these see
    AtBuiltMore.lean and AtWeights.lean; Rel is a variable there too.)
  - It is conditional. Its main premise is the conclusion of a theorem at every d
    (OnBytes.WholeKey.wholeKeyPrivacy, Johnson/WholeKey/Main.lean, under its premises PremW at every
    d). The only parameters at which this folder shows them, under premises on public data alone
    (premAll_laid, LaidAll.lean) have two placeholder provers, which send fixed messages.
  - Keys and proofs are typed: the statement is one level below a scheme whose keys and proofs are
    byte strings. The type of forms, the parser and the encoder encF are variables of which nothing
    is required here. The library's system with D's own form, parser and prover
    (VerifierAndGoals.systemOfRecord) has Form := D.Form and parse := D.parse Z.
  - The simulator's parameters (T, x₀, back, Sim, hp) are fixed before the index: none of them reads
    it.
  - The public parameters are variables (PP, PP', the pp of the two relations, hp). What a simulator
    is given of an index is Rel.pp of it, and frontSim passes hp of that on. For a relation whose
    public parameter is the index itself, with hp the identity, the simulator has the index, and the
    statement says nothing. Whoever quotes it names the public parameters and hp. (In the joins of
    Bundle.lean hp is the map to the one value of Unit: frontSim does not use Rel.pp of the index,
    whatever it is.)
  - The conclusion is at all of J because the image of idx is required to be in the range ok. At a
    range with one index, so at a constant idx, the statement says nothing: the simulators may hold
    that index. Whoever quotes it names the range and idx.
  - The main premise is required at every d of the type. For a shell there is no form that requires
    it at some of the values d only, at the cost of the probability that the reading returns another
    value (for wholeRead there is: privacy_read_on, PremAt.lean). If it fails at one d, however
    unlikely, ζ is at least the error at that d.
  - No further tokens: the instance is built with none, and the verifier is given none. A request
    whose honest proof would carry some is not covered: the premise on Rel speaks of the instance
    that is built with none.
  - The public files are fixed before the hash function is sampled.
  - ζ is a variable: no number is given. Every scheme satisfies a bound of 1 or more. Of two real
    views it says nothing where ζ is one half or more (TwoReal.lean). The same holds of a
    completeness error α.
  - One request a call; one run of the committer; a prover without a state.

Terms.
  scheme          a committer C (from an index to a published key and a prover's key), a prover P
                  and a verifier V, each with oracle access: ZKCP.Arg over one hash function, one
                  request a call (ZKCP/Defs.lean); ZKCP.Gen.Arg over any family of oracles, with
                  batches of requests (ZKCP/Gen.lean).
  index privacy   the library's definition ZKCP.HasStrongIndexPrivacyWith, always with its relation,
                  scheme, simulator and bound. On a range ok of indices (ZKCP/OnRange.lean):
                  ZKCP.StrongPrivacyOn for a ZKCP.Arg, ZKCP.Gen.PrivacyOn for a ZKCP.Gen.Arg.
  typed oracles   the family of oracles with Lean types that the compiled protocol queries. The
                  coding at d (T.m d) is a bijection between strings and points (an oracle, a query,
                  a block of its answer). The spare oracle is a typed oracle that committer, prover
                  and verifier never query.
  public reading  an algorithm without coins (required, not part of the type) that queries the hash
                  function and returns a value d (the digests); T.Pub. A public string is a string
                  that it can query, at some answers of the function. The told part is the part of d
                  that is in a key's code.
                  (Johnson/Top/InnerCompiledVerifierByPublicReading.lean, "Words".)
  family T        LayoutsByPublicReading R: the type T.D of the values d, the public reading, the public strings
                  T.Pt, the coding at d, and the input T.at d at each d.
  honest side     HonestSide: the strategies, search limits and numbers from which the committer and
                  the prover of the scheme with the whole key published are made.
  whole key       The scheme with the whole key published (argW, Johnson/WholeKey/Defs.lean)
                  publishes all that is made once: the first table's root, its out-of-domain sample,
                  the proof on it, and for each copy its root, out-of-domain sample and link proof
                  (FullKey; "table" and "copy": that file's "Words"). typedAt T h d is that scheme at
                  the input T.at d; wholeRead T h is "the public reading, then the scheme at its
                  value" (Johnson/PublicAt/Whole.lean).
  commitment ID   256 bits: the hash function's answer at the code of (told part, root and
                  out-of-domain sample).
  typed proof     VerifierAndGoals.TypedProof: what the library's typed verifier innerCompiledVerifier takes from the
                  prover: further tokens, a root key and a root proof. The further tokens are the
                  prover's; an instance is built from them and from the prompt and the output.
  description     VerifierAndGoals.Description. The release's goal statements use VerifierAndGoals.atSecondHashFunction
                  VerifierAndGoals.theDescription. The built description is descriptionOfDataOnBytes flashProveData (FlashProve.flashProveDescription).
                  The two are equal by a theorem, not by unfolding (theDescription_eq,
                  Johnson/Goal/Description/Description.lean).
  shell           a scheme of this folder (frontArg, frontArgK, and their cases frontAt and
                  frontId). Its committer and prover are this folder's and not the description's
                  own. Its verifier is a variable or, at frontAt and frontId, by definition the
                  definition of VerifierAndGoals.verify. Its verifier alone does not identify it (first limit
                  above).
  member          parameters that satisfy all premises of a conditional statement. "No member
                  known": no such parameters are known.
  re-packing      ZKCP.Wrap (ZKCP/PrivacyWrap.lean): new keys and proofs computed from the old ones,
                  new instances mapped to old ones, with at most one more query of the committer.
-/
import Johnson.FrontRoad.Front
import Ladder
import VerifiableInference.Agreement

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The statement for arbitrary parameters: under the four premises on the public reading, index
privacy of typedAt T h d at every d with one bound ζ on the range ok, and the premises on idx and
Rel, the scheme frontArg has ZKCP.HasStrongIndexPrivacyWith with the simulator frontSim, at the
bound ζ at one query more. Statement only; proved as frontPrivacy in FrontProof.lean. -/
def Spec.frontPrivacy : Prop :=
  ∀ (R : InnerCompilerInput) (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (J PP PP' : Type) (idx : J → R.Index) (x₀ : R.Instance) (back : R.Instance → List Token × List Token)
    (Vf : KeyF R → List Token × List Token → RequestProof 256 R.protocol → ZKCP.OComp 256 Bool)
    (R₁ : ZKCP.IndexedRelation R.Index R.Instance Unit PP)
    (Rel : ZKCP.IndexedRelation J (List Token × List Token) Unit PP') (hp : PP' → PP)
    (Sim : T.D → ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) PP
      (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol))
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : R.Index → Prop),
    T.Pub.NoCoin → (T.Pub.AsksIn fun _ s => T.Pt s) → NoRepeat T.Pub →
    (∀ d s, T.Pt s → IsOther (T.m d) s) →
    (∀ d, ZKCP.Gen.PrivacyOn (ZKCP.Special.toPair R₁) (typedAt T h d) 1 (Sim d) ζ ok) →
    (∀ w, ok (idx w)) → (∀ w, R₁.pp (idx w) = hp (Rel.pp w)) →
    (∀ w x', Rel.rel w x' () →
      R₁.rel (idx w) (instOf R x₀ x') () ∧ back (instOf R x₀ x') = x') →
    ZKCP.HasStrongIndexPrivacyWith Rel (frontArg T h idx x₀ Vf) (frontSim T x₀ back Sim hp)
      fun t N => ζ (t + 1) N

section At
open VerifierAndGoals
variable (D : Description) (Z : PublicFiles) (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
  (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type)
  (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
  (parse : Parser D Z Form) (encF : TypedProof (D.F Z) (D.P Z) → Form)

/-- A shell: frontArg with the definition of VerifierAndGoals.verify as its verifier. Its committer and prover
are this folder's, not the description's own. -/
def frontAt : ZKCP.Arg 256 (ModelWeights s) (List Token × List Token) Unit (KeyF (D.input Z c₀ m₀))
    (T.D × Isk 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits) (RequestProof 256 (D.input Z c₀ m₀).protocol) :=
  frontArg T h idx x₀ fun k x' π =>
    (verify D Z parse k.1 x'.1 x'.2
      (encF ([], (lowKey k.2, lowPrf k.2 π)))).toRandomized.toUpload

/-- The verifier of frontAt is the verifier of the library's system of D, in the form of
ZKCP/Defs.lean, at the ID, the request, and the form that is computed from the whole key and the
proof, for every prove. By unfolding. -/
theorem frontAt_V (k : KeyF (D.input Z c₀ m₀)) (x' : List Token × List Token)
    (π : RequestProof 256 (D.input Z c₀ m₀).protocol) :
    (frontAt D Z c₀ m₀ T h s idx x₀ Form parse encF).V k x' π =
      (system D Z s Form prove parse).uploadArgument.V k.1 x'
        (encF ([], (lowKey k.2, lowPrf k.2 π))) := rfl

end At

/-- Spec.frontPrivacy at the shell frontAt, under the same premises. Statement only; proved as
frontPrivacyAt in FrontProof.lean. It is not one of the release's goal statements. -/
def Spec.frontPrivacyAt : Prop :=
  ∀ (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (x₀ : (D.input Z c₀ m₀).Instance) (back : (D.input Z c₀ m₀).Instance → List Token × List Token)
    (Form : Type) (parse : VerifierAndGoals.Parser D Z Form)
    (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) (PP PP' : Type)
    (R₁ : ZKCP.IndexedRelation (D.input Z c₀ m₀).Index (D.input Z c₀ m₀).Instance Unit PP)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (hp : PP' → PP)
    (Sim : T.D → ZKCP.Gen.Simulator
      (typedOracleFamily 256 (D.input Z c₀ m₀).queryLayout.K (typedOracleCarrier (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody
                               (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) PP
      (FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)
      (D.input Z c₀ m₀).Instance (RequestProof 256 (D.input Z c₀ m₀).protocol))
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : (D.input Z c₀ m₀).Index → Prop),
    T.Pub.NoCoin → (T.Pub.AsksIn fun _ s => T.Pt s) → NoRepeat T.Pub →
    (∀ d s, T.Pt s → IsOther (T.m d) s) →
    (∀ d, ZKCP.Gen.PrivacyOn (ZKCP.Special.toPair R₁) (typedAt T h d) 1 (Sim d) ζ ok) →
    (∀ w, ok (idx w)) → (∀ w, R₁.pp (idx w) = hp (Rel.pp w)) →
    (∀ w x', Rel.rel w x' () →
      R₁.rel (idx w) (instOf (D.input Z c₀ m₀) x₀ x') () ∧
        back (instOf (D.input Z c₀ m₀) x₀ x') = x') →
    ZKCP.HasStrongIndexPrivacyWith Rel (frontAt D Z c₀ m₀ T h s idx x₀ Form parse encF)
      (frontSim T x₀ back Sim hp) fun t N => ζ (t + 1) N

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.frontAt_V

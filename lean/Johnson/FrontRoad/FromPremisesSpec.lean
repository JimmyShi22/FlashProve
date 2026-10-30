-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FromPremisesSpec.lean: two implications that put this folder's theorems together
at a variable honest side. If the premises of index privacy hold at every value of the public
reading, an argument system made for this purpose meets ZeroKnowledgeOn; if the premises of
completeness hold, the same system meets CompleteOn. Definitions and statements; the proofs are in
Johnson/FrontRoad/FromPremises.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What they are not. They prove nothing of any prover, and they are no new fact. The only parameters
at which this folder shows the premises of the first under premises on public data alone have two
placeholder provers, which send fixed messages (Johnson/FrontRoad/LaidAll.lean). This folder shows
no parameters with content for the second, and none for both. "For every honest side" binds a
hypothesis. They are about shownSystem (Johnson/FrontRoad/SlotShown.lean), not about VerifierAndGoals.system
at a description, so neither is a goal on zero knowledge or on completeness (Ladder.lean,
Ladder/Package.lean) at any description. They could be read as goals of the release: they count as
none.

What this file has. Both statements are for every description D, all public files Z, every family T
of inputs over the public reading that has the laws FamilyLaws (Johnson/FrontRoad/AtBuiltMore.lean),
and every family F of honest sides, simulators and numbers over the values d of that reading
(SidesAt, Johnson/FrontRoad/PremAt.lean).
Spec.roadPrivate_of_premAll: suppose that PremW (Johnson/WholeKey/Premises.lean) holds of F at every
d (PremAll), that ζ bounds the error zetaW at every d (ZetaLe), that every index that comes from
weights is in the range ok, that the requests of the set domain are tied to instances of which Yes
holds (TieOn), that NC and NP bound the honest side's typed queries at every d, and that bound + 1
is a multiple of coinsRange at every d. Then the three clauses of RoadPrivate hold.
Spec.completeOn_of_honAll: suppose that Z is in scope, that the premises of completeness hold of F
at every d (HonAll, AlphaLe, Johnson/FrontRoad/HonAt.lean), that the parser undoes the encoder at
accepted honest proofs (UndoOn, Johnson/FrontRoad/Complete.lean), and TieOn and the multiple as
above. Then shownSystem has CompleteOn on domain with error α.

  TieOn domain Yes   every request of domain whose output is the model's builds an instance, with no
      further tokens, that Yes holds of at the index of the weights, and from which back reads the
      request.
  RoadPrivate   three clauses, which are one fact: the second and third follow from the privacy in
      the first. The scheme frontId, which publishes the commitment ID alone, has the three clauses
      of ThreeOfId (Johnson/FrontRoad/IdAlone.lean) for the relation "the request is in domain and
      its output is the model's". shownSystem, read as a scheme, has index privacy for that relation
      with the same explicit simulator, at ζ at one query more. shownSystem meets the library's
      definition of zero knowledge on a stated set of requests
      (VerifiableInference.ZeroKnowledgeOn, VerifiableInference/MoreStatements.lean) on domain, at
      the same bound. That definition has the text of the statement ZeroKnowledge
      (VerifiableInference/Statements.lean) with one more condition on the requests, so it asks
      less. ZeroKnowledge itself is not stated here.

How it fits. Every step is a theorem of this folder; the two statements only put them together, so
that a new honest side needs one application. Johnson/FrontRoad/FromPremisesHomeSpec.lean has the
case of the family homeT b Z and an honest side that does not depend on d;
Johnson/FrontRoad/FromPremisesBothSpec.lean has both lists of premises over one list of variables.
Not among the release's goal statements.

Limits.
  The set domain, the relation Yes, the falls G and the bounds ζ and α are variables of which
      nothing more is asked. A domain that holds of nothing satisfies TieOn, and a Yes that holds of
      nothing empties UndoOn and every clause of HonFit on acceptance: both conclusions then hold
      and say nothing of any proof. A bound ζ says nothing until ζ + ζ < 1, to pass that is not to
      hide, and "below 1" is no bar for α either (Johnson/WholeKey/Half.lean,
      Johnson/WholeKey/Bundle.lean). Parameters that satisfy both lists count only with the domain
      named and a request shown in it, with Yes the true instances, and with both numbers.
  By reading, with no theorem: with falls or abort sets that are everything the clauses of HonAll on
      acceptance ask nothing, and AlphaLe holds only at α ≥ 3; and at an empty Yes and domain,
      placeholder provers, which send fixed messages, satisfy both lists at small α and ζ wherever
      the clause side of HonAll holds; it holds at laidAtN where ℓ is at most the length of
      a leaf's salt (sideFit_laidN, E2E/LinkLaidAny.lean).
  Spec.roadPrivate_of_premAll alone does not bar a useless prover. From any parameters that satisfy
      PremW one gets parameters that satisfy it too, whose sessions' prover always aborts publicly
      and sends nothing. For every relation that holds of some index and instance, at one request or
      more, that honest side has no completeness error below 1 (said here without a theorem); at a
      relation that holds of nothing the error is 0, by definition. The like at
      shownSystem itself: all premises of Spec.roadPrivate_of_premAll pass to the family with that
      prover; and where the parser undoes the encoder at the form of a proof that has no session's
      proof, CompleteOn holds there, on a set with a request that is the model's output, at no error
      below 1 (said here without a theorem).
  The map idx, the settings s, the parser and the encoder are variables of which
      Spec.roadPrivate_of_premAll asks nothing: a map that sends all weights to one index, or an
      encoder that throws the proof away, satisfies it. domain may depend on the weights; then
      whether a request meets it is not hidden (VerifiableInference/MoreStatements.lean).
  D is every description: nothing is asked of the soundness of its verifier, which is a third thing
      beside these two; there is no clause on binding or soundness here. The verifier is
      VerifierAndGoals.verify D Z parse at a variable parser, not at D.parse. At Form := the typed proofs
      UndoOn costs nothing and no byte is spoken of.
  shownSystem is an argument system made for this purpose, into whose verifier field the verifier of
      Ladder.lean is laid. Its randomness, sampler, committer and prover are made for one Z and one
      s. Zero knowledge does not read a verifier.
  The premises of index privacy ask that each interactive simulator has exactly the law of the
      honest output, for each list of the verifier's messages, but for the error numbers in F.
  The search limits in F are variables. At small limits hardly any proof is produced. The bound
      zetaW has no term for a search that runs out; the error of completeness has (alphaAll).
  Of the four clauses of HonAll, law and wires are proved at homeT b Z at every d (lawFit_home,
      wiresFit_home, Johnson/Prover/At/HomeAt.lean); hon is known at idle provers alone, at the
      numbers 0, 1, 1, 1 (honFit_idle_layoutsByPublicReading, Johnson/Prover/At/IdleAt.lean); side asks the lengths
      that the format requires of the honest side's salts and coins, and is proved at laidAtN, for
      ℓ ≤ sMT (sideFit_laidN, E2E/LinkLaidAny.lean). Over typed oracles PremW and the four like
      premises of completeness hold together at a toy alone, which is no case of these two lists
      (bundle_pad2, Johnson/WholeKey/Member2Bundle.lean).
  Every premise on F is asked at every d of the type, whether or not a hash function gives that d.
  One multiple of coinsRange (F.side d) is asked for all d. If the sizes of an honest side's lists
      grow with d without a bound, there is none.
  The counts of hash calls in RoadPrivate are those of frontId. The prover of shownSystem runs the
      committer again for each proof, and no count for shownSystem is concluded. NC and NP have no
      bar.
  CompleteOn speaks of one request under a fresh commitment, ZeroKnowledgeOn of N requests under
      one commitment.
  Spec.completeOn_of_honAll asks that Z is in scope, not that the description is live at Z. Where it
      is not live the verifier of Ladder.lean accepts nothing, so its premises are not to be
      expected to hold there at a Yes with a member and α below 1.
  One run of the committer; one request per proof; no further tokens; the public files, the weights
      and the environment are fixed before the hash function is sampled.
  All limits of Johnson/FrontRoad/IdAlone.lean, SlotShown.lean, Slot.lean, CompleteK.lean and
      Joined.lean.
-/
import Johnson.FrontRoad.IdAlone
import Johnson.FrontRoad.SlotShown

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Letters
variable (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (F : SidesAt T) (s : IntegerTransformer.Settings)
  (idx : ModelWeights s → (D.input Z c₀ m₀).Index) (x₀ : (D.input Z c₀ m₀).Instance)
  (back : (D.input Z c₀ m₀).Instance → List Token × List Token) (Form : Type)
  (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form)
  (domain : ModelWeights s → List Token → List Token → Prop)

/-- Every request of domain whose output is the model's builds an instance, with no further tokens,
that Yes holds of at the index of the weights, and from which back reads the request. -/
def TieOn (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) : Prop :=
  ∀ w p o, domain w p o → VerifierAndGoals.ModelOutput s w p o →
    ∃ x, (D.input Z c₀ m₀).buildInstance (p, o) [] = some x ∧ Yes (idx w) x ∧ back x = (p, o)

/-- The three clauses on index privacy and zero knowledge on a stated set of requests. -/
structure RoadPrivate (bound asked askedEach : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  three : ThreeOfId D Z c₀ m₀ T F s idx x₀ back Form parse encF (shownRel D s domain) asked
    askedEach ζ
  scheme : ZKCP.HasStrongIndexPrivacyWith (shownRel D s domain)
    (shownSystem D Z c₀ m₀ T F.side s idx x₀ Form parse encF bound).uploadArgument
    (frontSimK T x₀ back (fun id _ => id) (fun k π => encF ([], (lowKey k, lowPrf k π))) F.sim
      fun _ => ())
    fun t N => ζ (t + 1) N
  zeroKnowledgeOn : ZeroKnowledgeOn (shownSystem D Z c₀ m₀ T F.side s idx x₀ Form parse encF bound)
    domain fun t N => ζ (t + 1) N

end Letters

/-- Statement only; proved as roadPrivate_of_premAll in Johnson/FrontRoad/FromPremises.lean. An
implication. The only parameters at which this folder shows its premises under premises on public
data alone have two placeholder provers, which send fixed messages. From the premises of index
privacy at every value of the public reading to the three clauses of RoadPrivate. -/
def Spec.roadPrivate_of_premAll : Prop :=
  ∀ (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D) (F : SidesAt T)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (x₀ : (D.input Z c₀ m₀).Instance) (back : (D.input Z c₀ m₀).Instance → List Token × List Token)
    (Form : Type) (parse : VerifierAndGoals.Parser D Z Form)
    (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form)
    (domain : ModelWeights s → List Token → List Token → Prop)
    (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) (ok : (D.input Z c₀ m₀).Index → Prop)
    (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP bound : ℕ),
    FamilyLaws D Z c₀ m₀ T pair → PremAll F ok Yes (fun _ => True) →
    ZetaLe F (fun _ => True) ζ → (∀ w, ok (idx w)) → TieOn D Z c₀ m₀ s idx back domain Yes →
    (∀ d, commitN (D.input Z c₀ m₀).queryLayout (F.side d) ≤ NC) →
    (∀ d, proveN (D.input Z c₀ m₀).queryLayout (F.side d) ≤ NP) →
    (∀ d, coinsRange (F.side d) ∣ bound + 1) →
    RoadPrivate D Z c₀ m₀ T F s idx x₀ back Form parse encF domain bound
      (8 + NC * ((D.input Z c₀ m₀).queryLayout.K + 1) + 1) (NP * ((D.input Z c₀ m₀).queryLayout.K + 1)) ζ

/-- Statement only; proved as completeOn_of_honAll in Johnson/FrontRoad/FromPremises.lean. An
implication. This folder shows no parameters with content for its premises. From the premises of
completeness at every value of the public reading to CompleteOn of the same argument system. -/
def Spec.completeOn_of_honAll : Prop :=
  ∀ (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D) (F : SidesAt T)
    (G : FallsAt F) (s : IntegerTransformer.Settings)
    (idx : ModelWeights s → (D.input Z c₀ m₀).Index) (x₀ : (D.input Z c₀ m₀).Instance)
    (back : (D.input Z c₀ m₀).Instance → List Token × List Token) (Form : Type)
    (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form)
    (domain : ModelWeights s → List Token → List Token → Prop)
    (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) (α : ℝ≥0∞) (bound : ℕ),
    FamilyLaws D Z c₀ m₀ T pair → VerifierAndGoals.InScope Z = true → HonAll G Yes (fun _ => True) →
    AlphaLe G (fun _ => True) α → UndoOn D Z c₀ m₀ T F.side idx Yes parse encF →
    TieOn D Z c₀ m₀ s idx back domain Yes → (∀ d, coinsRange (F.side d) ∣ bound + 1) →
    CompleteOn (shownSystem D Z c₀ m₀ T F.side s idx x₀ Form parse encF bound) domain α

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.TieOn
#print axioms OnBytes.FrontRoad.RoadPrivate
#print axioms OnBytes.FrontRoad.Spec.roadPrivate_of_premAll
#print axioms OnBytes.FrontRoad.Spec.completeOn_of_honAll

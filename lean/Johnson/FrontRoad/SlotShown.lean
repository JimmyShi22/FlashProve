-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SlotShown.lean: the argument system of Johnson/FrontRoad/Slot.lean with the
description's own public parameters. It has six of its ten fields from the system of Ladder.lean;
the other four (randomness, sampler, committer, prover) are the honest side and are slotSystem's.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has. All of it is for every description D, all public files Z, every family T and
every honest side h: nothing is asked of the provers.
shownSystem: an argument system. Six of its ten fields are, by definition, those of VerifierAndGoals.system D
Z s Form prove parse (shown_six): the weights, the public parameters D.Shown with D.shown s, the
type of proofs, the model and the verifier VerifierAndGoals.verify D Z parse. The four others are
slotSystem's: the type of the committer's randomness, its sampler, the committer and the prover.
shown_privacy: index privacy of frontId in the stronger form, for a relation whose public parameters
have the type D.Shown, carries over to shownSystem read as a scheme, with the same relation,
simulator and bound. The premises are those of slot_privacy.
shown_zeroKnowledgeOn: so shownSystem meets the library's definition of zero knowledge on a stated
set of requests (VerifiableInference.ZeroKnowledgeOn, VerifiableInference/MoreStatements.lean), if
frontId has index privacy for the relation "the request is in the set and its output is the model's"
with the public parameters D.shown s. That definition has the text of the statement ZeroKnowledge
(VerifiableInference/Statements.lean) with one more condition on the requests, so it asks less.
ZeroKnowledge itself is not stated here.
shown_completeOn: under the same premises completeness of frontId for that relation carries over to
CompleteOn of shownSystem.

  shownRel domain   that relation.
  shown_upload   shownSystem, read as a scheme, is slotArg.

How it fits. ArgumentSystem.ofArgument (VerifiableInference/OfArgument.lean), on which slotSystem is
built, has the one value of Unit for its public parameters. The system of Ladder.lean has the
description's. Where hp is the map to the one value of Unit (laidIdSim, laidShownSim), frontSimK
uses nothing of the public parameters that it is given, so it serves at every type of public
parameters. At the built description D.Shown is Unit too, by definition (`fixedCommitterAndProver`,
Johnson/Goal/Tie/DescriptionOfData.lean), so there slotSystem and shownSystem differ in spelling alone (by
inspection, not proved). Not among the release's goal statements.

Limits.
  That six fields, the verifier among them, are those of the system of Ladder.lean holds by
      definition, for every committer and prover that are laid into shownSystem. Neither index
      privacy nor zero knowledge reads a verifier. So it gives a statement on hiding no weight.
  At a bound for which bound + 1 is not a multiple of coinsRange (h d) the committer's random
      choices need not be uniform (at bound 0 all are 0). The three theorems ask that it is one.
  The four other fields, which are the honest side, are made for one set of public files Z and one
      set of settings s. A description has one type of randomness and one sampler for all public
      files, while bound may depend on Z. At one Z the four can be laid into a description made for
      that Z (argued, not proved). One description for all Z is not shown.
  The three theorems are implications. They say nothing unless frontId has the property.
  The more D.shown s tells of the weights, the less ZeroKnowledgeOn says; no goal bounds it. At the
      built description it tells nothing: there the honest side is the filler `fixedCommitterAndProver`, whose Shown
      is Unit by definition (Johnson/Goal/Tie/DescriptionOfData.lean; `theHonest`,
      Johnson/Goal/Description/Honest.lean): no theorem here states it.
  The other limits of Johnson/FrontRoad/Slot.lean.
-/
import Johnson.FrontRoad.Slot

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead VerifierAndGoals
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
  (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : Parser D Z Form)
  (encF : TypedProof (D.F Z) (D.P Z) → Form) (bound : ℕ)

/-- **The argument system**: the system of Ladder.lean with slotSystem's randomness, sampler,
committer and prover. -/
def shownSystem : ArgumentSystem where
  Weights := ModelWeights s
  PublicParameters := D.Shown
  publicParameters := D.shown s
  CommitmentRandomness := Fin (bound + 1)
  Proof := Form
  nextToken := modelNextToken s
  sampleCommitmentRandomness :=
    (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).sampleCommitmentRandomness
  commit := (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).commit
  prove := (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).prove
  verify := verify D Z parse

/-- **Six of its ten fields are those of the system of Ladder.lean**, by definition: the weights,
the public parameters and the map to them, the type of proofs, the model and the verifier. The other
four (the type of the committer's randomness, its sampler, the committer and the prover) are
slotSystem's. -/
theorem shown_six
    (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form) :
    (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).Weights =
        (VerifierAndGoals.system D Z s Form prove parse).Weights ∧
      (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).PublicParameters =
        (VerifierAndGoals.system D Z s Form prove parse).PublicParameters ∧
      HEq (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).publicParameters
        (VerifierAndGoals.system D Z s Form prove parse).publicParameters ∧
      (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).Proof =
        (VerifierAndGoals.system D Z s Form prove parse).Proof ∧
      HEq (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).nextToken
        (VerifierAndGoals.system D Z s Form prove parse).nextToken ∧
      HEq (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).verify
        (VerifierAndGoals.system D Z s Form prove parse).verify :=
  ⟨rfl, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl⟩

/-- Read as a scheme, it is slotArg. -/
theorem shown_upload :
    (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).uploadArgument =
      slotArg D Z c₀ m₀ T h s idx x₀ Form parse encF bound :=
  ZKCP.Arg.eq_of_parts
    (ArgumentSystem.uploadArgument_ofArgument_C
      (slotArg D Z c₀ m₀ T h s idx x₀ Form parse encF bound)
      (slotCommit D Z c₀ m₀ T h s idx x₀ Form parse encF bound) (modelNextToken s)
      (ZKCP.Arg.commitsFromCoins_coinsFirst (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) bound))
    (ArgumentSystem.uploadArgument_ofArgument_P
      (slotArg D Z c₀ m₀ T h s idx x₀ Form parse encF bound)
      (slotCommit D Z c₀ m₀ T h s idx x₀ Form parse encF bound) (modelNextToken s))
    rfl

/-- The relation "the request is in the set and its output is the model's", with the description's
public parameters. -/
def shownRel (domain : ModelWeights s → List Token → List Token → Prop) :
    ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit D.Shown where
  rel := fun w x _ => domain w x.1 x.2 ∧ ModelOutput s w x.1 x.2
  pp := D.shown s

/-- **Index privacy carries over**, with the same relation, simulator and bound. -/
theorem shown_privacy
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit D.Shown)
    (Sim : ZKCP.Simulator 256 D.Shown (ZKCP.Digest 256) (List Token × List Token) Form)
    (ζ : ℕ → ℕ → ℝ≥0∞) (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (hp : ZKCP.HasStrongIndexPrivacyWith Rel (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) Sim
      ζ) :
    ZKCP.HasStrongIndexPrivacyWith Rel
      (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).uploadArgument Sim ζ := by
  rw [shown_upload]
  exact ZKCP.HasStrongIndexPrivacyWith.coinsFirst bound
    (slot_coins D Z c₀ m₀ T h s idx x₀ Form parse encF bound noCoin hr) hp

/-- **Zero-knowledge on a set of requests**, in the sense of the library's definition, from index
privacy of frontId for shownRel; an implication. -/
theorem shown_zeroKnowledgeOn (domain : ModelWeights s → List Token → List Token → Prop)
    (Sim : ZKCP.Simulator 256 D.Shown (ZKCP.Digest 256) (List Token × List Token) Form)
    (ζ : ℕ → ℕ → ℝ≥0∞) (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (hp : ZKCP.HasStrongIndexPrivacyWith (shownRel D s domain)
      (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) Sim ζ) :
    ZeroKnowledgeOn (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain ζ :=
  zeroKnowledgeOn_of_privacy (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain ζ Sim
    (shown_privacy D Z c₀ m₀ T h s idx x₀ Form parse encF bound (shownRel D s domain) Sim ζ noCoin
      hr hp)

/-- **Completeness carries over**, with the same error. -/
theorem shown_completeOn (domain : ModelWeights s → List Token → List Token → Prop) (α : ℝ≥0∞)
    (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (hc : ZKCP.HasCompletenessError (shownRel D s domain)
      (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) α) :
    CompleteOn (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain α := by
  refine completeOn_of_completenessError
    (shownSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) (shownRel D s domain) domain
    (fun _ _ _ hDomain hOutput => ⟨hDomain, hOutput⟩) α ?_
  rw [shown_upload]
  exact ZKCP.HasCompletenessError.coinsFirst bound
    (slot_coins D Z c₀ m₀ T h s idx x₀ Form parse encF bound noCoin hr) hc

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.shown_six
#print axioms OnBytes.FrontRoad.shown_upload
#print axioms OnBytes.FrontRoad.shown_privacy
#print axioms OnBytes.FrontRoad.shown_zeroKnowledgeOn
#print axioms OnBytes.FrontRoad.shown_completeOn

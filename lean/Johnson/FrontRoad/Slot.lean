-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Slot.lean: from the scheme whose key is the commitment ID alone (frontId) to an
argument system (VerifiableInference.ArgumentSystem) that is made for this purpose, with the weights
and the model of the system of Ladder.lean, into whose verifier field the verifier of Ladder.lean is
laid; completeness and index privacy carry over with the same bounds.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has. All of it is for every description D, all public files Z, every family T and
every honest side h: nothing is asked of the provers.
slotSystem: an argument system (VerifiableInference.ArgumentSystem). Its weights are the model
weights, its model is the integer model, a proof is a form, and its verifier field is VerifierAndGoals.verify
D Z parse (slot_verify). Its committer samples one number from 0, …, bound and then runs frontId's
committer at that number. Its prover is given the weights and that number: it runs the committer
again at that number, and then frontId's prover with what the committer kept.
slot_privacy: if the public reading samples nothing and bound + 1 is a multiple of coinsRange (h d)
for every d (Johnson/FrontRoad/CoinsEnough.lean), then index privacy of frontId in the stronger form
carries over to slotSystem, read as a scheme (uploadArgument), with the same relation, the same
simulator and the same bound.
slot_zeroKnowledgeOn_of_relationOn: so slotSystem meets the library's definition of zero knowledge
on a stated set of requests (VerifiableInference.ZeroKnowledgeOn,
VerifiableInference/MoreStatements.lean). That definition has the text of the statement
ZeroKnowledge (VerifiableInference/Statements.lean) with one more condition on the requests, so it
asks less. ZeroKnowledge itself is not stated here. The premise is that frontId has index privacy
for the relation "the request is in the set and its output is the model's".
slot_completeOn_of_relationOn: under the same two premises, completeness of frontId for that
relation carries over to CompleteOn of slotSystem.
slot_zeroKnowledgeOn, slot_completeOn: the same from the relation "the request is in the set" alone.
That premise asks more, since it speaks also of requests whose output is not the model's. For
completeness it is not to be expected to hold beside a sound verifier, unless the set itself holds
only requests with the model's output (argued, not proved).

  slotArg   frontId with the committer's random choices sampled first (Arg.coinsFirst,
      ZKCP/CoinsFirstArg.lean). slotCommit: its committer at a given number.
  slot_upload   slotSystem, read as a scheme, is slotArg.
  slot_coins   the premise of the library's step: bound + 1 is enough for frontId's committer.
  drawsNoCoin_det, deterministicOf_det   a deterministic algorithm, in the form of ZKCP/Defs.lean,
      samples nothing, and is given back by deterministicOf.

How it fits. Other theorems of this folder (`frontId`, FrontId.lean) are about a scheme whose
prover's key has another type than in the system of Ladder.lean. Here the prover's key has the form
that it has there, the weights with the committer's randomness; the type of that randomness is
another. The steps are the library's own: Arg.coinsFirst, ArgumentSystem.ofArgument and their
theorems (VerifiableInference/OfArgument.lean). Four files import this one:
Johnson/FrontRoad/SlotShown.lean, Johnson/Face/Compiler.lean (the file of `compile`),
Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestFront.lean and Johnson/CompletenessAndZeroKnowledge/SlotBudget.lean. Not one of the release's goal
statements.

Limits.
  That the verifier field of slotSystem is the verifier of Ladder.lean says nothing about its
      committer and prover:
      slot_verify has no premise, and neither index privacy nor zero knowledge reads a verifier.
  The theorems ask one multiple of coinsRange (h d) for all values d of the public reading. If the
      sizes of an honest side's lists grow with d without a bound, there is none. That range 1 is
      not enough as soon as a list has two entries is not_enough_commitW
      (Johnson/FrontRoad/CoinsEnough.lean). That zero knowledge fails at such a bound is not proved.
  The committer and prover of a description may not use choice (Ladder.lean, head, 9). Nothing here
      keeps an honest side h from using it.
  slotSystem has the weights, model, type of proofs and verifier of VerifierAndGoals.system at D. Its public
      parameters are the one value of Unit, and its randomness, sampler, committer and prover, which
      are the honest side, are this file's, made for one set of public files Z and one set of
      settings s. A description has one type of randomness for all public files, and bound may
      depend on Z. At one Z the four can be laid into a description made for that Z (argued, not
      proved). One description for all Z is not shown.
  The five theorems on privacy, zero knowledge and completeness are implications. They say nothing
      unless frontId has the property.
  None of them is VerifierAndGoals.PackageZeroKnowledge (Ladder/Package.lean) at any description. That speaks
      of systemOfRecord, at the settings that the reader returns at Z.
  All bounds are probabilities that are also over the sampled number. They say nothing of the
      committer at a number that somebody has chosen (see ZKCP/CoinsFirstArg.lean on this).
  Neither the committer nor the prover of slotSystem reads the field nextToken: the model is laid
      into the system as the verifier is.
  In ZeroKnowledgeOn the simulator is under "there is". slot_privacy names it.
  In slot_privacy the public parameters are a variable: where the public parameter is the index the
      statement says nothing (Johnson/FrontRoad/Spec.lean).
  The prover runs the committer again for each proof, so it makes the committer's queries each time.
  The number holds every random choice of the committer: see Johnson/FrontRoad/CoinsEnough.lean.
-/
import Johnson.FrontRoad.FrontId
import Johnson.FrontRoad.CoinsEnough
import ZKCP.CoinsFirstArg
import VerifiableInference.OfArgument

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead VerifierAndGoals
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- A deterministic algorithm, in the form of ZKCP/Defs.lean, samples nothing. -/
theorem drawsNoCoin_det {α : Type} :
    ∀ a : DeterministicAlgorithm α, a.toRandomized.toUpload.DrawsNoCoin
  | .done _ => trivial
  | .query _ next => fun answer => drawsNoCoin_det (next answer)

/-- deterministicOf gives a deterministic algorithm back. -/
theorem deterministicOf_det {α : Type} :
    ∀ a : DeterministicAlgorithm α, deterministicOf a.toRandomized.toUpload = a
  | .done _ => rfl
  | .query input next => by
    show DeterministicAlgorithm.query input
      (fun answer => deterministicOf (next answer).toRandomized.toUpload) = _
    exact congrArg _ (funext fun answer => deterministicOf_det (next answer))

variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
  (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : Parser D Z Form)
  (encF : TypedProof (D.F Z) (D.P Z) → Form) (bound : ℕ)

/-- frontId with the committer's random choices sampled first, as one number from 0, …, bound. The
prover's key is the weights with that number. -/
def slotArg : ZKCP.Arg 256 (ModelWeights s) (List Token × List Token) Unit (ZKCP.Digest 256)
    (ModelWeights s × Fin (bound + 1)) Form :=
  (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).coinsFirst bound

/-- frontId's committer at a given number: the commitment ID. -/
def slotCommit (w : ModelWeights s) (coins : Fin (bound + 1)) : ZKCP.OComp 256 (ZKCP.Digest 256) :=
  (((frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).C w).withCoins coins.val).mapO Prod.fst

/-- **The argument system.** At a bound for which bound + 1 is not a multiple of coinsRange (h d),
the committer's random choices need not be uniform (at bound 0 all are 0, so the commitment is a
function of the weights and the hash function, which whoever guesses the weights can compute and
compare). The theorems on privacy, zero knowledge and completeness below ask that it is a multiple.
slot_verify and slot_upload hold at every bound. -/
def slotSystem : ArgumentSystem :=
  ArgumentSystem.ofArgument (slotArg D Z c₀ m₀ T h s idx x₀ Form parse encF bound)
    (slotCommit D Z c₀ m₀ T h s idx x₀ Form parse encF bound) (modelNextToken s)

/-- **Its verifier field is the verifier of Ladder.lean.** The equation holds for every committer
and prover that are laid into slotSystem, so many argument systems have this verifier. One more is
the system of Ladder.lean at the description's own placeholders, whose committer returns zeros and
whose prover hands over empty files. So the equation gives a statement on hiding no weight. -/
theorem slot_verify :
    (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).verify = verify D Z parse :=
  funext fun c => funext fun p => funext fun o => funext fun form =>
    deterministicOf_det (verify D Z parse c p o form)

/-- Read as a scheme, it is slotArg. -/
theorem slot_upload :
    (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).uploadArgument =
      slotArg D Z c₀ m₀ T h s idx x₀ Form parse encF bound :=
  ArgumentSystem.uploadArgument_ofArgument _ _ _
    (ZKCP.Arg.commitsFromCoins_coinsFirst (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) bound)
    fun c x' form => drawsNoCoin_det (verify D Z parse c x'.1 x'.2 form)

/-- bound + 1 is enough for frontId's committer at all weights. -/
theorem slot_coins (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (w : ModelWeights s) :
    ((frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).C w).CoinsSuffice (bound + 1) :=
  coinsSuffice_frontK T h idx x₀ _ _ _ (bound + 1) noCoin hr w

/-- **Index privacy carries over**, with the same relation, simulator and bound. -/
theorem slot_privacy {PP' : Type}
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (Sim : ZKCP.Simulator 256 PP' (ZKCP.Digest 256) (List Token × List Token) Form)
    (ζ : ℕ → ℕ → ℝ≥0∞) (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (hp : ZKCP.HasStrongIndexPrivacyWith Rel (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) Sim
      ζ) :
    ZKCP.HasStrongIndexPrivacyWith Rel
      (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).uploadArgument Sim ζ := by
  rw [slot_upload]
  exact ZKCP.HasStrongIndexPrivacyWith.coinsFirst bound
    (slot_coins D Z c₀ m₀ T h s idx x₀ Form parse encF bound noCoin hr) hp

/-- **Zero knowledge on a stated set of requests** (VerifiableInference.ZeroKnowledgeOn), from index
privacy of frontId for the relation "the request is in the set and its output is the model's". This
is the form to use with provers that answer true requests alone. -/
theorem slot_zeroKnowledgeOn_of_relationOn
    (domain : ModelWeights s → List Token → List Token → Prop)
    (Sim : ZKCP.Simulator 256 Unit (ZKCP.Digest 256) (List Token × List Token) Form)
    (ζ : ℕ → ℕ → ℝ≥0∞) (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (hp : ZKCP.HasStrongIndexPrivacyWith
      (ZKCP.languageRelation fun w (x : List Token × List Token) =>
        domain w x.1 x.2 ∧ ModelOutput s w x.1 x.2)
      (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) Sim ζ) :
    ZeroKnowledgeOn (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain ζ :=
  zeroKnowledgeOn_ofArgument_of_relationOn _ _ _
    (ZKCP.Arg.commitsFromCoins_coinsFirst (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) bound)
    (fun c x' form => drawsNoCoin_det (verify D Z parse c x'.1 x'.2 form)) domain ζ Sim
    (ZKCP.HasStrongIndexPrivacyWith.coinsFirst bound
      (slot_coins D Z c₀ m₀ T h s idx x₀ Form parse encF bound noCoin hr) hp)

/-- The same from index privacy for the relation "the request is in the set" alone. That premise
asks more: it speaks also of requests whose output is not the model's. -/
theorem slot_zeroKnowledgeOn (domain : ModelWeights s → List Token → List Token → Prop)
    (Sim : ZKCP.Simulator 256 Unit (ZKCP.Digest 256) (List Token × List Token) Form)
    (ζ : ℕ → ℕ → ℝ≥0∞) (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (hp : ZKCP.HasStrongIndexPrivacyWith
      (ZKCP.languageRelation fun w (x : List Token × List Token) => domain w x.1 x.2)
      (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) Sim ζ) :
    ZeroKnowledgeOn (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain ζ :=
  zeroKnowledgeOn_ofArgument _ _ _
    (ZKCP.Arg.commitsFromCoins_coinsFirst (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) bound)
    (fun c x' form => drawsNoCoin_det (verify D Z parse c x'.1 x'.2 form)) domain ζ Sim
    (ZKCP.HasStrongIndexPrivacyWith.coinsFirst bound
      (slot_coins D Z c₀ m₀ T h s idx x₀ Form parse encF bound noCoin hr) hp)

/-- **Completeness carries over**, with the same error, from completeness of frontId for the
relation "the request is in the set and its output is the model's". -/
theorem slot_completeOn_of_relationOn
    (domain : ModelWeights s → List Token → List Token → Prop) (α : ℝ≥0∞)
    (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (hc : ZKCP.HasCompletenessError
      (ZKCP.languageRelation fun w (x : List Token × List Token) =>
        domain w x.1 x.2 ∧ ModelOutput s w x.1 x.2)
      (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) α) :
    CompleteOn (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain α :=
  completeOn_ofArgument_of_relationOn _ _ _
    (ZKCP.Arg.commitsFromCoins_coinsFirst (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) bound)
    (fun c x' form => drawsNoCoin_det (verify D Z parse c x'.1 x'.2 form)) domain α
    (ZKCP.HasCompletenessError.coinsFirst bound
      (slot_coins D Z c₀ m₀ T h s idx x₀ Form parse encF bound noCoin hr) hc)

/-- The same from completeness for the relation "the request is in the set" alone. That premise asks
more: it speaks also of requests whose output is not the model's. A sound verifier rejects such
requests but for its error, so beside one the premise is not to be expected to hold unless the set
itself holds only requests with the model's output (argued, not proved). -/
theorem slot_completeOn (domain : ModelWeights s → List Token → List Token → Prop) (α : ℝ≥0∞)
    (noCoin : T.Pub.NoCoin) (hr : ∀ d, coinsRange (h d) ∣ bound + 1)
    (hc : ZKCP.HasCompletenessError
      (ZKCP.languageRelation fun w (x : List Token × List Token) => domain w x.1 x.2)
      (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) α) :
    CompleteOn (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain α :=
  completeOn_ofArgument _ _ _
    (ZKCP.Arg.commitsFromCoins_coinsFirst (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) bound)
    (fun c x' form => drawsNoCoin_det (verify D Z parse c x'.1 x'.2 form)) domain α
    (ZKCP.HasCompletenessError.coinsFirst bound
      (slot_coins D Z c₀ m₀ T h s idx x₀ Form parse encF bound noCoin hr) hc)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.drawsNoCoin_det
#print axioms OnBytes.FrontRoad.deterministicOf_det
#print axioms OnBytes.FrontRoad.slot_verify
#print axioms OnBytes.FrontRoad.slot_upload
#print axioms OnBytes.FrontRoad.slot_coins
#print axioms OnBytes.FrontRoad.slot_privacy
#print axioms OnBytes.FrontRoad.slot_zeroKnowledgeOn_of_relationOn
#print axioms OnBytes.FrontRoad.slot_completeOn_of_relationOn
#print axioms OnBytes.FrontRoad.slot_zeroKnowledgeOn
#print axioms OnBytes.FrontRoad.slot_completeOn

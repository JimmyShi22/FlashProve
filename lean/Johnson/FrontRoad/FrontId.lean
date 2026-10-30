-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FrontId.lean: the shell frontId, the case of frontArgK (FrontK.lean) in which the
published key is the commitment ID alone. Its verifier is, by definition, the definition of
VerifierAndGoals.verify, and its committer and prover are this folder's, not the description's own. A
definition, an equation by unfolding, and a corollary of frontPrivacyK (FrontProof.lean).
Conditional, of a shell, and index privacy alone.
Terms and the limits that go with any quote: Spec.lean.

What this file has.
  frontId          frontArgK at κ := the ID alone and ϖ k π := encF ([], (root key, root proof)),
                   computed from the whole key k and the proof π (lowKey, lowPrf,
                   Johnson/WholeKey/Defs.lean). Of what is made once, all but the other copies'
                   entries is given to encF in every proof, as in the library's system: the ID is
                   not all that a verifier is sent.
  frontId_V        its verifier is (VerifierAndGoals.system D Z s Form prove parse).uploadArgument.V, as a
                   function of commitment, request and form, for every prove. By unfolding.
  privacy_frontId  Under the premises of Spec.frontPrivacyK: ZKCP.HasStrongIndexPrivacyWith at all
                   weights, with the simulator frontSimK and the bound ζ at one query more.

Limits. Whoever quotes it gives these, and all that the heads of Spec.lean and FrontK.lean list.
The only parameters at which this folder shows PremW at every d, under premises on public data
alone, which gives the main premise, have two placeholder provers, which send fixed messages
(premAll_laid, LaidAll.lean). They are at the built description with the number of the honest
committer's coins set anew (flashProveDescription.reBound b, AtHomeT.lean).
It is not the library's system. frontId has that system's types of index, key (a commitment, 256
bits), instance (a prompt with output tokens), witness and proof (a form), and its verifier. The
prover's key differs, and committer and prover are this folder's, with strategies that are variables
(Spec.lean, "frontAt is a shell").
The public parameters are variables: where the public parameter is the index the statement says
nothing (Spec.lean).
In this file index privacy is alone, and alone it is easy to satisfy. It does not read a verifier,
so frontId_V holds by definition, whatever committer and prover do. What connects them with that
verifier is completeness of the same scheme, with a bound on the honest side's queries: not here
(conditional theorems: CompleteK.lean; the join: MeetsId, Joined.lean).
privacy_frontId is not one of the release's goal statements. It could be read as one: it counts as
none.
-/
import Johnson.FrontRoad.FrontProof

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
  (encF : TypedProof (D.F Z) (D.P Z) → Form)

/-- A shell: frontArgK with the commitment ID alone as the published key and a form as a proof. Its
verifier is, by definition, the definition of VerifierAndGoals.verify, and its committer and prover are this
folder's, not the description's own. -/
def frontId : ZKCP.Arg 256 (ModelWeights s) (List Token × List Token) Unit Commitment
    (FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits ×
      (T.D × Isk 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
        (D.input Z c₀ m₀).linkRoundSplits)) Form :=
  frontArgK T h idx x₀ (fun id _ => id) (fun k π => encF ([], (lowKey k, lowPrf k π)))
    fun c x' form => (verify D Z parse c x'.1 x'.2 form).toRandomized.toUpload

/-- The verifier of frontId is the verifier of the library's system of D, in the form of
ZKCP/Defs.lean, for every prove. By unfolding. -/
theorem frontId_V
    (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form) :
    (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).V =
      (system D Z s Form prove parse).uploadArgument.V := rfl

/-- Under the premises of Spec.frontPrivacyK (FrontK.lean), index privacy passes to the shell
frontId, at one query more. Conditional, of a shell, index privacy alone. A case of
frontPrivacyK. -/
theorem privacy_frontId (back : (D.input Z c₀ m₀).Instance → List Token × List Token) {PP PP' : Type}
    (R₁ : ZKCP.IndexedRelation (D.input Z c₀ m₀).Index (D.input Z c₀ m₀).Instance Unit PP)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (hp : PP' → PP)
    (Sim : T.D → ZKCP.Gen.Simulator
      (typedOracleFamily 256 (D.input Z c₀ m₀).queryLayout.K (typedOracleCarrier (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody
                               (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) PP
      (FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)
      (D.input Z c₀ m₀).Instance (RequestProof 256 (D.input Z c₀ m₀).protocol))
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : (D.input Z c₀ m₀).Index → Prop) (noCoin : T.Pub.NoCoin)
    (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.PrivacyOn (ZKCP.Special.toPair R₁) (typedAt T h d) 1 (Sim d) ζ ok)
    (hok : ∀ w, ok (idx w)) (hpp : ∀ w, R₁.pp (idx w) = hp (Rel.pp w))
    (hrel : ∀ w x', Rel.rel w x' () →
      R₁.rel (idx w) (instOf (D.input Z c₀ m₀) x₀ x') () ∧
        back (instOf (D.input Z c₀ m₀) x₀ x') = x') :
    ZKCP.HasStrongIndexPrivacyWith Rel (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF)
      (frontSimK T x₀ back (fun id _ => id) (fun k π => encF ([], (lowKey k, lowPrf k π))) Sim hp)
      fun t N => ζ (t + 1) N :=
  frontPrivacyK (D.input Z c₀ m₀) T h _ _ _ PP PP' idx x₀ back _ _ _ R₁ Rel hp Sim ζ ok noCoin asks
    once spare hA hok hpp hrel

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.frontId_V
#print axioms OnBytes.FrontRoad.privacy_frontId

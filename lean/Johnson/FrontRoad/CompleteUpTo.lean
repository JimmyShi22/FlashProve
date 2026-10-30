-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CompleteUpTo.lean: the shells frontAt and frontId are complete with the error α +
γ, under the premises of Spec.frontComplete (Complete.lean) with UndoUpTo γ in place of UndoOn.
Conditional, no member known, of a shell. γ bounds the probability, over the hash function and all
coins, that the honest execution is accepted by readOne's verifier and yet the parser does not
return the typed proof.
Terms and the limits that go with any quote: Spec.lean.

What this file has.
  honestTriple   For any scheme, the experiment: commit; prove; verify; return the key, the proof
      and the verifier's bit. UndoUpTo takes it at readOne.
  UndoUpTo … γ   For every index and every request that builds a true instance: the probability that
      the bit is "accept" and the parser, under the same hash function, does not return the typed
      proof is at most γ. undoUpTo_of_on: UndoOn implies UndoUpTo at γ = 0.
  Spec.frontCompleteUpTo, frontCompleteUpTo   The statement and its proof: under the title's
      premises, frontAt is complete with the error α + γ. frontIdCompleteUpTo: the same for frontId.
  pr_frontK_le_add   For any scheme over one hash function, any form of key and proof, another
      verifier Vf and any event Bad on (hash function, key, proof). Suppose that outside Bad, where
      the old verifier can accept, Vf rejects no more often than the old verifier. Then the new
      experiment fails no more often than the old one, up to the probability that the honest
      execution is accepted and Bad holds. The proof follows that of pr_frontK_le (CompleteK.lean),
      with a union bound in place of the step at each proof.

Limits. Those of Complete.lean and CompleteK.lean. γ is a variable: no number is given. Whether
UndoUpTo holds for the description's own form and parser at a small γ is not proved. Nothing on
hiding or binding is proved here.

How it fits. UndoOn requires its condition under every hash function, at every accepted proof that
the honest side can produce there. One hash function under which one accepted honest proof is not
returned makes that premise false, however rare such a function is. A parser of bytes never returns
some typed values (a number that does not fit its field; a reserved value), and whether an honest
execution can produce one may depend on the hash function's answers (argued, not proved). So the
condition is required here under a sampled hash function, up to a probability, which is added to the
error. The joins (Bundle.lean, Joined.lean) require UndoOn.
-/
import Johnson.FrontRoad.CompleteK

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The honest execution with its verifier's bit: commit; prove; verify; return the key, the proof
and the bit. -/
def honestTriple {lam : ℕ} {I X W IVK ISK Pf : Type} (A : ZKCP.Arg lam I X W IVK ISK Pf) (i : I)
    (x : X) (w : W) : ZKCP.OComp lam (IVK × Pf × Bool) :=
  (A.C i).bind fun keys => (A.P keys.2 x w).bind fun π =>
    (A.V keys.1 x π).mapO fun b => (keys.1, π, b)

/-- The parser undoes the encoder up to γ, under a sampled hash function. For every index and every
request x' that builds an instance x with Tr (idx w) x: in honestTriple of readOne, the probability
that the bit is true and the parser, under the same hash function, does not return the typed proof
is at most γ. -/
def UndoUpTo (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    {J : Type} (idx : J → (D.input Z c₀ m₀).Index)
    (Tr : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) {Form : Type}
    (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form)
    (γ : ℝ≥0∞) : Prop :=
  ∀ (w : J) (x' : List Token × List Token) x, (D.input Z c₀ m₀).buildInstance x' [] = some x →
    Tr (idx w) x →
      ZKCP.Pr (honestTriple (readOne T h) (idx w) x ()) (fun f => {o | o.2.2 = true ∧
        (parse x'.1 x'.2 (encF ([], (lowKey o.1.2, lowPrf o.1.2 o.2.1)))).evaluate f ≠
          ([], (lowKey o.1.2, lowPrf o.1.2 o.2.1))}) ≤ γ

/-- States that frontAt is complete with the error α + γ under the premises of Spec.frontComplete
(Complete.lean), with UndoUpTo γ in place of UndoOn. Conditional, no member known, of a shell.
Statement only; proved as frontCompleteUpTo below. -/
def Spec.frontCompleteUpTo : Prop :=
  ∀ (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : VerifierAndGoals.Parser D Z Form)
    (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) (pair : Digest → D.More → T.D)
    (PP PP' : Type)
    (R₁ : ZKCP.IndexedRelation (D.input Z c₀ m₀).Index (D.input Z c₀ m₀).Instance Unit PP)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (α γ : ℝ≥0∞),
    T.Pub.NoCoin → (T.Pub.AsksIn fun _ s => T.Pt s) → NoRepeat T.Pub →
    (∀ d s, T.Pt s → IsOther (T.m d) s) →
    (∀ c m commitment prompt output (proof : VerifierAndGoals.TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof) →
    (∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash) →
    VerifierAndGoals.InScope Z = true →
    UndoUpTo D Z c₀ m₀ T h idx (fun i x => R₁.rel i x ()) parse encF γ →
    (∀ ck, ∃ code, T.encT ck = some code) →
    (∀ d, ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair R₁) (typedAt T h d) 1 α) →
    (∀ w x', Rel.rel w x' () →
      ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ R₁.rel (idx w) x ()) →
    ZKCP.HasCompletenessError Rel (frontAt D Z c₀ m₀ T h s idx x₀ Form parse encF) (α + γ)

/-! ## The union bound -/

section Front
variable {lam : ℕ} {I X X' W IVK K2 K' ISK Pf P' : Type}

/-- The step at one key and one proof. If q rejects no more often than p whenever p can accept and
bad is false, then q rejects at most as often as p, plus the probability that p accepts and bad
holds. -/
theorem prob_reject_le_add (p q : PMF Bool) (bad : Prop)
    (h : true ∈ p.support → ¬ bad →
      ZKCP.prob q {b | b = false} ≤ ZKCP.prob p {b | b = false}) :
    ZKCP.prob q {b | b = false} ≤
      ZKCP.prob p {b | b = false} + ZKCP.prob p {b | b = true ∧ bad} := by
  have hc : ({b : Bool | b = false}ᶜ : Set Bool) = {b | b = true} := by
    ext b
    cases b <;> simp
  by_cases hb : bad
  · have e : {b : Bool | b = true ∧ bad} = {b | b = true} := by
      ext b
      simp [hb]
    rw [e, ← hc, ZKCP.prob_add_compl]
    exact ZKCP.prob_le_one _ _
  · by_cases ht : true ∈ p.support
    · exact le_trans (h ht hb) le_self_add
    · have h0 : ZKCP.prob p {b | b = true} = 0 := by
        unfold ZKCP.prob
        rw [PMF.toOuterMeasure_apply_eq_zero_iff]
        rw [Set.disjoint_left]
        intro b hbs hbt
        exact ht ((show b = true from hbt) ▸ hbs)
      have h1 : ZKCP.prob p {b | b = false} = 1 := by
        have := ZKCP.prob_add_compl p {b | b = false}
        rwa [hc, h0, add_zero] at this
      rw [h1]
      exact le_trans (ZKCP.prob_le_one _ _) le_self_add

/-- pr_frontK_le (CompleteK.lean) up to an event Bad on (hash function, key, proof). If, where the
old verifier can accept and Bad is false, Vf rejects no more often than the old verifier (hV), the
new completeness experiment fails at most as often as the old one, plus the probability that the
honest execution is accepted and Bad holds. -/
theorem pr_frontK_le_add (A : ZKCP.Arg lam I X W IVK ISK Pf) (code : IVK → Option ZKCP.Str)
    (g : IVK → K2) (κ : ZKCP.Digest lam → K2 → K') (ϖ : K2 → Pf → P')
    (Vf : K' → X' → P' → ZKCP.OComp lam Bool) (i : I) (x : X) (x' : X') (w : W)
    (Bad : ZKCP.Oracle lam → IVK → Pf → Prop)
    (hV : ∀ f keys π, true ∈ ((A.V keys x π).run f).support → ¬ Bad f keys π →
      ZKCP.prob ((Vf (κ (ZKCP.digestUnder f code keys) (g keys)) x' (ϖ (g keys) π)).run f)
          {b | b = false} ≤
        ZKCP.prob ((A.V keys x π).run f) {b | b = false}) :
    ZKCP.Pr (((A.C i).bind fun keys =>
        (ZKCP.keyDigest code keys.1).mapO fun dg =>
          (κ dg (g keys.1), (g keys.1, keys.2))).bind fun keys =>
          ((A.P keys.2.2 x w).mapO (ϖ keys.2.1)).bind fun π => Vf keys.1 x' π)
        (fun _ => {b | b = false}) ≤
      ZKCP.Pr (ZKCP.completenessExp A i x w) (fun _ => {b | b = false}) +
        ZKCP.Pr (honestTriple A i x w) fun f => {o | o.2.2 = true ∧ Bad f o.1 o.2.1} := by
  have hm : Measurable fun f : ZKCP.Oracle lam =>
      ZKCP.PrCoins f (ZKCP.completenessExp A i x w) {b | b = false} :=
    ZKCP.measurable_prob_run _ _
  refine le_trans ?_ (le_of_eq (MeasureTheory.lintegral_add_left hm _))
  refine MeasureTheory.lintegral_mono fun f => ?_
  show ZKCP.prob ((((A.C i).bind fun keys =>
        (ZKCP.keyDigest code keys.1).mapO fun dg =>
          (κ dg (g keys.1), (g keys.1, keys.2))).bind fun keys =>
          ((A.P keys.2.2 x w).mapO (ϖ keys.2.1)).bind fun π => Vf keys.1 x' π).run f)
        {b | b = false} ≤
    ZKCP.prob (((A.C i).bind fun keys =>
      (A.P keys.2 x w).bind fun π => A.V keys.1 x π).run f) {b | b = false} +
    ZKCP.prob (((A.C i).bind fun keys => (A.P keys.2 x w).bind fun π =>
      (A.V keys.1 x π).mapO fun b => (keys.1, π, b)).run f)
        {o | o.2.2 = true ∧ Bad f o.1 o.2.1}
  rw [ZKCP.run_bind, run_C_frontK, ZKCP.prob_bind, ZKCP.expect_map, ZKCP.run_bind, ZKCP.prob_bind,
    ZKCP.run_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_add _ fun keys => ?_
  show ZKCP.prob ((((A.P keys.2 x w).mapO (ϖ (g keys.1))).bind fun π =>
      Vf (κ (ZKCP.digestUnder f code keys.1) (g keys.1)) x' π).run f) {b | b = false} ≤ _
  rw [ZKCP.run_bind, ZKCP.OComp.run_mapO, ZKCP.prob_bind, ZKCP.expect_map, ZKCP.run_bind,
    ZKCP.prob_bind, ZKCP.run_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_add _ fun π => ?_
  rw [ZKCP.OComp.run_mapO, ZKCP.prob_map]
  exact prob_reject_le_add _ _ (Bad f keys.1 π) (hV f keys.1 π)

end Front

/-! ## At the schemes of this folder -/

section Read
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {J K' P' : Type} (idx : J → R.Index) (x₀ : R.Instance)
  (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
  (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)

/-- The same for frontArgK against readOne, if instOf R x₀ x' = x (hi). -/
theorem pr_frontArgK_le_add (w : J) (x' : List Token × List Token) (x : R.Instance)
    (hi : instOf R x₀ x' = x) (Bad : ZKCP.Oracle 256 → KeyT R → RequestProof 256 R.protocol → Prop)
    (hV : ∀ f (ck : KeyT R) π, true ∈ (((readOne T h).V ck x π).run f).support → ¬ Bad f ck π →
      ZKCP.prob ((Vf (κ (ZKCP.digestUnder f (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) ck)
          ck.2) x' (ϖ ck.2 π)).run f) {b | b = false} ≤
        ZKCP.prob (((readOne T h).V ck x π).run f) {b | b = false}) :
    ZKCP.Pr (ZKCP.completenessExp (frontArgK T h idx x₀ κ ϖ Vf) w x' ())
        (fun _ => {b | b = false}) ≤
      ZKCP.Pr (ZKCP.completenessExp (readOne T h) (idx w) x ()) (fun _ => {b | b = false}) +
        ZKCP.Pr (honestTriple (readOne T h) (idx w) x ())
          fun f => {o | o.2.2 = true ∧ Bad f o.1 o.2.1} := by
  subst hi
  exact pr_frontK_le_add (readOne T h) (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2))
    (fun ck => ck.2) κ ϖ Vf (idx w) _ x' () Bad hV

end Read

section At
open VerifierAndGoals
variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)

/-- UndoOn implies UndoUpTo at γ = 0. -/
theorem undoUpTo_of_on {J : Type} (idx : J → (D.input Z c₀ m₀).Index)
    (Tr : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) {Form : Type}
    (parse : Parser D Z Form) (encF : TypedProof (D.F Z) (D.P Z) → Form)
    (hU : UndoOn D Z c₀ m₀ T h idx Tr parse encF) :
    UndoUpTo D Z c₀ m₀ T h idx Tr parse encF 0 := by
  intro w x' x hb ht
  refine le_of_eq ?_
  unfold ZKCP.Pr
  rw [MeasureTheory.lintegral_eq_zero_of_ae_eq_zero]
  refine Filter.Eventually.of_forall fun f => ?_
  show ZKCP.prob ((((readOne T h).C (idx w)).bind fun keys =>
      ((readOne T h).P keys.2 x ()).bind fun π =>
        ((readOne T h).V keys.1 x π).mapO fun b => (keys.1, π, b)).run f) _ = 0
  rw [ZKCP.run_bind, ZKCP.prob_bind]
  refine le_antisymm (le_trans (ZKCP.expect_le_on_support _ (G := fun _ => 0) fun keys hk => ?_)
    (le_of_eq (ZKCP.expect_zero _))) (zero_le _)
  rw [ZKCP.run_bind, ZKCP.prob_bind]
  refine le_trans (ZKCP.expect_le_on_support _ (G := fun _ => 0) fun π hπ => ?_)
    (le_of_eq (ZKCP.expect_zero _))
  rw [ZKCP.OComp.run_mapO, ZKCP.prob_map]
  refine le_of_eq ?_
  unfold ZKCP.prob
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  rintro b hbs ⟨hbt, hne⟩
  have hbt' : b = true := hbt
  subst hbt'
  exact hne (hU w f keys hk x' x hb ht π hπ hbs)

end At

/-- Under the premises of Spec.frontCompleteUpTo, the shell frontId, whose only published key is the
commitment ID, is complete with the error α + γ. Conditional, no member known, of a shell. -/
theorem frontIdCompleteUpTo (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : VerifierAndGoals.Parser D Z Form)
    (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) (pair : Digest → D.More → T.D)
    (PP PP' : Type)
    (R₁ : ZKCP.IndexedRelation (D.input Z c₀ m₀).Index (D.input Z c₀ m₀).Instance Unit PP)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (α γ : ℝ≥0∞) (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s)
    (once : NoRepeat T.Pub) (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (fits : ∀ c m commitment prompt output (proof : VerifierAndGoals.TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (reads : ∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (scope : VerifierAndGoals.InScope Z = true)
    (hparse : UndoUpTo D Z c₀ m₀ T h idx (fun i x => R₁.rel i x ()) parse encF γ)
    (hcode : ∀ ck, ∃ code, T.encT ck = some code)
    (hA : ∀ d, ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair R₁) (typedAt T h d) 1 α)
    (hrel : ∀ w x', Rel.rel w x' () →
      ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ R₁.rel (idx w) x ()) :
    ZKCP.HasCompletenessError Rel (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) (α + γ) := by
  intro w x' u hr
  cases u
  obtain ⟨x, hb, hx⟩ := hrel w x' hr
  have hi : instOf (D.input Z c₀ m₀) x₀ x' = x := by
    unfold instOf
    rw [hb]
    rfl
  exact le_trans
    (pr_frontArgK_le_add T h idx x₀ _ _ _ w x' x hi
      (fun f ck π => (parse x'.1 x'.2 (encF ([], (lowKey ck.2, lowPrf ck.2 π)))).evaluate f ≠
        ([], (lowKey ck.2, lowPrf ck.2 π)))
      fun f ck π _ hn =>
        front_rejects_le D Z c₀ m₀ T h pair fits reads noCoin scope parse encF hcode x' x hb f ck π
          fun _ => not_not.1 hn)
    (add_le_add (complete_readOne T h R₁ α noCoin asks once spare hA (idx w) x () hx)
      (hparse w x' x hb hx))

/-- Proof of Spec.frontCompleteUpTo. Under its premises the shell frontAt is complete with the error
α + γ. Conditional, no member known, of a shell. -/
theorem frontCompleteUpTo : Spec.frontCompleteUpTo := by
  intro D Z c₀ m₀ T h s idx x₀ Form parse encF pair PP PP' R₁ Rel α γ noCoin asks once spare fits
    reads scope hparse hcode hA hrel w x' u hr
  cases u
  obtain ⟨x, hb, hx⟩ := hrel w x' hr
  have hi : instOf (D.input Z c₀ m₀) x₀ x' = x := by
    unfold instOf
    rw [hb]
    rfl
  have e : ZKCP.Pr (ZKCP.completenessExp (frontAt D Z c₀ m₀ T h s idx x₀ Form parse encF) w x' ())
        (fun _ => {b | b = false}) =
      ZKCP.Pr (ZKCP.completenessExp (frontArgK T h idx x₀ (fun dg k => (dg, k)) (fun _ π => π)
        fun k x' π => (VerifierAndGoals.verify D Z parse k.1 x'.1 x'.2
          (encF ([], (lowKey k.2, lowPrf k.2 π)))).toRandomized.toUpload) w x' ())
        fun _ => {b | b = false} := by
    refine ZKCP.Pr_congr (fun f => ?_) _
    show ((((readOne T h).C (idx w)).bind fun keys =>
        (ZKCP.keyDigest (fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2))
          keys.1).mapO fun dg => ((dg, keys.1.2), keys.2)).bind fun keys =>
          ((readOne T h).P keys.2 (instOf (D.input Z c₀ m₀) x₀ x') ()).bind fun π =>
            (VerifierAndGoals.verify D Z parse keys.1.1 x'.1 x'.2
              (encF ([], (lowKey keys.1.2, lowPrf keys.1.2 π)))).toRandomized.toUpload).run f =
      ((((readOne T h).C (idx w)).bind fun keys =>
        (ZKCP.keyDigest (fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2))
          keys.1).mapO fun dg => ((dg, keys.1.2), (keys.1.2, keys.2))).bind fun keys =>
          (((readOne T h).P keys.2.2 (instOf (D.input Z c₀ m₀) x₀ x') ()).mapO fun π => π).bind
            fun π => (VerifierAndGoals.verify D Z parse keys.1.1 x'.1 x'.2
              (encF ([], (lowKey keys.1.2, lowPrf keys.1.2 π)))).toRandomized.toUpload).run f
    rw [ZKCP.run_bind, run_C_front, ZKCP.run_bind, run_C_frontK, PMF.bind_map, PMF.bind_map]
    refine congrArg _ (funext fun keys => ?_)
    show (((readOne T h).P keys.2 (instOf (D.input Z c₀ m₀) x₀ x') ()).bind fun π =>
        (VerifierAndGoals.verify D Z parse
          (ZKCP.digestUnder f (fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2))
            keys.1) x'.1 x'.2
          (encF ([], (lowKey keys.1.2, lowPrf keys.1.2 π)))).toRandomized.toUpload).run f =
      ((((readOne T h).P keys.2 (instOf (D.input Z c₀ m₀) x₀ x') ()).mapO fun π => π).bind
        fun π => (VerifierAndGoals.verify D Z parse
          (ZKCP.digestUnder f (fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2))
            keys.1) x'.1 x'.2
          (encF ([], (lowKey keys.1.2, lowPrf keys.1.2 π)))).toRandomized.toUpload).run f
    rw [ZKCP.run_bind, ZKCP.run_bind, ZKCP.OComp.run_mapO, PMF.bind_map]
    rfl
  rw [e]
  exact le_trans
    (pr_frontArgK_le_add T h idx x₀ _ _ _ w x' x hi
      (fun f ck π => (parse x'.1 x'.2 (encF ([], (lowKey ck.2, lowPrf ck.2 π)))).evaluate f ≠
        ([], (lowKey ck.2, lowPrf ck.2 π)))
      fun f ck π _ hn =>
        front_rejects_le D Z c₀ m₀ T h pair fits reads noCoin scope parse encF hcode x' x hb f ck π
          fun _ => not_not.1 hn)
    (add_le_add (complete_readOne T h R₁ α noCoin asks once spare hA (idx w) x () hx)
      (hparse w x' x hb hx))

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.pr_frontK_le_add
#print axioms OnBytes.FrontRoad.undoUpTo_of_on
#print axioms OnBytes.FrontRoad.frontCompleteUpTo
#print axioms OnBytes.FrontRoad.frontIdCompleteUpTo

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CompleteK.lean: under the premises of Spec.frontComplete (Complete.lean), the
shell frontId (FrontId.lean), whose only published key is the commitment ID, is complete with the
same error α. Conditional, no member known, of a shell. Also bounds on the honest side's hash
queries for the scheme with any form of key and proof (frontArgK, FrontK.lean).
Terms and the limits that go with any quote: Spec.lean.

What this file proves.
  frontIdComplete   frontId is complete with the error α, under the premises of Spec.frontComplete.
  frontIdComplete_hon   The same from the premises of completeness at every d over one family of
      honest sides (HonAll, AlphaLe, HonAt.lean) and the other premises of Spec.frontComplete.
  pr_frontK_le   For any scheme over one hash function, any form κ of the key and ϖ of the proofs,
      and another verifier Vf: if under every hash function, at the keys and proofs that the honest
      side can produce there, Vf rejects no more often than the old verifier, the new completeness
      experiment fails no more often. pr_frontArgK_le: the same for frontArgK. The proof follows
      that of pr_front_le (Complete.lean).
  queryBound_frontKC, queryBound_frontKP   The committer and the prover of frontArgK make at most q₀
      + NC · Bk + 1 and NP · Bk hash queries: the bounds of Within.lean, under its premises,
      unchanged.

Limits. Those of Complete.lean and Within.lean. Among them: no member is known, and whether UndoOn
holds for the description's own form and parser is not proved. Nothing on hiding or binding is
proved here.

How it fits. Complete.lean is about frontAt, whose key is the ID with the whole key and whose proofs
are typed, and Within.lean about frontArg. In frontId the key is a commitment, a proof is a form,
and the verifier equals, as a function, that of the library's system; the prover's key differs from
that system's, and committer and prover are this folder's, not the description's own. Its prover's
proofs are the forms computed from the whole key and frontAt's proofs, and its verifier is given the
same form as frontAt's. So, under the premises of Spec.frontComplete, its experiment, like
frontAt's, fails no more often than the experiment after the public reading.
-/
import Johnson.FrontRoad.HonAt
import Johnson.FrontRoad.Within
import Johnson.FrontRoad.FrontId

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Front
variable {lam : ℕ} {I X X' W IVK K2 K' ISK Pf P' : Type}

theorem run_C_frontK (A : ZKCP.Arg lam I X W IVK ISK Pf) (code : IVK → Option ZKCP.Str)
    (g : IVK → K2) (κ : ZKCP.Digest lam → K2 → K') (f : ZKCP.Oracle lam) (i : I) :
    ((A.C i).bind fun keys =>
        (ZKCP.keyDigest code keys.1).mapO fun dg => (κ dg (g keys.1), (g keys.1, keys.2))).run f =
      ((A.C i).run f).map fun keys =>
        (κ (ZKCP.digestUnder f code keys.1) (g keys.1), (g keys.1, keys.2)) := by
  rw [ZKCP.run_bind]
  show _ = ((A.C i).run f).bind fun keys =>
    PMF.pure (κ (ZKCP.digestUnder f code keys.1) (g keys.1), (g keys.1, keys.2))
  refine congrArg _ (funext fun keys => ?_)
  rw [ZKCP.OComp.run_mapO, ZKCP.run_keyDigest, PMF.pure_map]

/-- pr_front_le (Complete.lean) with any form κ of the key and ϖ of the proofs. If under every hash
function, at the keys and proofs that committer and prover can produce there, Vf rejects no more
often than the old verifier (hV), the new completeness experiment fails no more often than the old
one. -/
theorem pr_frontK_le (A : ZKCP.Arg lam I X W IVK ISK Pf) (code : IVK → Option ZKCP.Str)
    (g : IVK → K2) (κ : ZKCP.Digest lam → K2 → K') (ϖ : K2 → Pf → P')
    (Vf : K' → X' → P' → ZKCP.OComp lam Bool) (i : I) (x : X) (x' : X') (w : W)
    (hV : ∀ f, ∀ keys ∈ ((A.C i).run f).support, ∀ π ∈ ((A.P keys.2 x w).run f).support,
      ZKCP.prob ((Vf (κ (ZKCP.digestUnder f code keys.1) (g keys.1)) x'
          (ϖ (g keys.1) π)).run f) {b | b = false} ≤
        ZKCP.prob ((A.V keys.1 x π).run f) {b | b = false}) :
    ZKCP.Pr (((A.C i).bind fun keys =>
        (ZKCP.keyDigest code keys.1).mapO fun dg =>
          (κ dg (g keys.1), (g keys.1, keys.2))).bind fun keys =>
          ((A.P keys.2.2 x w).mapO (ϖ keys.2.1)).bind fun π => Vf keys.1 x' π)
        (fun _ => {b | b = false}) ≤
      ZKCP.Pr (ZKCP.completenessExp A i x w) fun _ => {b | b = false} := by
  refine MeasureTheory.lintegral_mono fun f => ?_
  show ZKCP.prob ((((A.C i).bind fun keys =>
        (ZKCP.keyDigest code keys.1).mapO fun dg =>
          (κ dg (g keys.1), (g keys.1, keys.2))).bind fun keys =>
          ((A.P keys.2.2 x w).mapO (ϖ keys.2.1)).bind fun π => Vf keys.1 x' π).run f)
        {b | b = false} ≤
    ZKCP.prob (((A.C i).bind fun keys =>
      (A.P keys.2 x w).bind fun π => A.V keys.1 x π).run f) {b | b = false}
  rw [ZKCP.run_bind, run_C_frontK, ZKCP.prob_bind, ZKCP.expect_map, ZKCP.run_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_on_support _ fun keys hk => ?_
  show ZKCP.prob ((((A.P keys.2 x w).mapO (ϖ (g keys.1))).bind fun π =>
      Vf (κ (ZKCP.digestUnder f code keys.1) (g keys.1)) x' π).run f) {b | b = false} ≤ _
  rw [ZKCP.run_bind, ZKCP.OComp.run_mapO, ZKCP.prob_bind, ZKCP.expect_map, ZKCP.run_bind,
    ZKCP.prob_bind]
  exact ZKCP.expect_le_on_support _ fun π hπ => hV f keys hk π hπ

end Front

section Read
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {J K' P' : Type} (idx : J → R.Index) (x₀ : R.Instance)
  (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
  (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)

/-- The same for frontArgK against readOne, if instOf R x₀ x' = x (hi). -/
theorem pr_frontArgK_le (w : J) (x' : List Token × List Token) (x : R.Instance)
    (hi : instOf R x₀ x' = x)
    (hV : ∀ f, ∀ keys ∈ (((readOne T h).C (idx w)).run f).support,
      ∀ π ∈ (((readOne T h).P keys.2 x ()).run f).support,
      ZKCP.prob ((Vf (κ (ZKCP.digestUnder f (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1)
          keys.1.2) x' (ϖ keys.1.2 π)).run f) {b | b = false} ≤
        ZKCP.prob (((readOne T h).V keys.1 x π).run f) {b | b = false}) :
    ZKCP.Pr (ZKCP.completenessExp (frontArgK T h idx x₀ κ ϖ Vf) w x' ())
        (fun _ => {b | b = false}) ≤
      ZKCP.Pr (ZKCP.completenessExp (readOne T h) (idx w) x ()) fun _ => {b | b = false} := by
  subst hi
  exact pr_frontK_le (readOne T h) (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2))
    (fun ck => ck.2) κ ϖ Vf (idx w) _ x' () hV

/-- If the public reading makes at most q₀ queries, the answer to a typed query has at most Bk hash
blocks at every d, and the committer at every d makes at most NC typed queries, the committer of
frontArgK makes at most q₀ + NC * Bk + 1 hash queries. -/
theorem queryBound_frontKC (q₀ Bk NC : ℕ) (hq : T.Pub.QueryBound q₀)
    (hB : ∀ d o, (T.m d).blocks o ≤ Bk)
    (hC : ∀ d i, (commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).QueryBound NC) (w : J) :
    ((frontArgK T h idx x₀ κ ϖ Vf).C w).QueryBound (q₀ + NC * Bk + 1) := by
  have hG : ((readTold T h).C (idx w)).QueryBound (q₀ + (NC * Bk + 0 + 0)) :=
    hq.bind fun d =>
      OComp.QueryBound.bind
        (OComp.QueryBound.bind
          (queryBound_overOne (T.m d) (hB d) _ NC (hC d (idx w))) fun _ => trivial)
        fun _ => trivial
  exact ZKCP.OComp.QueryBound.bind _ 1
    (fun keys => ZKCP.OComp.QueryBound.mapO _ _ 1 (ZKCP.queryBound_keyDigest _ _)) _ _
    (queryBound_oneOf_C (readTold T h) (idx w) hG)

/-- If the answer to a typed query has at most Bk hash blocks at every d, and the prover at every d
makes at most NP typed queries, the prover of frontArgK makes at most NP * Bk hash queries. -/
theorem queryBound_frontKP (Bk NP : ℕ) (hB : ∀ d o, (T.m d).blocks o ≤ Bk)
    (hP : ∀ d isk b, (proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk b).QueryBound NP)
    (isk : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))
    (x' : List Token × List Token) :
    ((frontArgK T h idx x₀ κ ϖ Vf).P isk x' ()).QueryBound (NP * Bk) := by
  have hG : ((readTold T h).P isk.2 [(instOf R x₀ x', ())]).QueryBound (NP * Bk) :=
    queryBound_overOne (T.m isk.2.1) (hB isk.2.1)
      (proveW R.queryLayout (T.cA isk.2.1) R.fixedSample (h isk.2.1) isk.2.2 [(instOf R x₀ x', ())]) NP
      (hP isk.2.1 isk.2.2 _)
  exact ZKCP.OComp.QueryBound.mapO _ _ _
    (queryBound_oneOf_P (readTold T h) isk.2 (instOf R x₀ x') () hG)

end Read

section At
open VerifierAndGoals

/-- Under the premises of Spec.frontComplete (Complete.lean), the shell frontId, whose only
published key is the commitment ID, is complete with the error α. Conditional, no member known, of a
shell. -/
theorem frontIdComplete (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : Parser D Z Form)
    (encF : TypedProof (D.F Z) (D.P Z) → Form) (pair : Digest → D.More → T.D) (PP PP' : Type)
    (R₁ : ZKCP.IndexedRelation (D.input Z c₀ m₀).Index (D.input Z c₀ m₀).Instance Unit PP)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP') (α : ℝ≥0∞)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (fits : ∀ c m commitment prompt output (proof : TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (reads : ∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (scope : InScope Z = true)
    (hparse : UndoOn D Z c₀ m₀ T h idx (fun i x => R₁.rel i x ()) parse encF)
    (hcode : ∀ ck, ∃ code, T.encT ck = some code)
    (hA : ∀ d, ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair R₁) (typedAt T h d) 1 α)
    (hrel : ∀ w x', Rel.rel w x' () →
      ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ R₁.rel (idx w) x ()) :
    ZKCP.HasCompletenessError Rel (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF) α := by
  intro w x' u hr
  cases u
  obtain ⟨x, hb, hx⟩ := hrel w x' hr
  have hi : instOf (D.input Z c₀ m₀) x₀ x' = x := by
    unfold instOf
    rw [hb]
    rfl
  exact le_trans
    (pr_frontArgK_le T h idx x₀ _ _ _ w x' x hi fun f keys hk π hπ =>
      front_rejects_le D Z c₀ m₀ T h pair fits reads noCoin scope parse encF hcode x' x hb f
        keys.1 π (hparse w f keys hk x' x hb hx π hπ))
    (complete_readOne T h R₁ α noCoin asks once spare hA (idx w) x () hx)

/-- The same if HonAll and AlphaLe (HonAt.lean) hold at every d of the type, and the other premises
of Spec.frontComplete hold at the honest sides F.side and the relation of Yes. Conditional, no
member known, of a shell. -/
theorem frontIdComplete_hon (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (F : SidesAt T) (G : FallsAt F)
    (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) (α : ℝ≥0∞)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : Parser D Z Form)
    (encF : TypedProof (D.F Z) (D.P Z) → Form) (pair : Digest → D.More → T.D) (PP' : Type)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (fits : ∀ c m commitment prompt output (proof : TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (reads : ∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (scope : InScope Z = true) (hparse : UndoOn D Z c₀ m₀ T F.side idx Yes parse encF)
    (hcode : ∀ ck, ∃ code, T.encT ck = some code)
    (hH : HonAll G Yes fun _ => True) (hα : AlphaLe G (fun _ => True) α)
    (hrel : ∀ w x', Rel.rel w x' () →
      ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ Yes (idx w) x) :
    ZKCP.HasCompletenessError Rel (frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF) α :=
  frontIdComplete D Z c₀ m₀ T F.side s idx x₀ Form parse encF pair Unit PP'
    (ZKCP.languageRelation Yes) Rel α noCoin asks once spare fits reads scope hparse hcode
    (fun d => complete_typedAt hH hα d trivial) hrel

end At

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.pr_frontK_le
#print axioms OnBytes.FrontRoad.queryBound_frontKC
#print axioms OnBytes.FrontRoad.queryBound_frontKP
#print axioms OnBytes.FrontRoad.frontIdComplete
#print axioms OnBytes.FrontRoad.frontIdComplete_hon

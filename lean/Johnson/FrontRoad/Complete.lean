-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Complete.lean: the shell frontAt is complete with the error α, if the scheme with
the whole key published is complete with the error α, over the typed oracles, at every value d of
the type T.D, whether or not the public reading can return it, and under the further premises listed
here. Conditional, no member known, of a shell.
Terms and the limits that go with any quote: Spec.lean.

What this file has, for arbitrary parameters.
  Spec.frontComplete, frontComplete   The statement and its proof: ZKCP.HasCompletenessError Rel
      (frontAt …) α. The premises: the public reading has no coins, queries public strings only,
      none twice, and at every d each public string codes a point of the spare oracle · fits: for
      all c and m, innerCompiledVerifier at D's input at (c, m) is innerCompiledVerifier at T's input at pair c m · reads:
      under every hash function, pair of VerifierAndGoals.verify's two readings is the value of T's public
      reading · the public files are in scope · UndoOn · every key with a told part has a code · at
      every d, typedAt T h d is complete for one request, with one error α for all d · whatever Rel
      holds of builds, with no further tokens, an instance of which the inner relation holds at the
      index idx w.
  UndoOn   The parser undoes the encoder on what the honest side can produce. Under each hash
      function, take a key that the committer can produce there, and a proof that the prover can
      produce for a request that builds a true instance. If the verifier after the public reading
      (readOne's) can accept this proof, the form that is computed from the whole key and the proof
      is parsed back to the typed proof. Nothing is required of other typed proofs. undoOn_of_all:
      UndoOn holds if the parser undoes the encoder at every typed proof.
  pr_front_le   For any scheme over one hash function: put the digest of a code of the key in front
      of a part of the key, and take another verifier Vf. If under every hash function, at the keys
      and proofs that the honest side can produce there, Vf rejects no more often than the old
      verifier, the new completeness experiment fails no more often. pr_frontArg_le: the same for
      frontArg (Front.lean).
  front_rejects_le   Under fits, reads, "no coins", "in scope" and "every key with a told part has a
      code", for a request that builds an instance, and where the parser returns the typed proof if
      readOne's verifier can accept: under every hash function VerifierAndGoals.verify rejects no more often
      than readOne's verifier. By verify_whole (Shell.lean).
  complete_readOne   Under the four premises on the public reading and completeness at every d,
      readOne T h is complete with the error α. By complete_pub (ZKCP/PublicRead/Complete.lean).

Limits.
  - Completeness at every d is a premise, required at every d of the type. No member is built. At
    relations R₁ and Rel that hold of nothing the premises on UndoOn, on completeness at every d (at
    α = 0) and on Rel hold of every honest side, and the conclusion says nothing. "No member known"
    means: none with a true instance and α below 1.
  - Completeness is ZKCP.HasCompletenessError (ZKCP/Defs.lean): one index and one
    request, both fixed before the hash function is sampled, and one run of the committer.
  - The encoder and the parser are variables: nothing is said about bytes. UndoOn is restricted for
    a reason. No encoder satisfies "the parser undoes the encoder at every typed proof" for a parser
    that reads a number from eight bytes, as the built description's own parser reads a copy's
    number (argued, not proved; Johnson/Goal/Tie/DescriptionOnBytes.lean, OnBytes/Maker/Carrier.lean).
    Whether UndoOn holds for that parser is not proved. The encoder here does not see the hash
    function, and that parser's decoder reads a digest, so (argued) whether it undoes the encoder
    may depend on the hash function. A weaker premise, up to a probability γ: CompleteUpTo.lean.
  - Nothing on hiding or binding is proved here.

How it fits. PremW, the premises of the theorem on index privacy (wholeKeyPrivacy), does not exclude
a sessions' prover (the prover of a request's proof) that always aborts. Said here without a
theorem: from any parameters that satisfy PremW one gets others with such a prover. These satisfy
PremW too, have ZKCP.Gen.PrivacyOn for every relation whose true instances are in PremW's Ryes, and
have no completeness error below 1 for any relation that holds of some index and instance, at one
request or more. Completeness of the same scheme for such a relation, with an error below 1,
excludes such a prover.
-/
import Johnson.FrontRoad.Spec
import Johnson.FrontRoad.Shell
import Johnson.Prover.All.End
import ZKCP.PublicRead.Complete
import Compile.DigestKeyArg

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The parser undoes the encoder on what the honest side can produce. Under every hash function f:
for every key that the committer can produce, every request x' that builds an instance x with Tr
(idx w) x, and every proof π that the prover can produce for x, if the verifier of readOne can
accept π, the form encF ([], (lowKey, lowPrf)) is parsed back to that typed proof. Nothing is
required of other typed proofs. -/
def UndoOn (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    {J : Type} (idx : J → (D.input Z c₀ m₀).Index)
    (Tr : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) {Form : Type}
    (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) : Prop :=
  ∀ (w : J) (f : ZKCP.Oracle 256), ∀ keys ∈ (((readOne T h).C (idx w)).run f).support,
    ∀ (x' : List Token × List Token) x, (D.input Z c₀ m₀).buildInstance x' [] = some x → Tr (idx w) x →
      ∀ π ∈ (((readOne T h).P keys.2 x ()).run f).support,
        true ∈ (((readOne T h).V keys.1 x π).run f).support →
          (parse x'.1 x'.2 (encF ([], (lowKey keys.1.2, lowPrf keys.1.2 π)))).evaluate f =
            ([], (lowKey keys.1.2, lowPrf keys.1.2 π))

/-- If the parser undoes the encoder at every typed proof, under every hash function, UndoOn holds.
-/
theorem undoOn_of_all (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    {J : Type} (idx : J → (D.input Z c₀ m₀).Index)
    (Tr : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) {Form : Type}
    (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form)
    (hall : ∀ (hash : Hash) p o tp, (parse p o (encF tp)).evaluate hash = tp) :
    UndoOn D Z c₀ m₀ T h idx Tr parse encF :=
  fun _ f _ _ x' _ _ _ _ _ _ => hall f x'.1 x'.2 _

/-- States that frontAt is complete with the error α (ZKCP.HasCompletenessError) under the eleven
premises that the head lists, among them completeness of typedAt T h d with the error α at every d.
Conditional, no member known, of a shell. Statement only; proved as frontComplete below. -/
def Spec.frontComplete : Prop :=
  ∀ (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : VerifierAndGoals.Parser D Z Form)
    (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) (pair : Digest → D.More → T.D)
    (PP PP' : Type)
    (R₁ : ZKCP.IndexedRelation (D.input Z c₀ m₀).Index (D.input Z c₀ m₀).Instance Unit PP)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP') (α : ℝ≥0∞),
    T.Pub.NoCoin → (T.Pub.AsksIn fun _ s => T.Pt s) → NoRepeat T.Pub →
    (∀ d s, T.Pt s → IsOther (T.m d) s) →
    (∀ c m commitment prompt output (proof : VerifierAndGoals.TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof) →
    (∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash) →
    VerifierAndGoals.InScope Z = true →
    UndoOn D Z c₀ m₀ T h idx (fun i x => R₁.rel i x ()) parse encF →
    (∀ ck, ∃ code, T.encT ck = some code) →
    (∀ d, ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair R₁) (typedAt T h d) 1 α) →
    (∀ w x', Rel.rel w x' () →
      ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ R₁.rel (idx w) x ()) →
    ZKCP.HasCompletenessError Rel (frontAt D Z c₀ m₀ T h s idx x₀ Form parse encF) α

/-! ## A map on the published key -/

section MapKey
variable {S : OSpec} {I X W PP IVK IVK' ISK Pf : Type}

theorem verifyAll_mapKey (A : ZKCP.Gen.Arg S I X W IVK ISK Pf) (f : IVK → IVK')
    (V' : IVK' → X → Pf → Rom.OComp S Bool) (hV : ∀ k x π, V' (f k) x π = A.V k x π) (k : IVK) :
    ∀ l : List (X × Pf),
      ZKCP.Gen.verifyAll (mapKeyArg A f V') (f k) l = ZKCP.Gen.verifyAll A k l
  | [] => rfl
  | (x, π) :: l => by
    show (V' (f k) x π).bind (fun c =>
        (ZKCP.Gen.verifyAll (mapKeyArg A f V') (f k) l).bind fun cs => .pure (c && cs)) =
      (A.V k x π).bind fun c => (ZKCP.Gen.verifyAll A k l).bind fun cs => .pure (c && cs)
    rw [hV, verifyAll_mapKey A f V' hV k l]

/-- If the new verifier at the mapped key is the old verifier at the key (hV), completeness with the
error α is kept by a map on the published key (mapKeyArg). -/
theorem completeness_mapKey (R : ZKCP.Gen.RelPair I X W PP) (A : ZKCP.Gen.Arg S I X W IVK ISK Pf)
    (B : ℕ) (α : ℝ≥0∞) (f : IVK → IVK') (V' : IVK' → X → Pf → Rom.OComp S Bool)
    (hV : ∀ k x π, V' (f k) x π = A.V k x π) (h : ZKCP.Gen.HasCompletenessError R A B α) :
    ZKCP.Gen.HasCompletenessError R (mapKeyArg A f V') B α := by
  intro i b hb
  have e : ZKCP.Gen.completenessExp (mapKeyArg A f V') i b = ZKCP.Gen.completenessExp A i b := by
    show ((A.C i).bind fun k => Rom.OComp.pure (f k.1, k.2)).bind (fun key =>
        (A.P key.2 b).bind fun πs =>
          ZKCP.Gen.verifyAll (mapKeyArg A f V') key.1 ((b.map Prod.fst).zip πs.val)) =
      (A.C i).bind fun key => (A.P key.2 b).bind fun πs =>
        ZKCP.Gen.verifyAll A key.1 ((b.map Prod.fst).zip πs.val)
    rw [Rom.OComp.bind_assoc]
    refine congrArg _ (funext fun key => ?_)
    show (A.P key.2 b).bind (fun πs =>
        ZKCP.Gen.verifyAll (mapKeyArg A f V') (f key.1) ((b.map Prod.fst).zip πs.val)) = _
    exact congrArg _ (funext fun πs => verifyAll_mapKey A f V' hV key.1 _)
  rw [e]
  exact h i b hb

end MapKey

/-! ## The digest in front, and another verifier -/

section Front
variable {lam : ℕ} {I X X' W IVK K2 ISK Pf : Type}

theorem run_C_front (A : ZKCP.Arg lam I X W IVK ISK Pf) (code : IVK → Option ZKCP.Str)
    (g : IVK → K2) (f : ZKCP.Oracle lam) (i : I) :
    ((A.C i).bind fun keys =>
        (ZKCP.keyDigest code keys.1).mapO fun dg => ((dg, g keys.1), keys.2)).run f =
      ((A.C i).run f).map fun keys => ((ZKCP.digestUnder f code keys.1, g keys.1), keys.2) := by
  rw [ZKCP.run_bind]
  show _ = ((A.C i).run f).bind fun keys =>
    PMF.pure ((ZKCP.digestUnder f code keys.1, g keys.1), keys.2)
  refine congrArg _ (funext fun keys => ?_)
  rw [ZKCP.OComp.run_mapO, ZKCP.run_keyDigest, PMF.pure_map]

/-- Put the digest of a code of the key in front of a part g of the key, and take another verifier
Vf. If under every hash function, at the keys and proofs that committer and prover can produce
there, Vf rejects no more often than the old verifier (hV), the new completeness experiment fails no
more often than the old one. -/
theorem pr_front_le (A : ZKCP.Arg lam I X W IVK ISK Pf) (code : IVK → Option ZKCP.Str)
    (g : IVK → K2) (Vf : ZKCP.Digest lam × K2 → X' → Pf → ZKCP.OComp lam Bool) (i : I) (x : X)
    (x' : X') (w : W)
    (hV : ∀ f, ∀ keys ∈ ((A.C i).run f).support, ∀ π ∈ ((A.P keys.2 x w).run f).support,
      ZKCP.prob ((Vf (ZKCP.digestUnder f code keys.1, g keys.1) x' π).run f) {b | b = false} ≤
        ZKCP.prob ((A.V keys.1 x π).run f) {b | b = false}) :
    ZKCP.Pr (((A.C i).bind fun keys =>
        (ZKCP.keyDigest code keys.1).mapO fun dg => ((dg, g keys.1), keys.2)).bind fun keys =>
          (A.P keys.2 x w).bind fun π => Vf keys.1 x' π) (fun _ => {b | b = false}) ≤
      ZKCP.Pr (ZKCP.completenessExp A i x w) fun _ => {b | b = false} := by
  refine MeasureTheory.lintegral_mono fun f => ?_
  show ZKCP.prob ((((A.C i).bind fun keys =>
        (ZKCP.keyDigest code keys.1).mapO fun dg => ((dg, g keys.1), keys.2)).bind fun keys =>
          (A.P keys.2 x w).bind fun π => Vf keys.1 x' π).run f) {b | b = false} ≤
    ZKCP.prob (((A.C i).bind fun keys =>
      (A.P keys.2 x w).bind fun π => A.V keys.1 x π).run f) {b | b = false}
  rw [ZKCP.run_bind, run_C_front, ZKCP.prob_bind, ZKCP.expect_map, ZKCP.run_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_on_support _ fun keys hk => ?_
  show ZKCP.prob (((A.P keys.2 x w).bind fun π =>
      Vf (ZKCP.digestUnder f code keys.1, g keys.1) x' π).run f) {b | b = false} ≤ _
  rw [ZKCP.run_bind, ZKCP.run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  exact ZKCP.expect_le_on_support _ fun π hπ => hV f keys hk π hπ

end Front

/-! ## After the public reading -/

section Read
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {PP : Type}

/-- Under the four premises on the public reading, if typedAt T h d is complete with the error α at
every d, so is readTold T h: the told part in front of the key, then the step over d (complete_pub).
-/
theorem complete_readTold (Rl : ZKCP.Gen.RelPair R.Index R.Instance Unit PP) (B : ℕ) (α : ℝ≥0∞)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.HasCompletenessError Rl (typedAt T h d) B α) :
    ZKCP.Gen.HasCompletenessError Rl (readTold T h) B α :=
  complete_pub 256 _ _ _ _ _ _ _ _ Rl (toldAt T h) B α T.Pt T.Pub noCoin asks once
    (fun d i => asks_mapKey_C _ _ _ _ i (wholeAt_C h spare d i))
    (fun d isk b => wholeAt_P h spare d isk b)
    (fun d ck x π => by
      show (if ck.1 = T.part d then (wholeAt T h d).V ck.2 x π else .pure false).AsksIn _
      split
      · exact wholeAt_V h spare d ck.2 x π
      · exact trivial)
    fun d => completeness_mapKey Rl (wholeAt T h d) B α _ _ (fun _ _ _ => if_pos rfl)
      (completeness_overOne (T.m d) Rl (typedAt T h d) B α (hA d))

/-- Under the same premises, at one request: readOne T h is complete with the error α in the form of
ZKCP/Defs.lean. -/
theorem complete_readOne (R₁ : ZKCP.IndexedRelation R.Index R.Instance Unit PP) (α : ℝ≥0∞)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair R₁) (typedAt T h d) 1 α) :
    ZKCP.HasCompletenessError R₁ (readOne T h) α :=
  ZKCP.SpecialAny.completeness_of_gen R₁ (ZKCP.SpecialAny.agrees_oneOf _) α
    (complete_readTold T h (ZKCP.Special.toPair R₁) 1 α noCoin asks once spare hA)

/-- If instOf R x₀ x' = x (hi) and, under every hash function, at the keys and proofs that the
honest side can produce there, Vf rejects no more often than the verifier of readOne (hV), the
completeness experiment of frontArg fails no more often than that of readOne. -/
theorem pr_frontArg_le {J : Type} (idx : J → R.Index) (x₀ : R.Instance)
    (Vf : KeyF R → List Token × List Token → RequestProof 256 R.protocol → ZKCP.OComp 256 Bool) (w : J)
    (x' : List Token × List Token) (x : R.Instance) (hi : instOf R x₀ x' = x)
    (hV : ∀ f, ∀ keys ∈ (((readOne T h).C (idx w)).run f).support,
      ∀ π ∈ (((readOne T h).P keys.2 x ()).run f).support,
      ZKCP.prob ((Vf (ZKCP.digestUnder f (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1,
          keys.1.2) x' π).run f) {b | b = false} ≤
        ZKCP.prob (((readOne T h).V keys.1 x π).run f) {b | b = false}) :
    ZKCP.Pr (ZKCP.completenessExp (frontArg T h idx x₀ Vf) w x' ()) (fun _ => {b | b = false}) ≤
      ZKCP.Pr (ZKCP.completenessExp (readOne T h) (idx w) x ()) fun _ => {b | b = false} := by
  subst hi
  exact pr_front_le (readOne T h) (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2))
    (fun ck => ck.2) Vf (idx w) _ x' () hV

end Read

/-! ## The definition of VerifierAndGoals.verify -/

section At
open VerifierAndGoals
variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)

/-- Under fits, reads, "the public reading has no coins", "the public files are in scope" and "every
key with a told part has a code": let x' build the instance x, and suppose that the parser returns
the typed proof if the verifier of readOne can accept (hparse). Then under the hash function f,
VerifierAndGoals.verify at the digest of the key's code rejects no more often than the verifier of readOne. -/
theorem front_rejects_le (pair : Digest → D.More → T.D)
    (fits : ∀ c m commitment prompt output (proof : TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (reads : ∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (noCoin : T.Pub.NoCoin) (scope : InScope Z = true) {Form : Type} (parse : Parser D Z Form)
    (encF : TypedProof (D.F Z) (D.P Z) → Form)
    (hcode : ∀ ck, ∃ code, T.encT ck = some code) (x' : List Token × List Token)
    (x : (D.input Z c₀ m₀).Instance) (hb : (D.input Z c₀ m₀).buildInstance x' [] = some x)
    (f : ZKCP.Oracle 256) (ck : KeyT (D.input Z c₀ m₀)) (π : RequestProof 256 (D.input Z c₀ m₀).protocol)
    (hparse : true ∈ (((readOne T h).V ck x π).run f).support →
      (parse x'.1 x'.2 (encF ([], (lowKey ck.2, lowPrf ck.2 π)))).evaluate f =
        ([], (lowKey ck.2, lowPrf ck.2 π))) :
    ZKCP.prob (((verify D Z parse
        (ZKCP.digestUnder f (fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2)) ck)
        x'.1 x'.2 (encF ([], (lowKey ck.2, lowPrf ck.2 π)))).toRandomized.toUpload).run f)
        {b | b = false} ≤
      ZKCP.prob (((readOne T h).V ck x π).run f) {b | b = false} := by
  rw [RandomizedAlgorithm.run_toUpload, DeterministicAlgorithm.run_toRandomized]
  refine ZKCP.prob_pure_le_of_support fun he c hc => ?_
  have hc0 := hc
  have e1 : ((readOne T h).V ck x π).run f =
      ((readTold T h).V ck x π).runEager fun _ => f := by
    have e0 := Rom.runEager_toRom f (Rom.ofRom ((readTold T h).V ck x π))
    rw [Rom.toRom_ofRom] at e0
    exact e0.symm
  rw [e1] at hc
  have e2 : ((readTold T h).V ck x π).runEager (fun _ => f) =
      ((toldAt T h (T.Pub.det fun _ => f)).V ck x π).runEager fun _ => f :=
    verify_at noCoin (toldAt T h) ck x π fun _ => f
  rw [e2] at hc
  have hc' : c ∈ ((if ck.1 = T.part (T.Pub.det fun _ => f) then
      (wholeAt T h (T.Pub.det fun _ => f)).V ck.2 x π else .pure false).runEager
        fun _ => f).support := hc
  by_cases hp : ck.1 = T.part (T.Pub.det fun _ => f)
  · rw [if_pos hp] at hc'
    have nc : ((wholeAt T h (T.Pub.det fun _ => f)).V ck.2 x π).NoCoin :=
      Rom.noCoin_overOne _ _ (noCoin_VRA _ _ _ _ _ _ _ _)
    rw [nc.runEager, PMF.support_pure, Set.mem_singleton_iff] at hc'
    show c = false
    by_contra hne
    have hct : c = true := by
      cases c
      · exact absurd rfl hne
      · rfl
    obtain ⟨code, hcd⟩ := hcode (ck.1, lowKey ck.2)
    have hy := (verify_whole D Z c₀ m₀ T pair fits reads h parse f
      (ZKCP.digestUnder f (fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2)) ck)
      x'.1 x'.2 (encF ([], (lowKey ck.2, lowPrf ck.2 π))) [] ck.2 π (hparse (hct ▸ hc0))).2
      ⟨scope, x, code, hb, by rw [← hp]; exact hcd,
        (ZKCP.digestUnder_of_some f
          (enc := fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2)) hcd).symm,
        by rw [← hc']; exact hct⟩
    have he' : (verify D Z parse _ x'.1 x'.2 _).evaluate f = false := he
    rw [hy] at he'
    cases he'
  · rw [if_neg hp] at hc'
    have hc2 : c ∈ (PMF.pure false : PMF Bool).support := hc'
    rw [PMF.support_pure] at hc2
    exact hc2

/-- Proof of Spec.frontComplete. Under its premises the shell frontAt is complete with the error α.
Conditional, no member known, of a shell. -/
theorem frontComplete : Spec.frontComplete := by
  intro D Z c₀ m₀ T h s idx x₀ Form parse encF pair PP PP' R₁ Rel α noCoin asks once spare fits
    reads scope hparse hcode hA hrel w x' u hr
  cases u
  obtain ⟨x, hb, hx⟩ := hrel w x' hr
  have hi : instOf (D.input Z c₀ m₀) x₀ x' = x := by
    unfold instOf
    rw [hb]
    rfl
  exact le_trans
    (pr_frontArg_le T h idx x₀ _ w x' x hi fun f keys hk π hπ =>
      front_rejects_le D Z c₀ m₀ T h pair fits reads noCoin scope parse encF hcode x' x hb f
        keys.1 π (hparse w f keys hk x' x hb hx π hπ))
    (complete_readOne T h R₁ α noCoin asks once spare hA (idx w) x () hx)

end At

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.completeness_mapKey
#print axioms OnBytes.FrontRoad.pr_front_le
#print axioms OnBytes.FrontRoad.complete_readOne
#print axioms OnBytes.FrontRoad.front_rejects_le
#print axioms OnBytes.FrontRoad.frontComplete

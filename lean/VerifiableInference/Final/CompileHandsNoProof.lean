-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/CompileHandsNoProof.lean: at a request that builds an instance which is not served, compile's prover hands out
one fixed form, under every oracle and at all coins.

1.  WHAT IS CLAIMED: Spec.compile_hands_no_proof, of any protocol whose online prover withholds at every message of a request that is not
    served, and whose writer sends every typed proof without a proof string to one form. Nothing else of the protocol.
2.  HOW: Ends Q c: every path of the program c ends in a value with Q. The committer's secret key names the index that it was given; the
    prover's run then stops at every message; so its proof has no string, and the writer gives the form.
3.  This ties the compiled prover to a reply of none at a refused request (reply, VerifiableInference/AtEveryRequest.lean). That verify
    rejects the form is Protocol.RejectsNoProof, a fact about the parser, which is not shown here.
-/
import VerifiableInference.Final.RefuseUnserved
import Johnson.FrontRoad.SlotShown

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.FrontRoad OnBytes.PublicAt VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## 1 Every path ends so -/

section Ends
variable {S : OSpec} {α β : Type}

/-- Every path of the program ends in a value with Q. -/
def Ends (Q : α → Prop) : Rom.OComp S α → Prop
  | .pure a => Q a
  | .query _ _ k => ∀ r, Ends Q (k r)
  | .sample _ k => ∀ r, Ends Q (k r)

theorem Ends.bind {Q' : α → Prop} {Q : β → Prop} {g : α → Rom.OComp S β} (hg : ∀ a, Q' a → Ends Q (g a)) :
    ∀ c : Rom.OComp S α, Ends Q' c → Ends Q (c.bind g)
  | .pure a, h => hg a h
  | .query _ _ k, h => fun r => Ends.bind hg (k r) (h r)
  | .sample _ k, h => fun r => Ends.bind hg (k r) (h r)

theorem ends_true : ∀ c : Rom.OComp S α, Ends (fun _ => True) c
  | .pure _ => trivial
  | .query _ _ k => fun r => ends_true (k r)
  | .sample _ k => fun r => ends_true (k r)

theorem Ends.overOne {lam : ℕ} {Q : α → Prop} (m : OracleCoding S lam) :
    ∀ c : Rom.OComp S α, Ends Q c → Ends Q (c.overOne m)
  | .pure _, h => h
  | .sample _ k, h => fun r => Ends.overOne m (k r) (h r)
  | .query _ _ k, h =>
    Ends.bind (Q' := fun _ => True) (fun _ _ => Ends.overOne m _ (h _)) _ (ends_true _)

theorem Ends.overOneF {lam : ℕ} {Q : α → Prop} (m : OracleCoding S lam) (more : More S lam) :
    ∀ c : Rom.OComp S α, Ends Q c → Ends Q (c.overOneF m more)
  | .pure _, h => h
  | .sample _ k, h => fun r => Ends.overOneF m more (k r) (h r)
  | .query _ _ k, h =>
    Ends.bind (Q' := fun _ => True) (fun _ _ => Ends.overOneF m more _ (h _)) _ (ends_true _)

end Ends

section EndsZ
variable {lam : ℕ} {α β : Type}

/-- The same, over one hash function. -/
def EndsZ (Q : α → Prop) : ZKCP.OComp lam α → Prop
  | .pure a => Q a
  | .query _ k => ∀ r, EndsZ Q (k r)
  | .sample _ k => ∀ r, EndsZ Q (k r)

theorem EndsZ.bind {Q' : α → Prop} {Q : β → Prop} {g : α → ZKCP.OComp lam β} (hg : ∀ a, Q' a → EndsZ Q (g a)) :
    ∀ c : ZKCP.OComp lam α, EndsZ Q' c → EndsZ Q (c.bind g)
  | .pure a, h => hg a h
  | .query _ k, h => fun r => EndsZ.bind hg (k r) (h r)
  | .sample _ k, h => fun r => EndsZ.bind hg (k r) (h r)

theorem endsZ_true : ∀ c : ZKCP.OComp lam α, EndsZ (fun _ => True) c
  | .pure _ => trivial
  | .query _ k => fun r => endsZ_true (k r)
  | .sample _ k => fun r => endsZ_true (k r)

theorem EndsZ.withCoins {Q : α → Prop} : ∀ (c : ZKCP.OComp lam α) (n : ℕ), EndsZ Q c → EndsZ Q (c.withCoins n)
  | .pure _, _, h => h
  | .query _ k, n, h => fun r => EndsZ.withCoins (k r) n (h r)
  | .sample _ k, n, h => EndsZ.withCoins (k _) _ (h _)

theorem EndsZ.ofRom {Q : α → Prop} : ∀ c : Rom.OComp (rom lam) α, Ends Q c → EndsZ Q (Rom.ofRom c)
  | .pure _, h => h
  | .query _ _ k, h => fun r => EndsZ.ofRom (k r) (h r)
  | .sample _ k, h => fun r => EndsZ.ofRom (k r) (h r)

end EndsZ

/-- What an algorithm of the library's type can return under a hash function ends so. -/
theorem support_ofUpload {α : Type} {Q : α → Prop} : ∀ c : ZKCP.OComp 256 α, EndsZ Q c →
    ∀ (hash : VerifiableInference.Hash) (a : α), a ∈ ((VerifiableInference.RandomizedAlgorithm.ofUpload c).run hash).support → Q a
  | .pure r, h, _, a, ha => by
    have e : a = r := (PMF.mem_support_pure_iff _ _).1 ha
    exact e ▸ h
  | .query i k, h, hash, a, ha => support_ofUpload (k (hash i)) (h _) hash a ha
  | .sample n k, h, hash, a, ha => by
    obtain ⟨d, -, hd⟩ := (PMF.mem_support_bind_iff _ _ _).1 ha
    exact support_ofUpload (k d) (h d) hash a hd

theorem prob_ofUpload_zero {α : Type} {Q : α → Prop} (c : ZKCP.OComp 256 α) (h : EndsZ Q c) :
    VerifiableInference.Prob (VerifiableInference.RandomizedAlgorithm.ofUpload c) {a | ¬ Q a} = 0 := by
  have z : ∀ hash, VerifiableInference.eventProbability
      ((VerifiableInference.RandomizedAlgorithm.ofUpload c).run hash) {a | ¬ Q a} = 0 := fun hash =>
    (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2
      (Set.disjoint_left.2 fun a ha hn => hn (support_ofUpload c h hash a ha))
  unfold VerifiableInference.Prob
  simp only [z]
  exact MeasureTheory.lintegral_zero

/-! ## 2 The committer and the prover over typed oracles -/

section Typed
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
  (h : HonestSide lam L Bd aT aL)

/-- The committer's secret key names the index that it was given. -/
theorem ends_commitW (i : I) : Ends (fun k => k.2.i = i) (commitW W S cA h i) := by
  refine Ends.bind (Q' := fun _ => True) (fun d _ => ?_) _ (ends_true _)
  refine Ends.bind (Q' := fun _ => True) (fun t₁ _ => ?_) _ (ends_true _)
  refine Ends.bind (Q' := fun _ => True) (fun ts _ => ?_) _ (ends_true _)
  refine Ends.bind (Q' := fun _ => True) (fun a _ => ?_) _ (ends_true _)
  refine Ends.bind (Q' := fun _ => True) (fun ls _ => ?_) _ (ends_true _)
  exact rfl

/-- Where the test for a stop says yes at every message the prover's proof has no string. -/
theorem ends_proveAt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB)
    (hst : ∀ r e n ρ, h.st.stopB isk.i r e x n ρ = true) :
    Ends (fun π => π.piB = none) (proveAt W cA r₀ h isk x d) := by
  unfold proveAt
  split
  · exact rfl
  · rename_i t _
    refine Ends.bind (Q' := fun _ => True) (fun c _ => ?_) _ (ends_true _)
    exact shown_of_stops (fun ρ => hst t.r t.seed (h.nm d.j) ρ) c

theorem ends_proveW (isk : Isk lam L Bd aT aL) (x : X) (hst : ∀ r e n ρ, h.st.stopB isk.i r e x n ρ = true) :
    Ends (fun πs => (ZKCP.Special.head1 πs).piB = none) (proveW W cA r₀ h isk [(x, ())]) := by
  show Ends _ ((coinsP W h).bind fun d => (proveAt W cA r₀ h isk x d).bind fun π =>
    (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof lam L) [(x, ())])))
  refine Ends.bind (Q' := fun _ => True) (fun d _ => ?_) _ (ends_true _)
  refine Ends.bind (Q' := fun π : RequestProof lam L => π.piB = none) (fun π hπ => ?_) _
    (ends_proveAt W cA r₀ h isk x d hst)
  exact hπ

end Typed

/-! ## 3 Over one hash function -/

section Front
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)

theorem readOne_C_ends (i : R.Index) : EndsZ (fun keys => keys.2.2.i = i) ((readOne T h).C i) := by
  refine EndsZ.ofRom _ ?_
  show Ends _ (T.Pub.bind fun d => ((toldAt T h d).C i).bind fun k => Rom.OComp.pure (k.1, (d, k.2)))
  refine Ends.bind (Q' := fun _ => True) (fun d _ => ?_) _ (ends_true _)
  show Ends _ ((((commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).overOne (T.m d)).bind fun k =>
    Rom.OComp.pure ((T.part d, k.1), k.2)).bind fun k => Rom.OComp.pure (k.1, (d, k.2)))
  refine Ends.bind (Q' := fun k : KeyT R × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits => k.2.i = i)
    (fun k hk => ?_) _ ?_
  · exact hk
  · refine Ends.bind (Q' := fun k : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits => k.2.i = i)
      (fun k hk => ?_) _ (Ends.overOne _ _ (ends_commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i))
    exact hk

theorem readOne_P_ends (d : T.D) (isk : Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (x : R.Instance)
    (hst : ∀ r e n ρ, (h d).st.stopB isk.i r e x n ρ = true) :
    EndsZ (fun π => π.piB = none) ((readOne T h).P (d, isk) x ()) := by
  refine EndsZ.ofRom _ ?_
  show Ends _ (((proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk [(x, ())]).overOne (T.m d)).bind fun πs =>
    Rom.OComp.pure (ZKCP.Special.head1 πs))
  refine Ends.bind (Q' := fun πs => (ZKCP.Special.head1 πs).piB = none) (fun πs hπ => ?_) _
    (Ends.overOne _ _ (ends_proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk x hst))
  exact hπ

variable (more : (d : T.D) → More (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) 256)

theorem readOneF_C_ends (i : R.Index) :
    EndsZ (fun keys => keys.2.2.i = i) ((readOneF T h more).C i) := by
  refine EndsZ.ofRom _ ?_
  show Ends _ (T.Pub.bind fun d => ((toldAtF T h more d).C i).bind fun k =>
    Rom.OComp.pure (k.1, (d, k.2)))
  refine Ends.bind (Q' := fun _ => True) (fun d _ => ?_) _ (ends_true _)
  show Ends _ ((((commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).overOneF (T.m d) (more d)).bind fun k =>
    Rom.OComp.pure ((T.part d, k.1), k.2)).bind fun k => Rom.OComp.pure (k.1, (d, k.2)))
  refine Ends.bind (Q' := fun k : KeyT R × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits => k.2.i = i)
    (fun k hk => ?_) _ ?_
  · exact hk
  · refine Ends.bind (Q' := fun k : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits => k.2.i = i)
      (fun k hk => ?_) _ (Ends.overOneF _ _ _ (ends_commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i))
    exact hk

theorem readOneF_P_ends (d : T.D) (isk : Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (x : R.Instance)
    (hst : ∀ r e n ρ, (h d).st.stopB isk.i r e x n ρ = true) :
    EndsZ (fun π => π.piB = none) ((readOneF T h more).P (d, isk) x ()) := by
  refine EndsZ.ofRom _ ?_
  show Ends _ (((proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk [(x, ())]).overOneF (T.m d) (more d)).bind fun πs =>
    Rom.OComp.pure (ZKCP.Special.head1 πs))
  refine Ends.bind (Q' := fun πs => (ZKCP.Special.head1 πs).piB = none) (fun πs hπ => ?_) _
    (Ends.overOneF _ _ _ (ends_proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk x hst))
  exact hπ

end Front

section Slot
variable (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
  (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : VerifierAndGoals.Parser D Z Form)
  (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) (bound : ℕ)

/-- **The prover of the slot system hands the one form**, where the run stops at every message and the writer sends a proof without a
string to that form. -/
theorem slotProve_ends (noProof : Form)
    (hw : ∀ k (π : RequestProof 256 (D.input Z c₀ m₀).protocol), π.piB = none → encF ([], (lowKey k, lowPrf k π)) = noProof)
    (weights : ModelWeights s) (coins : Fin (bound + 1)) (request : List Token × List Token)
    (hst : ∀ d r e n ρ, (h d).st.stopB (idx weights) r e (instOf (D.input Z c₀ m₀) x₀ request) n ρ = true) :
    EndsZ (fun form => form = noProof)
      ((slotArg D Z c₀ m₀ T h s idx x₀ Form parse encF bound).P (weights, coins) request ()) := by
  show EndsZ _ ((((frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).C weights).withCoins coins.val).bind fun key =>
    (frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).P key.2 request ())
  refine EndsZ.bind (Q' := fun key : Commitment × (FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits ×
      (T.D × Isk 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) =>
      key.2.2.2.i = idx weights) (fun key hk => ?_) _ (EndsZ.withCoins _ _ ?_)
  · show EndsZ _ (((readOne T h).P key.2.2 (instOf _ x₀ request) ()).mapO
      fun π => encF ([], (lowKey key.2.1, lowPrf key.2.1 π)))
    refine EndsZ.bind (Q' := fun π : RequestProof 256 (D.input Z c₀ m₀).protocol => π.piB = none) (fun π hπ => ?_) _ ?_
    · exact hw _ π hπ
    · exact readOne_P_ends T h key.2.2.1 key.2.2.2 _ fun r e n ρ => by
        rw [hk]
        exact hst _ r e n ρ
  · show EndsZ _ (((readOne T h).C (idx weights)).bind fun keys =>
      (ZKCP.keyDigest (fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
        (dg, (keys.1.2, keys.2)))
    refine EndsZ.bind (Q' := fun keys : KeyT (D.input Z c₀ m₀) × (T.D × Isk 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody
        (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits) => keys.2.2.i = idx weights) (fun keys hk => ?_) _
      (readOne_C_ends T h _)
    refine EndsZ.bind (Q' := fun _ => True) (fun _ _ => ?_) _ (endsZ_true _)
    exact hk

variable (more : (d : T.D) → More (typedOracleFamily 256 (D.input Z c₀ m₀).queryLayout.K (typedOracleCarrier (D.input Z c₀ m₀).protocol
                           (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) 256)

/-- **The same at the third exit.** -/
theorem slotProveF_ends (noProof : Form)
    (hw : ∀ k (π : RequestProof 256 (D.input Z c₀ m₀).protocol), π.piB = none → encF ([], (lowKey k, lowPrf k π)) = noProof)
    (weights : ModelWeights s) (coins : Fin (bound + 1)) (request : List Token × List Token)
    (hst : ∀ d r e n ρ, (h d).st.stopB (idx weights) r e (instOf (D.input Z c₀ m₀) x₀ request) n ρ = true) :
    EndsZ (fun form => form = noProof)
      ((slotArgF D Z c₀ m₀ T h more s idx x₀ Form parse encF bound).P (weights, coins) request ()) := by
  show EndsZ _ ((((frontIdF D Z c₀ m₀ T h more s idx x₀ Form parse encF).C weights).withCoins
    coins.val).bind fun key => (frontIdF D Z c₀ m₀ T h more s idx x₀ Form parse encF).P key.2 request ())
  refine EndsZ.bind (Q' := fun key : Commitment × (FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits ×
      (T.D × Isk 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) =>
      key.2.2.2.i = idx weights) (fun key hk => ?_) _ (EndsZ.withCoins _ _ ?_)
  · show EndsZ _ (((readOneF T h more).P key.2.2 (instOf _ x₀ request) ()).mapO
      fun π => encF ([], (lowKey key.2.1, lowPrf key.2.1 π)))
    refine EndsZ.bind (Q' := fun π : RequestProof 256 (D.input Z c₀ m₀).protocol => π.piB = none) (fun π hπ => ?_) _ ?_
    · exact hw _ π hπ
    · exact readOneF_P_ends T h more key.2.2.1 key.2.2.2 _ fun r e n ρ => by
        rw [hk]
        exact hst _ r e n ρ
  · show EndsZ _ (((readOneF T h more).C (idx weights)).bind fun keys =>
      (ZKCP.keyDigest (fun ck : KeyT (D.input Z c₀ m₀) => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
        (dg, (keys.1.2, keys.2)))
    refine EndsZ.bind (Q' := fun keys : KeyT (D.input Z c₀ m₀) × (T.D × Isk 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody
        (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits) => keys.2.2.i = idx weights) (fun keys hk => ?_) _
      (readOneF_C_ends T h more _)
    refine EndsZ.bind (Q' := fun _ => True) (fun _ _ => ?_) _ (endsZ_true _)
    exact hk

end Slot

/-! ## 4 At compile, at a description -/

section AtADescription
open VerifierAndGoals VerifiableInference.OnPublicFiles

variable (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings)
  (idx : ModelWeights s → (D.C Z).I) (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (pair : Digest → D.More → T.D) (agree : ∀ c m, T.at (pair c m) = D.input Z c m) (x₀ : (D.C Z).X)
  (provers : HonestProvers ((D.F Z).withProvers (D.P Z)))
  (settings : (reading : T.D) →
    CompiledSettings ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers)
  (firstBlockTest : (reading : T.D) → Rom.More (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256
    (D.input Z c₀ m₀).queryLayout.K (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier (D.input Z c₀ m₀).protocol
                (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) 256)
  (coinBound : ℕ) (Form : Type) (parse : Parser D Z Form)
  (write : TypedProof ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL → Form)

set_option quotPrecheck false

local notation "𝕀" =>
  atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound Form parse write
local notation "ℍ" =>
  fun reading => AtRecs.side (honestSide
    ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers (settings reading))

/-- What compile's prover hands at a request, in the program's own form. The instance that it runs on
is instOf: at a request that builds none it is the fallback instance. -/
theorem compile_prove_ends (Served : (D.C Z).I → (D.C Z).X → Prop) (noProof : Form)
    (hR : provers.RefusesUnserved Served) (hW : (𝕀).WritesNoProof noProof)
    (weights : ModelWeights s) (randomness : (compile 𝕀).CommitmentRandomness)
    (request : List Token × List Token)
    (hS : ¬ Served (idx weights) (instOf (D.input Z c₀ m₀) x₀ request)) :
    EndsZ (fun form => form = noProof)
      ((slotArgF D Z c₀ m₀ T ℍ firstBlockTest s idx x₀ Form parse write coinBound).P
        (weights, randomness) request ()) :=
  slotProveF_ends D Z c₀ m₀ T ℍ s idx x₀ Form parse write coinBound firstBlockTest noProof
    (fun k π hπ => hW _ hπ) weights randomness request
    (fun d r e n ρ => stopB_unserved _ (settings d) hR hS r e n ρ)

/-- **In the form of HandsOutNoProof**: whatever compile's prover can return under any hash function,
at a request whose instance is not served, is the form noProof. At a request that builds no instance
the prover runs on the fallback instance, so this asks that the fallback instance is not served. -/
theorem compile_prove_run (Served : (D.C Z).I → (D.C Z).X → Prop) (noProof : Form)
    (hR : provers.RefusesUnserved Served) (hW : (𝕀).WritesNoProof noProof)
    (weights : ModelWeights s) (randomness : (compile 𝕀).CommitmentRandomness)
    (request : List Token × List Token)
    (hS : ¬ Served (idx weights) (instOf (D.input Z c₀ m₀) x₀ request))
    (hash : VerifiableInference.Hash) (form : Form)
    (hf : ((compile 𝕀).prove weights randomness request.1 request.2).run hash form ≠ 0) :
    form = noProof :=
  support_ofUpload _
    (compile_prove_ends D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound Form parse write
      Served noProof hR hW weights randomness request hS) hash form
    ((PMF.mem_support_iff _ _).2 hf)

/-- **At a request that builds an instance which is not served, compile's prover hands out the form
noProof.** Proved at every description; not at a public side that is no description. -/
theorem compile_hands_no_proof_holds : Spec.compile_hands_no_proof 𝕀 := by
  intro Served noProof hR hW weights randomness request x hb hS
  have hb' : (D.input Z c₀ m₀).buildInstance request [] = some x := hb
  have hx : instOf (D.input Z c₀ m₀) x₀ request = x := by
    unfold instOf
    rw [hb']
    rfl
  exact prob_ofUpload_zero _
    (compile_prove_ends D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound Form parse write
      Served noProof hR hW weights randomness request (by rw [hx]; exact hS))

end AtADescription

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.ends_commitW
#print axioms VerifiableInference.Compilation.ends_proveW
#print axioms VerifiableInference.Compilation.slotProve_ends
#print axioms VerifiableInference.Compilation.compile_prove_ends
#print axioms VerifiableInference.Compilation.compile_prove_run
#print axioms VerifiableInference.Compilation.compile_hands_no_proof_holds

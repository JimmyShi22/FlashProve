-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/FrontRoot.lean: the key is (root, record) alone, over the compiled verifier
with a record of this folder (`VC`, Cms.lean).

After lean/Johnson/RecCompile/FrontRoot.lean, in that file's words; its head tells why. The key is
`KeyRoot` = (root, record); Test's proof and the one link travel in the proof `OfflineLinkOnlineProof`, which here
also holds the number of the stored copy. `VR W S p k x π` is `VC` fed from the two.

Main names:
  `bindingRAt`: index binding for the languages, for every scheme whose verifier is `VR`, from
    `BcsAtC`, at the bound `epsC`.
  `cmsR_binding_lang`, `cmsR_binding_at`, `cmsR_binding_work`: as their likes without R
    (CmsGlue.lean, Pass.lean).
  `detBound_VR`: `VR` flips no coin and asks at most `tVC W` queries.
  `bindingR_one`: the same over one hash function.
  `soundForWith_rootSystem`: the front's soundness. This is said under the hypotheses that stand in
    the statement itself, which this comment does not list; it is no claim that they hold.

Limits: soundness alone. No committer, no prover, no completeness, nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.Front
import Johnson.TypedOracleCompiler.RecCompile.Pass

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ}

/-- The key: the root of the first encoded index, and its record. -/
structure KeyRoot (lam : ℕ) (L : HolographicProtocol I X) where
  cm : Dig lam
  rcd : L.Rec

/-- A proof: the test's proof on the first encoded index, one further encoded index (root, record,
link), the session's proof. -/
structure OfflineLinkOnlineProof (lam : ℕ) (L : HolographicProtocol I X) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape) where
  /-- the number of the stored copy -/
  copy : ℕ
  piT : Option (OneProtocolProof lam (batTC L aT))
  link : Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))
  piB : Option (OneProtocolProof lam L.onlineBatch)

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- Cms.lean's key, put together from the key and the proof. -/
def KeyRoot.full (k : KeyRoot lam L) (π : OfflineLinkOnlineProof lam L aT aL) : FullKey lam L aT aL :=
    ⟨k.cm, k.rcd, π.piT, [π.link]⟩

/-- Cms.lean's proof: the one link, the session's proof. -/
def OfflineLinkOnlineProof.low (π : OfflineLinkOnlineProof lam L aT aL) : RequestProof lam L := ⟨0, π.copy, π.piB⟩

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The verifier: Cms.lean's VC. -/
def VR (p : Params) (k : KeyRoot lam L) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  VC W S p (k.full π) x π.low

/-- The index extractor: extractorC0's text at the key (root, record). -/
def indexExtractorAtRootAndOutOfDomainSample :
    ZKCP.Gen.Extractor (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L)
        (OfflineLinkOnlineProof lam L aT aL) where
  Ei := fun k tr => L.decodeIndex (extEnc W tr k.cm) k.rcd
  Ew := fun _ _ _ _ _ => ()

theorem detBound_VR (p : Params) (k : KeyRoot lam L) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) :
    DetBound (VR W S p k x π) (tVC W) := detBound_VC W S p (k.full π) x π.low

def joinedR (p : Params) {St : Type} (Ct : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (KeyRoot lam L × St))
    (Pt : St → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (X × OfflineLinkOnlineProof lam L aT aL)) :
        TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  Ct.bind fun a => (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.ann a.1.cm).bind fun _ =>
    (Pt a.2).bind fun xp => (VR W S p a.1 xp.1 xp.2).bind fun _ => OComp.pure ()

theorem joinedR_queryBound (p : Params) {St : Type}
    {Ct : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (KeyRoot lam L × St)}
    {Pt : St → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (X × OfflineLinkOnlineProof lam L aT aL)} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (joinedR W S p Ct Pt).QueryBound (tC + tP + tVC W + 1) := by
  have h : (joinedR W S p Ct Pt).QueryBound (tC + (1 + (tP + (tVC W + 0)))) := by
    unfold joinedR
    exact hC.bind fun a =>
        (detBound_ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.ann a.1.cm).queryBound.bind fun
            _ =>
      (hP a.2).bind fun xp => (detBound_VR W S p a.1 xp.1 xp.2).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- Index binding for the languages from the event Bad, for every scheme whose verifier is VR: the
key is (root, record). -/
theorem bindingRAt {ISK : Type} (p : Params)
    (Ryes Rt : I → X → Prop) (εs : ℝ≥0∞) (hsub : ∀ i x, Ryes i x → Rt i x)
    (hB : BcsAtC W S Rt εs) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L) ISK
        (OfflineLinkOnlineProof lam L aT aL))
    (hA : A.V = VR W S p) :
    ZKCP.Gen.HasIndexBindingWith (relPair Ryes Rt hsub) A (indexExtractorAtRootAndOutOfDomainSample W) (epsC W εs) := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨Bad, hrare, -, hSd, -, hT, hL, hO, hE⟩ := hB
  have hpt : ∀ f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)),
      PrCoins f (ZKCP.Gen.bindingExp A (indexExtractorAtRootAndOutOfDomainSample W) Ct Pt)
          (ZKCP.Gen.bindingBad (relPair Ryes Rt hsub)) ≤
        PrCoins f (joinedR W S p Ct Pt).withTrace {o | Bad o.2} := by
    intro f
    unfold PrCoins
    simp only [ZKCP.Gen.bindingExp, bind_eq, pure_eq, joinedR, _root_.Compile.withTrace_bind,
        OComp.bind_assoc,
      OComp.ask, OComp.withTrace, OComp.bind, OComp.runEager_bind, OComp.runEager]
    refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
    have e1 : (A.V a.1.1 b.1.1 b.1.2).runEager f =
        ((VR W S p a.1.1 b.1.1 b.1.2).withTrace.runEager f).map Prod.fst := by
      rw [hA]
      exact (runEager_withTrace_fst f _).symm
    rw [e1, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
    rintro ⟨hacc, hbad⟩
    by_contra hnb
    have hrun : RunsIn c.2 (VC W S p (a.1.1.full b.1.2) b.1.1 b.1.2.low) true := by
      have := runsIn_of_mem_support (detBound_VR W S p a.1.1 b.1.1 b.1.2) f c hc
      have hc1 : c.1 = true := hacc
      rwa [hc1] at this
    have hnb' : ¬ Bad ((a.2 ++ [annE W a.1.1.cm (f OracleName.ann a.1.1.cm)]) ++ (b.2 ++ (c.2 ++ []))) := by
      simpa [annE] using hnb
    obtain ⟨i, hi, hr⟩ := coreC W S hW p hSd hT hL hO hE (a.1.1.full b.1.2) b.1.1 b.1.2.low a.2
      (b.2 ++ (c.2 ++ [])) c.2 _
      (fun e he => List.mem_append_right _ (List.mem_append_left _ he)) hrun hnb'
    have hi' : (indexExtractorAtRootAndOutOfDomainSample W).Ei a.1.1 a.2 = some i := hi
    simp only [hi'] at hbad
    rcases hbad with hb | hb
    · exact hb ⟨(), hr⟩
    · exact hb hr
  calc
    Rom.Pr (ZKCP.Gen.bindingExp A (indexExtractorAtRootAndOutOfDomainSample W) Ct Pt)
          (fun _ => ZKCP.Gen.bindingBad (relPair Ryes Rt hsub)) ≤
        Rom.Pr (joinedR W S p Ct Pt).withTrace (fun _ => {o | Bad o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (joinedR W S p Ct Pt).withTrace.law {o | Bad o.2} := Pr_eq_law _ _
    _ ≤ ((tC + tP + tVC W + 1 : ℕ) : ℝ≥0∞) * εs +
          2 * ((tC + tP + tVC W + 1 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
        hrare Unit (joinedR W S p Ct Pt) _ (joinedR_queryBound W S p hC hP)
    _ = epsC W εs tC tP := rfl

/-- Index binding for the languages, for every scheme whose verifier is VR, from SoundR (as
cms_binding_lang). -/
theorem cmsR_binding_lang {ISK : Type} (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w)
    (hS : L.SoundR Rno wit εs) (hSd : S.Law εs) (hlT : L.offline.IsLocal)
    (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal) (hcT : aT.Coherent) (hcL : aL.Coherent)
    (hco : L.onlineBatch.ann.Coherent) (hdT : W.depthReqT = 0) (hdL : W.depthReqL = 0) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L) ISK
        (OfflineLinkOnlineProof lam L aT aL))
    (hA : A.V = VR W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (indexExtractorAtRootAndOutOfDomainSample W) (epsC W εs) := by
  obtain ⟨eR, -, hrcd⟩ := hS.rcd
  obtain ⟨εT, hbT, hsT⟩ := hS.sndT
  obtain ⟨εL, hbL, hsL⟩ := hS.sndL
  obtain ⟨εB, hbB, hsB⟩ := hS.sndB
  exact bindingRAt W S p _ _ εs sub
    (cms_bcs I X Wn lam L Bd aT aL W S Rno wit eR εT εL εB εs ⟨hS.noneColl, hrcd, hsT, hsL, hsB⟩ hSd
      (by rw [hdT, pow_zero, timesShared_one]; exact hbT)
      (by rw [hdL, pow_zero, timesShared_one]; exact hbL)
      hbB hlT hlL hlB hcT hcL hco hW) hW A hA

/-- Index binding for the languages from explicit lists (as cms_binding_at). -/
theorem cmsR_binding_at {ISK : Type} (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (hSd : S.Law εs) (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hbB : Err.Below εB εs)
    (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hcT : aT.Coherent) (hcL : aL.Coherent) (hco : L.onlineBatch.ann.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L) ISK
        (OfflineLinkOnlineProof lam L aT aL))
    (hA : A.V = VR W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (indexExtractorAtRootAndOutOfDomainSample W) (epsC W εs) :=
  bindingRAt W S p _ _ εs sub
    (cms_bcs I X Wn lam L Bd aT aL W S Rno wit eR εT εL εB εs hS hSd hbT hbL hbB hlT hlL hlB hcT hcL
      hco hW) hW A hA

theorem extractorR0_local (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) : LocalTo (indexExtractorAtRootAndOutOfDomainSample W) m :=
  ⟨fun k tr => by
    show L.decodeIndex (extEnc W tr k.cm) k.rcd = L.decodeIndex (extEnc W (single m tr) k.cm) k.rcd
    rw [extEnc_single W m hl hn], fun _ _ _ _ _ => rfl⟩

/-- Index binding over one hash function, same bound. -/
theorem bindingR_one {ISK PP : Type}
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (R : ZKCP.Gen.RelPair I X Unit PP)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L) ISK
        (OfflineLinkOnlineProof lam L aT aL))
    (ε : ℕ → ℕ → ℝ≥0∞) (h : ZKCP.Gen.HasIndexBindingWith R A (indexExtractorAtRootAndOutOfDomainSample W) ε) :
    ZKCP.Gen.HasIndexBindingWith R (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W)) ε :=
  binding_overOne m R A (indexExtractorAtRootAndOutOfDomainSample W) (extractorR0_local W m hl hn) ε h

/-- Index binding at the passed object, work counted, the key being (root, record): the statement of
`cms_binding_work` (Pass.lean) with `VR`, `KeyRoot`, `OfflineLinkOnlineProof`, `indexExtractorAtRootAndOutOfDomainSample`. -/
theorem cmsR_binding_work {I X Wn : Type} {lam : ℕ} {ISK Bd : Type} (Nn : Type)
    [Inhabited Nn] (L : HolographicProtocol I X)
    (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape)
    (gT : GBits (L.pull σT σL σB).offline.shape) (gL : GBits (L.pull σT σL σB).link.shape)
    (gB : GBits (L.pull σT σL σB).onlineBatch.loc.shape)
    (aT : RoundSplits ((L.pull σT σL σB).grind Nn gT gL gB).offline.shape)
    (aL : RoundSplits ((L.pull σT σL σB).grind Nn gT gL gB).link.shape)
    (W : QueryLayout lam (typedOracleCarrier ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL)
    (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (fT : σT.Fib) (fL : σL.Fib) (fB : σB.Fib) (hSd : S.Law εs)
    (hbT : Err.BelowG gT (Err.pull σT εT) εs) (hbL : Err.BelowG gL (Err.pull σL εL) εs)
    (hbB : Err.BelowG gB (Err.pull σB εB) εs)
    (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hcT : aT.Coherent) (hcL : aL.Coherent) (hco : L.onlineBatch.ann.Coherent)
    (hdT : W.depthReqT = 0) (hdL : W.depthReqL = 0) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL)) I X
        Unit
      (KeyRoot lam ((L.pull σT σL σB).grind Nn gT gL gB)) ISK
      (OfflineLinkOnlineProof lam ((L.pull σT σL σB).grind Nn gT gL gB) aT aL))
    (hA : A.V = VR W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (indexExtractorAtRootAndOutOfDomainSample W) (epsC W εs) :=
  cmsR_binding_at W S p Ryes Rno _ eR _ _ _ εs sub
    (((hS.pull fT fL fB)).grind Nn gT gL gB) hSd
    (by rw [hdT, pow_zero, timesShared_one]; exact (Err.below_grind_iff gT _ εs).2 hbT)
    (by rw [hdL, pow_zero, timesShared_one]; exact (Err.below_grind_iff gL _ εs).2 hbL)
    ((Err.below_grind_iff gB _ εs).2 hbB) ((hlT.pull σT).grind gT) ((hlL.pull σL).grind gL)
    ((hlB.pull σB).grind gB) hcT hcL
    (BatchGrind.coherent_grind gB (BatchPull.coherent_pull σB hco)) hW A hA

end TypedOracleCompiler.Compile.Batch.Cms

namespace TypedOracleCompiler.VerifiableInference.Rec
open Rom ZKCP _root_.VerifiableInference _root_.VerifiableInference.Rec
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X ISK : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The front's soundness for the verifier with a record, the key being (root, record): the 256-bit
commitment is the digest of a code of `KeyRoot`. This is said under the hypotheses that stand in the
statement itself, which this comment does not list; it is no claim that they hold. -/
theorem soundForWith_rootSystem (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL))
    (Sd : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL) (p : Params)
    (m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)) 256) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1)
    (A : ZKCP.Gen.Arg (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot 256 L) ISK
        (OfflineLinkOnlineProof 256 L aT aL))
    (hA : A.V = VR W Sd p) (hK : Countable (KeyRoot 256 L)) (tag bound : ℕ)
    (build : List Token × List Token → List Token → Option X)
        (π₀ : KeyRoot 256 L × OfflineLinkOnlineProof 256 L aT aL)
    (nextToken : I → List Token → Option Token) {Yes IsTrue : I → X → Prop}
    (sub : ∀ i x, Yes i x → IsTrue i x) {ε : ℕ → ℕ → ℝ≥0∞} {ε' : ℕ → ℝ≥0∞}
    (bnd : ZKCP.Gen.HasIndexBindingWith (relPair Yes IsTrue sub) A (indexExtractorAtRootAndOutOfDomainSample W) ε)
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ε' (tC + tP)) :
    SoundForWith (systemOf (schemeOverOneHashFunction m A) hK tag bound build π₀ nextToken)
      (tokenExtractorOf (X := X) (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W)) hK tag).Ei claim ε' :=
  soundForWith_systemOf (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W)) hK tag bound π₀ nextToken
    (IsTrue := IsTrue)
    (bindingR_one W m hl hn (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) A ε
      (fun tC tP St Ct Pt hC hP => bnd tC tP St Ct Pt hC hP))
    (fun k x π => noCoin_overOne m _ (by
      rw [hA]
      exact noCoin_of_detBound _ _ (detBound_VR W Sd p k x π)))
    claim x₀ sound hε

end TypedOracleCompiler.VerifiableInference.Rec

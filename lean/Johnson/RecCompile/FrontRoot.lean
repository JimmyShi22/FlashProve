-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/FrontRoot.lean: the compiled verifier with a record, its key being the root of
the first encoded index and its record alone.

In Johnson/RecCompile/Front.lean the 256-bit commitment is the digest of a code of the whole key
`FullKey`: root, record, the test's proof, the links with their proofs. Here the key is
`KeyRoot` = (root, record); the test's proof and one link travel in the proof `PrfRoot`.
Definitions, statements and proofs.
Main names:
  `VR W S p k x π`: `VC W S p ⟨k.cm, k.rcd, π.piT, [π.link]⟩ x ⟨0, π.piB⟩`: the verifier of
    Johnson/RecCompile/Cms.lean itself, fed from the two records.
  `indexExtractorAtRootAndOutOfDomainSample`: the index decoder on what the committer's trace determines under the root, and
    the record: the text of `extractorC0`.
  `bindingRAt`: index binding for the languages, for every scheme whose verifier is `VR`, from the
    same `BcsAtC` and at the same bound `epsC` as `bindingCAt` (Johnson/RecCompile/CmsGlue.lean).
  `cmsR_binding_lang`, `cmsR_binding_at`, `cmsR_binding_work`: the statements of
    `cms_binding_lang` (Johnson/RecCompile/CmsGlue.lean), `cms_binding_at`, `cms_binding_work`
    (Johnson/RecCompile/Pass.lean) with
    `VR`, `KeyRoot`, `PrfRoot`, `indexExtractorAtRootAndOutOfDomainSample`.
  `bindingR_one`: the same over one hash function. `soundForWith_rootSystem`: the front's
    soundness, the key's code taken by choice.
How: `coreC` (Johnson/RecCompile/CmsGlue.lean) is general in the key: it reads the key's root and
record in its conclusion and asks nowhere that the key's proofs were fixed when the committer's
trace ended, because the analysis announces the root right behind the committer. It is applied as
it stands. The prover now chooses the test's proof and the link after the commitment.
Limits: under what `bindingCAt`, `cms_binding_lang`, `cms_binding_work` and
`soundForWith_recSystem` have. One link a proof. It does not say: completeness; anything on an
honest committer or prover; that a written code of `KeyRoot` is that of any program.

-/
import Johnson.RecCompile.Front
import Johnson.RecCompile.Pass

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ}

/-- The key: the root of the first encoded index, and its record. -/
structure KeyRoot (lam : ℕ) (L : HolographicProtocol I X) where
  cm : Dig lam
  rcd : L.Rec

/-- A proof: the test's proof on the first encoded index, one further encoded index (root, record,
link), the session's proof. -/
structure PrfRoot (lam : ℕ) (L : HolographicProtocol I X) where
  piT : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))
  link : Dig lam × L.Rec × Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))
  piB : Option (OneProtocolProof lam L.onlineBatch)

variable {L : HolographicProtocol I X}

/-- The key `FullKey`, put together from the key and the proof. -/
def KeyRoot.full (k : KeyRoot lam L) (π : PrfRoot lam L) : FullKey lam L :=
  ⟨k.cm, k.rcd, π.piT, [π.link]⟩

/-- The proof `RequestProof`: the one link, the session's proof. -/
def PrfRoot.low (π : PrfRoot lam L) : RequestProof lam L := ⟨0, π.piB⟩

variable (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L)

/-- The verifier: `VC`. -/
def VR (p : Params) (k : KeyRoot lam L) (x : X) (π : PrfRoot lam L) : TypedOracleComputation lam W.K L.carrierC Bool :=
  VC W S p (k.full π) x π.low

/-- The index extractor: extractorC0's text at the key (root, record). -/
def indexExtractorAtRootAndOutOfDomainSample :
    ZKCP.Gen.Extractor (spec lam W.K L.carrierC) I X Unit (KeyRoot lam L) (PrfRoot lam L) where
  Ei := fun k tr => L.decodeIndex (extEnc W tr k.cm) k.rcd
  Ew := fun _ _ _ _ _ => ()

theorem detBound_VR (p : Params) (k : KeyRoot lam L) (x : X) (π : PrfRoot lam L) :
    DetBound (VR W S p k x π) (tVC W) := detBound_VC W S p (k.full π) x π.low

def joinedR (p : Params) {St : Type} (Ct : TypedOracleComputation lam W.K L.carrierC (KeyRoot lam L × St))
    (Pt : St → TypedOracleComputation lam W.K L.carrierC (X × PrfRoot lam L)) : TypedOracleComputation lam W.K L.carrierC Unit :=
  Ct.bind fun a => (OComp.ask (S := spec lam W.K L.carrierC) OracleName.ann a.1.cm).bind fun _ =>
    (Pt a.2).bind fun xp => (VR W S p a.1 xp.1 xp.2).bind fun _ => OComp.pure ()

theorem joinedR_queryBound (p : Params) {St : Type}
    {Ct : TypedOracleComputation lam W.K L.carrierC (KeyRoot lam L × St)}
    {Pt : St → TypedOracleComputation lam W.K L.carrierC (X × PrfRoot lam L)} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (joinedR W S p Ct Pt).QueryBound (tC + tP + tVC W + 1) := by
  have h : (joinedR W S p Ct Pt).QueryBound (tC + (1 + (tP + (tVC W + 0)))) := by
    unfold joinedR
    exact hC.bind fun a =>
        (detBound_ask (S := spec lam W.K L.carrierC) OracleName.ann a.1.cm).queryBound.bind fun _ =>
      (hP a.2).bind fun xp => (detBound_VR W S p a.1 xp.1 xp.2).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- Index binding for the languages from the event Bad, for every scheme whose verifier is VR: the
key is (root, record). -/
theorem bindingRAt {ISK : Type} (p : Params)
    (Ryes Rt : I → X → Prop) (εs : ℝ≥0∞) (hsub : ∀ i x, Ryes i x → Rt i x)
    (hB : BcsAtC W S Rt εs) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (KeyRoot lam L) ISK (PrfRoot lam L))
    (hA : A.V = VR W S p) :
    ZKCP.Gen.HasIndexBindingWith (relPair Ryes Rt hsub) A (indexExtractorAtRootAndOutOfDomainSample W) (epsC W εs) := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨Bad, hrare, -, hSd, -, hT, hL, hO, hE⟩ := hB
  have hpt : ∀ f : Fam (spec lam W.K L.carrierC),
      PrCoins f (ZKCP.Gen.bindingExp A (indexExtractorAtRootAndOutOfDomainSample W) Ct Pt)
          (ZKCP.Gen.bindingBad (relPair Ryes Rt hsub)) ≤
        PrCoins f (joinedR W S p Ct Pt).withTrace {o | Bad o.2} := by
    intro f
    unfold PrCoins
    simp only [ZKCP.Gen.bindingExp, bind_eq, pure_eq, joinedR, withTrace_bind, OComp.bind_assoc,
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
`cms_binding_lang`). -/
theorem cmsR_binding_lang {ISK : Type} (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w)
    (hS : L.SoundR Rno wit εs) (hSd : S.Law εs) (hl : L.late = none) (hlT : L.offline.IsLocal)
    (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (KeyRoot lam L) ISK (PrfRoot lam L))
    (hA : A.V = VR W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (indexExtractorAtRootAndOutOfDomainSample W) (epsC W εs) := by
  obtain ⟨eR, -, hrcd⟩ := hS.rcd
  obtain ⟨εT, hbT, hsT⟩ := hS.sndT
  obtain ⟨εL, hbL, hsL⟩ := hS.sndL
  obtain ⟨εB, hbB, hsB⟩ := hS.sndB
  exact bindingRAt W S p _ _ εs sub
    (cms_bcs I X Wn lam L W S Rno wit eR εT εL εB εs ⟨hS.noneColl, hrcd, hsT, hsL, hsB⟩ hSd hbT hbL
      hbB hl hlT hlL hlB hco hW) hW A hA

/-- Index binding for the languages from explicit lists (as cms_binding_at). -/
theorem cmsR_binding_at {ISK : Type} (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (hSd : S.Law εs) (hbT : Err.Below εT εs) (hbL : Err.Below εL εs) (hbB : Err.Below εB εs)
    (hl : L.late = none) (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hco : L.onlineBatch.ann.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (KeyRoot lam L) ISK (PrfRoot lam L))
    (hA : A.V = VR W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (indexExtractorAtRootAndOutOfDomainSample W) (epsC W εs) :=
  bindingRAt W S p _ _ εs sub
    (cms_bcs I X Wn lam L W S Rno wit eR εT εL εB εs hS hSd hbT hbL hbB hl hlT hlL hlB hco hW)
    hW A hA

theorem extractorR0_local (m : OracleCoding (spec lam W.K L.carrierC) lam)
    (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) : LocalTo (indexExtractorAtRootAndOutOfDomainSample W) m :=
  ⟨fun k tr => by
    show L.decodeIndex (extEnc W tr k.cm) k.rcd = L.decodeIndex (extEnc W (single m tr) k.cm) k.rcd
    rw [extEnc_single W m hl hn], fun _ _ _ _ _ => rfl⟩

/-- Index binding over one hash function, same bound. -/
theorem bindingR_one {ISK PP : Type}
    (m : OracleCoding (spec lam W.K L.carrierC) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (R : ZKCP.Gen.RelPair I X Unit PP)
    (A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (KeyRoot lam L) ISK (PrfRoot lam L))
    (ε : ℕ → ℕ → ℝ≥0∞) (h : ZKCP.Gen.HasIndexBindingWith R A (indexExtractorAtRootAndOutOfDomainSample W) ε) :
    ZKCP.Gen.HasIndexBindingWith R (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W)) ε :=
  binding_overOne m R A (indexExtractorAtRootAndOutOfDomainSample W) (extractorR0_local W m hl hn) ε h

/-- Index binding at the passed object, work counted, the key being (root, record): the statement of
`cms_binding_work` with `VR`, `KeyRoot`, `PrfRoot`, `indexExtractorAtRootAndOutOfDomainSample`. -/
theorem cmsR_binding_work {I X Wn : Type} {lam : ℕ} {ISK : Type} (Nn : Type) [Inhabited Nn]
    (L : HolographicProtocol I X)
    (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape)
    (gT : GBits (L.pull σT σL σB).offline.shape) (gL : GBits (L.pull σT σL σB).link.shape)
    (gB : GBits (L.pull σT σL σB).onlineBatch.loc.shape)
    (W : QueryLayout lam ((L.pull σT σL σB).grind Nn gT gL gB).carrierC)
    (S : OutOfDomainSampleQueryLayout lam W.K ((L.pull σT σL σB).grind Nn gT gL gB))
    (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (fT : σT.Fib) (fL : σL.Fib) (fB : σB.Fib) (hSd : S.Law εs)
    (hbT : Err.BelowG gT (Err.pull σT εT) εs) (hbL : Err.BelowG gL (Err.pull σL εL) εs)
    (hbB : Err.BelowG gB (Err.pull σB εB) εs)
    (hl : L.late = none) (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hco : L.onlineBatch.ann.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (spec lam W.K ((L.pull σT σL σB).grind Nn gT gL gB).carrierC) I X Unit
      (KeyRoot lam ((L.pull σT σL σB).grind Nn gT gL gB)) ISK
      (PrfRoot lam ((L.pull σT σL σB).grind Nn gT gL gB)))
    (hA : A.V = VR W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (indexExtractorAtRootAndOutOfDomainSample W) (epsC W εs) :=
  cmsR_binding_at W S p Ryes Rno _ eR _ _ _ εs sub
    (((hS.pull fT fL fB)).grind Nn gT gL gB) hSd
    ((Err.below_grind_iff gT _ εs).2 hbT) ((Err.below_grind_iff gL _ εs).2 hbL)
    ((Err.below_grind_iff gB _ εs).2 hbB) hl ((hlT.pull σT).grind gT) ((hlL.pull σL).grind gL)
    ((hlB.pull σB).grind gB) (BatchGrind.coherent_grind gB (BatchPull.coherent_pull σB hco)) hW A hA

end Compile.Batch.Cms

namespace VerifiableInference.Rec
open Rom ZKCP Iop Compile Compile.Batch Compile.Batch.Cms
open scoped ENNReal

variable {I X ISK : Type} {L : HolographicProtocol I X}

/-- The front's soundness for the verifier with a record, the key being (root, record): the 256-bit
commitment is the digest of a code of `KeyRoot`. This is said under the hypotheses that stand in the
statement itself, which this comment does not list; it is no claim that they hold. -/
theorem soundForWith_rootSystem (W : QueryLayout 256 L.carrierC) (Sd : OutOfDomainSampleQueryLayout 256 W.K L) (p : Params)
    (m : OracleCoding (spec 256 W.K L.carrierC) 256) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1)
    (A : ZKCP.Gen.Arg (spec 256 W.K L.carrierC) I X Unit (KeyRoot 256 L) ISK (PrfRoot 256 L))
    (hA : A.V = VR W Sd p) (hK : Countable (KeyRoot 256 L)) (tag bound : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : KeyRoot 256 L × PrfRoot 256 L)
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

end VerifiableInference.Rec

#print axioms Compile.Batch.Cms.bindingRAt
#print axioms Compile.Batch.Cms.cmsR_binding_lang
#print axioms Compile.Batch.Cms.cmsR_binding_work
#print axioms VerifiableInference.Rec.soundForWith_rootSystem

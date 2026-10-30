-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/CmsGlue.lean: from BcsAtC to index binding for every scheme
whose verifier is VC (Cms.lean); then Spec.cms_binding_lang from cms_bcs (CmsBcs.lean). After
Compile/Batch/GlueBinding.lean.

-/
import Johnson.RecCompile.CmsBcs

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : HolographicProtocol I X}

theorem detBound_seedIs (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L) (t : Tag) (cm : Dig lam)
    (s : L.OutOfDomainSeed) : DetBound (seedIs W S t cm s) 1 := by
  unfold seedIs
  exact (detBound_ask (S := spec lam W.K L.carrierC) _ _).bind (t := 0) fun a => detBound_pure _ _

theorem runsIn_seedIs {W : QueryLayout lam L.carrierC} {S : OutOfDomainSampleQueryLayout lam W.K L} {tr : Tc W} {t : Tag}
    {cm : Dig lam} {s : L.OutOfDomainSeed} (h : RunsIn tr (seedIs W S t cm s) true) :
    ∃ a : FsAns lam W.K, fbE t (seedQ W S t cm) a ∈ tr ∧ S.seed a.1 = s := by
  unfold seedIs at h
  obtain ⟨a, ha, h2⟩ := (runsIn_bind_iff _ _ _).1 h
  refine ⟨a, runsIn_ask_iff.1 ha, ?_⟩
  have h3 := runsIn_pure_iff.1 h2
  simpa using h3

theorem detBound_VC (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L) (p : Params) (v : FullKey lam L)
    (x : X) (π : RequestProof lam L) : DetBound (VC W S p v x π) (tVC W) := by
  unfold VC tVC
  split
  · refine ((detBound_seedIs W S _ _ _).bind
      (t := 1 + (tVQB (wTC W) W.depthReq + (tVQB (wLC W) W.depthReq +
        (tVQB (wBC W) W.depthReq + 0)))) fun _ =>
      (detBound_seedIs W S _ _ _).bind
        (t := tVQB (wTC W) W.depthReq + (tVQB (wLC W) W.depthReq +
          (tVQB (wBC W) W.depthReq + 0))) fun _ =>
      (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind
        (t := tVQB (wLC W) W.depthReq + (tVQB (wBC W) W.depthReq + 0)) fun a =>
        (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind
          (t := tVQB (wBC W) W.depthReq + 0) fun b =>
          (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun c =>
            detBound_pure _ _).mono ?_
    omega
  · exact detBound_pure _ _

/-- The deterministic part, with records (after pathLemmaB, Compile/Batch/GlueBinding.lean). -/
theorem pathLemmaC {Rt : I → X → Prop} {x : X} {Y₀ Y₁ : Fin L.wordLength → L.Symbol} {r₀ r₁ : L.Rec}
    (hT : L.decodeIndex Y₀ r₀ ≠ none) (hL : L.decodeIndex Y₀ r₀ = none ∨ L.decodeIndex Y₁ r₁ = L.decodeIndex Y₀ r₀)
    (hO : L.decodeIndex Y₁ r₁ = none ∨ ∃ i, L.decodeIndex Y₁ r₁ = some i ∧ Rt i x) :
    ∃ i, L.decodeIndex Y₀ r₀ = some i ∧ Rt i x := by
  rcases hL with h | h
  · exact absurd h hT
  · rcases hO with h' | ⟨i, hi, hr⟩
    · exact absurd (h ▸ h') hT
    · exact ⟨i, h ▸ hi, hr⟩

theorem coreC (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L) (hW : OKC W S) (p : Params)
    {Rt : I → X → Prop} {Bad : Tc W → Prop}
    (hSd : ∀ tr t cm (a : FsAns lam W.K), ¬ Bad tr → fbE t (seedQ W S t cm) a ∈ tr →
      ¬ L.hasCollisionAt (extEnc W tr cm) (S.seed a.1))
    (hT : ∀ tr cm rec π, ¬ Bad tr → RunsIn tr (vTC' W cm rec π) true →
      L.hasCollisionAt (extEnc W tr cm) rec.1 ∨ L.decodeIndex (extEnc W tr cm) rec ≠ none)
    (hL : ∀ tr cm cm' rec rec' π, ¬ Bad tr → RunsIn tr (vLC' W cm cm' rec rec' π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec)
    (hO : ∀ tr cm x rec π, ¬ Bad tr → RunsIn tr (vBC' W S cm x rec π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) rec = some i ∧ Rt i x)
    (hE : ∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)
    (v : FullKey lam L) (x : X) (π : RequestProof lam L) (trC rest trV : Tc W) (u : Unit)
    (hsub : trV ⊆ rest) (hrun : RunsIn trV (VC W S p v x π) true)
    (hnb : ¬ Bad ((trC ++ [annE W v.cm u]) ++ rest)) :
    ∃ i, L.decodeIndex (extEnc W trC v.cm) v.rcd = some i ∧ Rt i x := by
  set tr : Tc W := (trC ++ [annE W v.cm u]) ++ rest with htr
  have hrun' : RunsIn tr (VC W S p v x π) true :=
    hrun.mono fun e he => List.mem_append_right _ (hsub he)
  have hann : Announced W (trC ++ [annE W v.cm u]) v.cm := by
    cases u
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hext : extEnc W trC v.cm = extEnc W tr v.cm := by
    rw [← extEnc_ann trC v.cm u v.cm]
    exact hE _ rest v.cm hnb hann
  rw [hext]
  unfold VC at hrun'
  split at hrun'
  · rename_i πT cmj recj πL πB _ _ _
    simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun'
    obtain ⟨s0, hs0, sj, hsj, a, ha, b, hb, c, hc, habc⟩ := hrun'
    simp only [Bool.and_eq_true] at habc
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := habc
    obtain ⟨a0, hm0, he0⟩ := runsIn_seedIs hs0
    obtain ⟨aj, hmj, hej⟩ := runsIn_seedIs hsj
    have hc0 : ¬ L.hasCollisionAt (extEnc W tr v.cm) v.rcd.1 := he0 ▸ hSd tr _ _ a0 hnb hm0
    have hcj : ¬ L.hasCollisionAt (extEnc W tr cmj) recj.1 := hej ▸ hSd tr _ _ aj hnb hmj
    obtain ⟨_, _, ha'⟩ := runsIn_verifyB_of_strict hW.T ha
    obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hW.Lk hb
    obtain ⟨_, _, hc'⟩ := runsIn_verifyB_of_strict hW.B hc
    exact pathLemmaC ((hT tr v.cm v.rcd _ hnb ha').resolve_left hc0)
      ((hL tr v.cm cmj v.rcd recj _ hnb hb').imp_right fun h => h.resolve_left hcj)
      (hO tr cmj x recj _ hnb hc')
  · exact absurd (runsIn_pure_iff.1 hrun') (by simp)

def joinedC (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L) (p : Params) {St : Type}
    (Ct : TypedOracleComputation lam W.K L.carrierC (FullKey lam L × St))
    (Pt : St → TypedOracleComputation lam W.K L.carrierC (X × RequestProof lam L)) :
    TypedOracleComputation lam W.K L.carrierC Unit :=
  Ct.bind fun a => (OComp.ask (S := spec lam W.K L.carrierC) OracleName.ann a.1.cm).bind fun _ =>
    (Pt a.2).bind fun xp => (VC W S p a.1 xp.1 xp.2).bind fun _ => OComp.pure ()

theorem joinedC_queryBound (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L) (p : Params) {St : Type}
    {Ct : TypedOracleComputation lam W.K L.carrierC (FullKey lam L × St)}
    {Pt : St → TypedOracleComputation lam W.K L.carrierC (X × RequestProof lam L)} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (joinedC W S p Ct Pt).QueryBound (tC + tP + tVC W + 1) := by
  have h : (joinedC W S p Ct Pt).QueryBound (tC + (1 + (tP + (tVC W + 0)))) := by
    unfold joinedC
    exact hC.bind fun a =>
        (detBound_ask (S := spec lam W.K L.carrierC) OracleName.ann a.1.cm).queryBound.bind fun _ =>
      (hP a.2).bind fun xp => (detBound_VC W S p a.1 xp.1 xp.2).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- Index binding for the languages from the event Bad, for every scheme whose verifier is VC. -/
theorem bindingCAt {ISK : Type} (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L) (p : Params)
    (Ryes Rt : I → X → Prop) (εs : ℝ≥0∞) (hsub : ∀ i x, Ryes i x → Rt i x)
    (hB : BcsAtC W S Rt εs) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (FullKey lam L) ISK (RequestProof lam L))
    (hA : A.V = VC W S p) :
    ZKCP.Gen.HasIndexBindingWith (relPair Ryes Rt hsub) A (extractorC0 W) (epsC W εs) := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨Bad, hrare, -, hSd, -, hT, hL, hO, hE⟩ := hB
  have hpt : ∀ f : Fam (spec lam W.K L.carrierC),
      PrCoins f (ZKCP.Gen.bindingExp A (extractorC0 W) Ct Pt)
          (ZKCP.Gen.bindingBad (relPair Ryes Rt hsub)) ≤
        PrCoins f (joinedC W S p Ct Pt).withTrace {o | Bad o.2} := by
    intro f
    unfold PrCoins
    simp only [ZKCP.Gen.bindingExp, bind_eq, pure_eq, joinedC, withTrace_bind, OComp.bind_assoc,
      OComp.ask, OComp.withTrace, OComp.bind, OComp.runEager_bind, OComp.runEager]
    refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
    have e1 : (A.V a.1.1 b.1.1 b.1.2).runEager f =
        ((VC W S p a.1.1 b.1.1 b.1.2).withTrace.runEager f).map Prod.fst := by
      rw [hA]
      exact (runEager_withTrace_fst f _).symm
    rw [e1, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
    rintro ⟨hacc, hbad⟩
    by_contra hnb
    have hrun : RunsIn c.2 (VC W S p a.1.1 b.1.1 b.1.2) true := by
      have := runsIn_of_mem_support (detBound_VC W S p a.1.1 b.1.1 b.1.2) f c hc
      have hc1 : c.1 = true := hacc
      rwa [hc1] at this
    have hnb' : ¬ Bad ((a.2 ++ [annE W a.1.1.cm (f OracleName.ann a.1.1.cm)]) ++ (b.2 ++ (c.2 ++ []))) := by
      simpa [annE] using hnb
    obtain ⟨i, hi, hr⟩ := coreC W S hW p hSd hT hL hO hE a.1.1 b.1.1 b.1.2 a.2
      (b.2 ++ (c.2 ++ [])) c.2 _
      (fun e he => List.mem_append_right _ (List.mem_append_left _ he)) hrun hnb'
    have hi' : (extractorC0 W).Ei a.1.1 a.2 = some i := hi
    simp only [hi'] at hbad
    rcases hbad with hb | hb
    · exact hb ⟨(), hr⟩
    · exact hb hr
  calc
    Rom.Pr (ZKCP.Gen.bindingExp A (extractorC0 W) Ct Pt)
          (fun _ => ZKCP.Gen.bindingBad (relPair Ryes Rt hsub)) ≤
        Rom.Pr (joinedC W S p Ct Pt).withTrace (fun _ => {o | Bad o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (joinedC W S p Ct Pt).withTrace.law {o | Bad o.2} := Pr_eq_law _ _
    _ ≤ ((tC + tP + tVC W + 1 : ℕ) : ℝ≥0∞) * εs +
          2 * ((tC + tP + tVC W + 1 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
        hrare Unit (joinedC W S p Ct Pt) _ (joinedC_queryBound W S p hC hP)
    _ = epsC W εs tC tP := rfl

theorem cms_binding_lang : Spec.cms_binding_lang := by
  intro I X Wn ISK lam L W S p Ryes Rno wit εs sub hS hSd hl hlT hlL hlB hco hW A hA
  obtain ⟨eR, -, hrcd⟩ := hS.rcd
  obtain ⟨εT, hbT, hsT⟩ := hS.sndT
  obtain ⟨εL, hbL, hsL⟩ := hS.sndL
  obtain ⟨εB, hbB, hsB⟩ := hS.sndB
  exact bindingCAt W S p _ _ εs sub
    (cms_bcs I X Wn lam L W S Rno wit eR εT εL εB εs ⟨hS.noneColl, hrcd, hsT, hsL, hsB⟩ hSd hbT hbL
      hbB hl hlT hlL hlB hco hW) hW A hA

/-- The same with witnesses and the recomputing extractor. -/
theorem cms_binding {ISK : Type} (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L) (p : Params)
    (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (re : I → X → Wn) (w0 : Wn)
    (εs : ℝ≥0∞) (sub : ∀ i x w, Ryes i x w → Rno i x w) (hS : L.SoundR Rno wit εs)
    (hSd : S.Law εs) (hl : L.late = none) (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hco : L.onlineBatch.ann.Coherent) (hW : OKC W S) (hre : ∀ i x w, Rno i x w → Rno i x (re i x))
    (A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (FullKey lam L) ISK (RequestProof lam L))
    (hA : A.V = VC W S p) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW Ryes Rno sub) (ZKCP.Gen.withW Wn A)
      (ZKCP.Gen.recompute (extractorC0 W) re w0) (epsC W εs) :=
  ZKCP.Gen.binding_by_recompute _ I X Wn Unit _ ISK _ (ZKCP.Gen.relPairW Ryes Rno sub)
    (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w)
      fun i x ⟨w, h⟩ => ⟨w, sub i x w h⟩) A (extractorC0 W) re w0 (epsC W εs)
    (fun _ _ h => h) hre
    (cms_binding_lang I X Wn ISK lam L W S p Ryes Rno wit εs _ hS hSd hl hlT hlL hlB hco hW A hA)

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.cms_bcs
#print axioms Compile.Batch.Cms.cms_binding_lang
#print axioms Compile.Batch.Cms.cms_binding

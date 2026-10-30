-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/CmsAnsPr.lean: index binding for every scheme whose verifier is the compiled
verifier with the answers alone in each chain's first query, FOR EVERY ALGORITHM.

CmsAns.lean proves its clauses on traces in which the seed queries of a first query's roots stand
before it. A cheating committer or prover need not ask in that order. As in LinkAnsPr.lean the order
is had in the analysis alone: the algorithm that is judged (committer; the root announced; prover;
verifier) is wrapped so that it asks, before each first query of a chain at any of the three tags,
the seed queries of that query's two first roots (`between`, OnBytes/Slice/WrapBetween.lean). Under
every fixed family of oracle functions the wrapped algorithm has the same output; its trace is the
old one with entries laid in; it asks at most five times as many queries. The index extractor reads
the committer's own trace: the word under a root does not see the entries laid in.

Two things that such an argument must mind: a seed query may be asked again later: the events are
caused by new entries alone; the wrapping is a map on algorithms that does not look at the oracle
functions.

Main names:
  `preAll`: what is asked before a query. `seedsFirstAll_of_asksFirst`, `extEnc_lenBA`.
  `VG`, `extractorG`: the verifier and the index extractor for a key and a proof of any types from
    which the key and the proof of `verifyAtFullKey` are put together, the root and the record being the key's.
  `soundnessBoundOverTypedOracles`: the bound: n εs + 2 (n + 1)² / 2^lam at n = 5 (tC + tP + tVC + 1).
  `bindingGAt`: index binding from `BcsAtA`. `cmsA_binding_at`: from `SoundAtR`.
The two instances, at the whole key and at the key (root, record): FrontRootAns.lean.
Limits: soundness alone; typed oracles; one clause, index binding.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAns
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPr
import Johnson.TypedOracleCompiler.RecCompile.FrontRoot

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

variable {I X Wn : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-! ## What is asked before a query -/

/-- before a first query of a chain: the seed queries of the two first entries of its list -/
def preAt {t : Tag} (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  if q.round = 0 then
    match q.head with
    | .f1 cms _ _ => askSeeds W S (cms.take 2)
    | _ => OComp.pure ()
  else OComp.pure ()

/-- what is asked before a query: nothing, but before a first query of a chain -/
def preAll : (o : OracleName) → domOf lam (typedOracleCarrier L Bd aT aL) o → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit
  | OracleName.fb _, q => preAt W S q
  | _, _ => OComp.pure ()

/-- `preAll`, typed as a wrapping of algorithms over the typed oracles wants it -/
abbrev preA : (o : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).ι) →
    (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o → OComp (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) Unit :=
  preAll W S

theorem detBound_preAt {t : Tag} (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) :
    DetBound (preAt W S q) 4 := by
  unfold preAt
  split
  · split
    · rename_i cms _ _ _
      exact (detBound_askSeeds W S _).mono (by
        have := List.length_take_le 2 cms
        omega)
    · exact detBound_pure _ _
  · exact detBound_pure _ _

theorem detBound_preAll (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    DetBound (preAll W S o q) 4 := by
  cases o with
  | fb t => exact detBound_preAt W S q
  | _ => exact detBound_pure _ _

variable (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- nothing is asked before a query in a round other than 0 -/
theorem preAll_round {t : Tag} (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) (h : q.round ≠ 0) :
    preAll W S (OracleName.fb t) q = OComp.pure () := by
  show preAt W S q = _
  unfold preAt
  rw [if_neg h]

/-- every entry of the log of what is asked before a query is a query to the seeds' oracle in a
round other than 0 -/
theorem round_preAll (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ∀ x ∈ ((preAll W S o q).withTrace.det g).2,
      ∃ (q' : FbIn lam (typedOracleCarrier L Bd aT aL) S.t) (a : FsAns lam W.K),
        x = fbE S.t q' a ∧ q'.round ≠ 0 := by
  intro x hx
  cases o with
  | fb t =>
    have hx' : x ∈ ((preAt W S q).withTrace.det g).2 := hx
    unfold preAt at hx'
    split at hx'
    · split at hx'
      · exact round_log W S g _ x hx'
      · exact absurd hx' List.not_mem_nil
    · exact absurd hx' List.not_mem_nil
  | _ => exact absurd hx List.not_mem_nil

/-- What is asked before a query asks nothing for its own queries. -/
theorem idle_preAll (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ∀ x ∈ ((preAll W S o q).withTrace.det g).2,
      ((preAll W S x.1 x.2.1).withTrace.det g).2 = [] := by
  intro x hx
  obtain ⟨q', a, rfl, hr⟩ := round_preAll W S g o q x hx
  show ((preAll W S (OracleName.fb S.t) q').withTrace.det g).2 = []
  rw [preAll_round W S q' hr]
  rfl

/-- A TRACE THAT ASKS FIRST HAS THE ORDER, at all three tags. -/
theorem seedsFirstAll_of_asksFirst (σ : Tc W) (h : AsksFirst (preA W S) g σ) :
    SeedsFirstAll W S σ := by
  intro t pre q a post cms x salt htr hr hq c hc
  have hb := asksFirst_before (preA W S) g σ h (idle_preAll W S g) pre (fbE t q a) post htr
  have e : preAll W S (OracleName.fb t) q = askSeeds W S (cms.take 2) := by
    show preAt W S q = _
    unfold preAt
    rw [if_pos hr, hq]
  have hb' : ∀ x ∈ ((askSeeds W S (cms.take 2)).withTrace.det g).2, x ∈ pre := by
    rw [← e]
    exact hb
  exact (seedAsked_log W S g _ c hc).mono hb'

theorem filter_lenBA : ∀ σ : Tc W,
    (lenB (preA W S) g σ).filter (notFb W) = σ.filter (notFb W)
  | [] => rfl
  | e :: σ => by
    show (((preAll W S e.1 e.2.1).withTrace.det g).2 ++ e :: lenB (preA W S) g σ).filter
      (notFb W) = _
    have h0 : (((preAll W S e.1 e.2.1).withTrace.det g).2).filter (notFb W) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨q', a, rfl, -⟩ := round_preAll W S g e.1 e.2.1 x hx
      simp [notFb, fbE]
    rw [List.filter_append, h0, List.nil_append, List.filter_cons, List.filter_cons,
      filter_lenBA σ]

/-- The word under a root does not see the entries laid in. -/
theorem extEnc_lenBA (σ : Tc W) (cm : Dig lam) :
    extEnc W (lenB (preA W S) g σ) cm = extEnc W σ cm := by
  rw [← extEnc_filter W (lenB (preA W S) g σ), filter_lenBA, extEnc_filter]

/-! ## The verifier's count -/

variable (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

theorem detBound_VCA (p : Params) (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) :
    DetBound (verifyAtFullKey W S cA r₀ p v x π) (tVC W) := by
  unfold verifyAtFullKey tVC
  split
  · refine ((detBound_seedIs W S _ _).bind
      (t := 2 + (tVQB (wTC W) W.depthReqT + (tVQB (wLC W) W.depthReqL +
        (tVQB (wBC W) W.depthReq + 0)))) fun _ =>
      (detBound_seedIs W S _ _).bind
        (t := tVQB (wTC W) W.depthReqT + (tVQB (wLC W) W.depthReqL +
          (tVQB (wBC W) W.depthReq + 0))) fun _ =>
      (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind
        (t := tVQB (wLC W) W.depthReqL + (tVQB (wBC W) W.depthReq + 0)) fun a =>
        (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind
          (t := tVQB (wBC W) W.depthReq + 0) fun b =>
          (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun c =>
            detBound_pure _ _).mono ?_
    omega
  · exact detBound_pure _ _

/-! ## The deterministic part -/

variable {W S cA r₀}

theorem coreA (hW : OKA W cA) (p : Params) {Rt : I → X → Prop} {Bad : Tc W → Prop}
    (hSd : ∀ tr cm s, ¬ Bad tr → RunsIn tr (outOfDomainSeedIs W S cm s) true → ¬ L.hasCollisionAt (extEnc W tr cm) s)
    (hT : ∀ tr (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) cm rec π,
      (∀ e ∈ tr, e.2.2 = g e.1 e.2.1) → SeedsFirstAll W S tr → ¬ Bad tr →
      RunsIn tr (outOfDomainSeedIs W S cm rec.1) true → RunsIn tr (vTA' W cA cm rec π) true →
      L.hasCollisionAt (extEnc W tr cm) rec.1 ∨ L.decodeIndex (extEnc W tr cm) rec ≠ none)
    (hL : ∀ tr (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) cm cm' rec rec' π,
      (∀ e ∈ tr, e.2.2 = g e.1 e.2.1) → SeedsFirstAll W S tr → ¬ Bad tr →
      RunsIn tr (outOfDomainSeedIs W S cm rec.1) true → RunsIn tr (outOfDomainSeedIs W S cm' rec'.1) true →
      RunsIn tr (vLA' W cA cm cm' rec rec' π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec)
    (hO : ∀ tr (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) cm x rec π,
      (∀ e ∈ tr, e.2.2 = g e.1 e.2.1) → SeedsFirstAll W S tr → ¬ Bad tr →
      RunsIn tr (outOfDomainSeedIs W S cm rec.1) true → RunsIn tr (vBA' W cA r₀ cm x rec π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) rec = some i ∧ Rt i x)
    (hE : ∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)
    (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) (trC rest trV : Tc W) (u : Unit)
    (hsub : trV ⊆ rest) (hrun : RunsIn trV (verifyAtFullKey W S cA r₀ p v x π) true)
    (hg : ∀ e ∈ (trC ++ [annE W v.cm u]) ++ rest, e.2.2 = g e.1 e.2.1)
    (hnb : ¬ Bad (lenB (preA W S) g ((trC ++ [annE W v.cm u]) ++ rest))) :
    ∃ i, L.decodeIndex (extEnc W trC v.cm) v.rcd = some i ∧ Rt i x := by
  have hn : ∀ o q, (preAll W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preAll W S o q)
  set tr : Tc W := lenB (preA W S) g ((trC ++ [annE W v.cm u]) ++ rest) with htr
  have hrun' : RunsIn tr (verifyAtFullKey W S cA r₀ p v x π) true :=
    hrun.mono fun e he => mem_lenB (preA W S) g _ e (List.mem_append_right _ (hsub he))
  have hans : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1 := lenB_ans (preA W S) hn g _ hg
  have hfirst : SeedsFirstAll W S tr := seedsFirstAll_of_asksFirst W S g tr ⟨_, rfl⟩
  have hsplit : tr = lenB (preA W S) g (trC ++ [annE W v.cm u]) ++ lenB (preA W S) g rest :=
    lenB_append (preA W S) g _ _
  have hann : Announced W (lenB (preA W S) g (trC ++ [annE W v.cm u])) v.cm := by
    cases u
    exact mem_lenB (preA W S) g _ _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
  have hext : extEnc W trC v.cm = extEnc W tr v.cm := by
    rw [← extEnc_ann trC v.cm u v.cm, ← extEnc_lenBA W S g (trC ++ [annE W v.cm u]) v.cm, hsplit]
    exact hE _ _ v.cm (hsplit ▸ hnb) hann
  rw [hext]
  unfold verifyAtFullKey at hrun'
  split at hrun'
  · rename_i πT cmj recj πL πB _ _ _
    simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun'
    obtain ⟨s0, hs0, sj, hsj, a, ha, b, hb, c, hc, habc⟩ := hrun'
    simp only [Bool.and_eq_true] at habc
    obtain ⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := habc
    have hc0 : ¬ L.hasCollisionAt (extEnc W tr v.cm) v.rcd.1 := hSd tr _ _ hnb hs0
    have hcj : ¬ L.hasCollisionAt (extEnc W tr cmj) recj.1 := hSd tr _ _ hnb hsj
    obtain ⟨_, _, ha'⟩ := runsIn_verifyB_of_strict hW.T ha
    obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hW.Lk hb
    obtain ⟨_, _, hc'⟩ := runsIn_verifyB_of_strict hW.B hc
    exact pathLemmaC ((hT tr g v.cm v.rcd _ hans hfirst hnb hs0 ha').resolve_left hc0)
      ((hL tr g v.cm cmj v.rcd recj _ hans hfirst hnb hs0 hsj hb').imp_right
        fun h => h.resolve_left hcj)
      (hO tr g cmj x recj _ hans hfirst hnb hsj hc')
  · exact absurd (runsIn_pure_iff.1 hrun') (by simp)

/-! ## The bound, for a key and a proof of any types -/

variable (W S cA r₀)

section G
variable {IVK Pf : Type} (full : IVK → Pf → FullKey lam L aT aL) (low : Pf → RequestProof lam L)
  (cmOf : IVK → Dig lam) (rcOf : IVK → L.Rec)

/-- The verifier at a key and a proof from which those of `verifyAtFullKey` are put together. -/
def VG (p : Params) (k : IVK) (x : X) (π : Pf) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyAtFullKey W S cA r₀ p (full k π) x (low π)

/-- The index extractor: the index decoder on what the committer's trace determines under the key's
root, and the key's record. -/
def extractorG : ZKCP.Gen.Extractor (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit IVK Pf where
  Ei := fun k tr => L.decodeIndex (extEnc W tr (cmOf k)) (rcOf k)
  Ew := fun _ _ _ _ _ => ()

def joinedG (p : Params) {St : Type} (Ct : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (IVK × St))
    (Pt : St → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (X × Pf)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  Ct.bind fun a =>
    (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.ann (cmOf a.1)).bind fun _ =>
    (Pt a.2).bind fun xp => (VG W S cA r₀ full low p a.1 xp.1 xp.2).bind fun _ => OComp.pure ()

theorem joinedG_queryBound (p : Params) {St : Type}
    {Ct : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (IVK × St)}
    {Pt : St → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (X × Pf)} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (joinedG W S cA r₀ full low cmOf p Ct Pt).QueryBound (tC + tP + tVC W + 1) := by
  have h : (joinedG W S cA r₀ full low cmOf p Ct Pt).QueryBound
      (tC + (1 + (tP + (tVC W + 0)))) := by
    unfold joinedG
    exact hC.bind fun a =>
        (detBound_ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.ann
          (cmOf a.1)).queryBound.bind fun _ =>
      (hP a.2).bind fun xp =>
        (detBound_VCA W S cA r₀ p (full a.1 xp.2) xp.1 (low xp.2)).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- The bound: n εs + 2 (n + 1)² / 2^lam at n = 5 (tC + tP + tVC + 1). -/
def soundnessBoundOverTypedOracles (εs : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞ := fun tC tP =>
  (((tC + tP + tVC W + 1) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
    2 * (((tC + tP + tVC W + 1) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

/-- Index binding for the languages from the event Bad, for every scheme whose verifier is `VG`. -/
theorem bindingGAt {ISK : Type} (hcm : ∀ k π, (full k π).cm = cmOf k)
    (hrc : ∀ k π, (full k π).rcd = rcOf k) (p : Params)
    (Ryes Rt : I → X → Prop) (εs : ℝ≥0∞) (hsub : ∀ i x, Ryes i x → Rt i x)
    (hB : BcsAtA W S cA r₀ Rt εs) (hW : OKA W cA)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit IVK ISK Pf)
    (hA : A.V = VG W S cA r₀ full low p) :
    ZKCP.Gen.HasIndexBindingWith (relPair Ryes Rt hsub) A (extractorG W cmOf rcOf)
      (soundnessBoundOverTypedOracles W εs) := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨Bad, hrare, -, hSd, hT, hL, hO, hE⟩ := hB
  have hn : ∀ o q, (preAll W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preAll W S o q)
  have hpt : ∀ f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)),
      PrCoins f (ZKCP.Gen.bindingExp A (extractorG W cmOf rcOf) Ct Pt)
          (ZKCP.Gen.bindingBad (relPair Ryes Rt hsub)) ≤
        PrCoins f (between (preA W S) (joinedG W S cA r₀ full low cmOf p Ct Pt)).withTrace
          {o | Bad o.2} := by
    intro f
    unfold PrCoins
    rw [between_law (preA W S) hn f, pr_map]
    simp only [ZKCP.Gen.bindingExp, bind_eq, pure_eq, joinedG, _root_.Compile.withTrace_bind,
        OComp.bind_assoc,
      OComp.ask, OComp.withTrace, OComp.bind, OComp.runEager_bind, OComp.runEager]
    refine pr_bind_le_bind _ _ _ _ _ fun a ha => pr_bind_le_bind _ _ _ _ _ fun b hb => ?_
    have e1 : (A.V a.1.1 b.1.1 b.1.2).runEager f =
        ((VG W S cA r₀ full low p a.1.1 b.1.1 b.1.2).withTrace.runEager f).map Prod.fst := by
      rw [hA]
      exact (runEager_withTrace_fst f _).symm
    rw [e1, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
    rintro ⟨hacc, hbad⟩
    by_contra hnb
    have hrun : RunsIn c.2 (verifyAtFullKey W S cA r₀ p (full a.1.1 b.1.2) b.1.1 (low b.1.2)) true := by
      have := runsIn_of_mem_support (detBound_VCA W S cA r₀ p (full a.1.1 b.1.2) b.1.1
        (low b.1.2)) f c hc
      have hc1 : c.1 = true := hacc
      rwa [hc1] at this
    have hnb' : ¬ Bad (lenB (preA W S) f
        ((a.2 ++ [annE W (full a.1.1 b.1.2).cm (f OracleName.ann (cmOf a.1.1))]) ++
          (b.2 ++ (c.2 ++ [])))) := by
      rw [hcm]
      simpa [annE] using hnb
    have hgs : ∀ e ∈ (a.2 ++ [annE W (full a.1.1 b.1.2).cm (f OracleName.ann (cmOf a.1.1))]) ++
        (b.2 ++ (c.2 ++ [])), e.2.2 = f e.1 e.2.1 := by
      intro e he
      rcases List.mem_append.1 he with h | h
      · rcases List.mem_append.1 h with h | h
        · exact support_withTrace_ans f _ a ha e h
        · rw [List.mem_singleton.1 h, hcm]
          rfl
      · rcases List.mem_append.1 h with h | h
        · exact support_withTrace_ans f _ b hb e h
        · rcases List.mem_append.1 h with h | h
          · exact support_withTrace_ans f _ c hc e h
          · exact absurd h List.not_mem_nil
    obtain ⟨i, hi, hr⟩ := coreA hW p hSd hT hL hO hE f (full a.1.1 b.1.2) b.1.1 (low b.1.2) a.2
      (b.2 ++ (c.2 ++ [])) c.2 _
      (fun e he => List.mem_append_right _ (List.mem_append_left _ he)) hrun hgs hnb'
    have hi' : (extractorG W cmOf rcOf (X := X) (Pf := Pf)).Ei a.1.1 a.2 = some i := by
      rw [hcm, hrc] at hi
      exact hi
    simp only [hi'] at hbad
    rcases hbad with hb | hb
    · exact hb ⟨(), hr⟩
    · exact hb hr
  calc
    Rom.Pr (ZKCP.Gen.bindingExp A (extractorG W cmOf rcOf) Ct Pt)
          (fun _ => ZKCP.Gen.bindingBad (relPair Ryes Rt hsub)) ≤
        Rom.Pr (between (preA W S) (joinedG W S cA r₀ full low cmOf p Ct Pt)).withTrace
          (fun _ => {o | Bad o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (between (preA W S) (joinedG W S cA r₀ full low cmOf p Ct Pt)).withTrace.law
          {o | Bad o.2} := Pr_eq_law _ _
    _ ≤ soundnessBoundOverTypedOracles W εs tC tP :=
        hrare Unit _ _ (between_bound (preA W S) 4
          (fun o q => (detBound_preAll W S o q).queryBound) _ _
          (joinedG_queryBound W S cA r₀ full low cmOf p hC hP))

/-- Index binding for the languages from explicit lists, for every scheme whose verifier is `VG`. -/
theorem cmsA_binding_at {ISK : Type} (hcm : ∀ k π, (full k π).cm = cmOf k)
    (hrc : ∀ k π, (full k π).rcd = rcOf k) (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hbB : Err.Below εB εs) (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal)
    (hlB : L.onlineBatch.loc.IsLocal) (hcT : aT.Coherent) (hcL : aL.Coherent)
    (hco : L.onlineBatch.ann.Coherent) (hW : OKA W cA)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit IVK ISK Pf)
    (hA : A.V = VG W S cA r₀ full low p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (extractorG W cmOf rcOf) (soundnessBoundOverTypedOracles W εs) :=
  bindingGAt W S cA r₀ full low cmOf rcOf hcm hrc p _ _ εs sub
    (cmsA_bcs W S cA r₀ Rno wit eR εT εL εB εs hS hSd hbT hbL hbB hlT hlL hlB hcT hcL hco hW)
    hW A hA

end G

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.bindingGAt
#print axioms TypedOracleCompiler.Compile.Batch.Cms.cmsA_binding_at

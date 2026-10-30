-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowBindingTo.lean: the proofs of CompileK/KnowExtTo.lean.

This file is about the step from a statement on lists of queries to the security experiment of index
binding, for an extractor that looks up the Fiat-Shamir answers before a round j.
The analogue of CompileK/KnowBindingT.lean for the extractor that follows the chain up to round j.

Main names, each under the hypotheses of its statement:
  `GoodRunT`, `VC_goodT`: what is known of an accepting run of the verifier of the analysis (`VC`,
    CompileK/KnowBinding.lean: the slot's check first), with one fact more: its first part holds the
    slot's whole chain. So the roots of the rounds and, if there is at least one round, the root of
    the encoded index occur there, whatever the prover has asked.
  `coreBTo`: outside Bad, after such a run. The extracted oracles and the extracted encoded index
    are those of the whole trace (they depend on Merkle entries alone, and are fixed once their
    roots occur). If the chain up to round j stands in the extractor's two traces, the verifier
    messages read there agree before round j with those of the verifier's own run (`runsIn_chainTo`,
    CompileK/ChainTo.lean; a trace has one answer at a point), and the map does not read the others:
    its value is a witness. If not: none, and a witness exists.
  `bindingOfRunTo` (stated here). `bindingBatchTo`, `bindingUpTo`, `some_of_chainTo`: the proofs of
    the statements of these names in `Spec`. `VC_goodT` is the analogue of `VC_good`
    (CompileK/KnowBinding.lean) with one field more; `bindingOfRunTo` that of `bindingOfRun`.

Limits: what the head of CompileK/KnowExtTo.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowBindingT
import CompileK.KnowExtTo

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The plain parts of the extracted transcript do not depend on the verifier messages. -/
theorem trStar_plains_rho {K : ℕ} (tr : Trace (spec lam K L)) :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p)) (rts : RootsOfChain lam s)
        (pls : Plains s) (ρ ρ' : Rho s),
      (trStar tr s A ws prjS rts pls ρ).plains = (trStar tr s A ws prjS rts pls ρ').plains
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (_, ws), prjS, (_, rts), (_, pls), (_, ρ), (_, ρ') =>
      congrArg (Prod.mk _) (trStar_plains_rho tr s A ws (fun p => prjS (.inr p)) rts pls ρ ρ')

theorem some_of_chainTo : Spec.some_of_chainTo := by
  intro I X Wn lam L W j wit v trC trP x π πB ρ e3 hf hr
  have h1 : (chainSTo W j π.cm x πB).follow (trC ++ trP) = some (some ρ) := follow_of_runsIn hf hr
  simp only [extractorBTo, e3, Option.bind_some, rhoTo, h1, Option.join_some, Option.map_some]

section Good
variable (W : QueryLayout lam L) (p : Params)

/-- `GoodRun` of CompileK/KnowBinding.lean, and: the first part of the trace holds the slot's whole
chain. -/
def GoodRunT (v : IVK lam L) (x : X) (π : Prf lam L) (trV : Tc W) : Prop :=
  ∃ (πT : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))
      (πL : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) (πB : OneProtocolProof lam L.onlineBatch) (trH rest : Tc W),
    π.piB = some πB ∧ trV = trH ++ rest ∧
    trH.filter isMk = [] ∧
    (∀ c ∈ RootsOfChain.list L.onlineBatch.loc.shape (rtsB W πB), (evM lam W.K L).OccursIn trH c) ∧
    RunsIn trV (vTS W p.sMT p.sFS v.cm πT) true ∧
    RunsIn trV (vLS W p.sMT p.sFS v.cm π.cm πL) true ∧
    RunsIn trV (vBS W p.sMT p.sFS π.cm x πB) true ∧
    ∃ z, RunsIn trH (chainS W π.cm x πB) (some z)

/-- The accepting runs of the verifier of the analysis are good, and their first part holds the
slot's whole chain: its trace begins with the exact trace of the slot's chain, which holds no Merkle
query and at which all roots of the slot's string that belong to a round occur. -/
theorem VC_goodT (f : Fam (spec lam W.K L)) (v : IVK lam L) (x : X) (π : Prf lam L) :
    ∀ o ∈ ((VC W p v x π).withTrace.runEager f).support, o.1 = true → GoodRunT W p v x π o.2 := by
  intro o ho hacc
  have hfalse : ∀ o : Bool × Tc W, o ∈
        ((OComp.pure false : TypedOracleComputation lam W.K L Bool).withTrace.runEager f).support →
      o.1 = true → False := by
    intro o ho hacc
    simp only [OComp.withTrace, OComp.runEager, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho
    cases hacc
  unfold VC at ho
  split at ho
  · rename_i πT πL πB _ _ e3
    split_ifs at ho
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_withTrace_bind f _ _ ho
      have hch : RunsIn a.2 (chainBS W π.cm x πB) a.1 :=
        runsIn_of_mem_support (detBound_chainB Tag.onl [π.cm] (some x) πB.salt πB.rtreq
            L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh id 0 .first πB.roots πB.plains)
          f a ha
      have hrest : RunsIn b.2 (restC W p v x π πT πL πB a.1) true := by
        have := runsIn_of_mem_support (detBound_restC W p v x π πT πL πB a.1) f b hb
        have hb1 : b.1 = true := hacc
        rwa [hb1] at this
      unfold restC at hrest
      simp only [runsIn_bind_iff, runsIn_pure_iff] at hrest
      obtain ⟨c, hc, a', ha', b', hb', habc⟩ := hrest
      simp only [Bool.and_eq_true] at habc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
      have hsubA : a.2 ⊆ a.2 ++ b.2 := fun e he => List.mem_append_left _ he
      have hsubB : b.2 ⊆ a.2 ++ b.2 := fun e he => List.mem_append_right _ he
      refine ⟨πT, πL, πB, a.2, b.2, e3, rfl,
        filter_nil_of_noMk (noMk_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) f ha, ?_,
        ha'.mono hsubB, hb'.mono hsubB, ?_, ?_⟩
      · rcases hr : a.1 with _ | ⟨ρ, rts, ph⟩
        · rw [hr] at hc
          exact absurd (runsIn_pure_iff.1 hc) (by simp)
        · rw [hr] at hch
          rw [rtsB_of_chainQB hch]
          exact roots_occur_chainB _ _ _ _ _ _ _ _ _ _ _ hch
      · rw [vBS_eq]
        exact (runsIn_bind_iff _ _ _).2 ⟨a.1, hch.mono hsubA, hc.mono hsubB⟩
      · rcases hr : a.1 with _ | z
        · rw [hr] at hc
          exact absurd (runsIn_pure_iff.1 hc) (by simp)
        · rw [hr] at hch
          exact ⟨z, hch⟩
    · exact (hfalse o ho hacc).elim
  · exact (hfalse o ho hacc).elim

end Good

section Core
variable {W : QueryLayout lam L} {p : Params}

/-- Under the hypotheses below: outside Bad, after a good run, the extractor names a witness, or
says none and a witness exists. -/
theorem coreBTo (hW : W.OKG) (hne : L.onlineBatch.loc.shape ≠ []) {j : ℕ} {Rno : I → X → Wn → Prop}
    {wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn} (hbl : TrBlind j wit)
    {Bad : Tc W → Prop}
    (hT : ∀ tr cm π, ¬ Bad tr → RunsIn tr (vT W cm π) true → L.decodeIndex (extEnc W tr cm) ≠ none)
    (hL : ∀ tr cm cm' π, ¬ Bad tr → RunsIn tr (vL W cm cm' π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ L.decodeIndex (extEnc W tr cm') = L.decodeIndex (extEnc W tr cm))
    (hO : ∀ tr cm x π, ¬ Bad tr → RunsIn tr (vB W cm x π) true →
      ∃ ρ rts ph,
        RunsIn tr (chainS W cm x π) (some (ρ, rts, ph)) ∧
        (L.decodeIndex (extEnc W tr cm) = none ∨
          ∃ i, L.decodeIndex (extEnc W tr cm) = some i ∧ Rno i x (wit x (extEnc W tr cm) (starB W tr π ρ))))
    (hE : ∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)
    (hR : ∀ tr tr' π ρ, ¬ Bad (tr ++ tr') →
      (∀ c ∈ RootsOfChain.list L.onlineBatch.loc.shape (rtsB W π), (evM lam W.K L).OccursIn tr c) →
      starB W tr π ρ = starB W (tr ++ tr') π ρ)
    (hY : ∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → (evM lam W.K L).OccursIn tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)
    (v : IVK lam L) (x : X) (π : Prf lam L) (trC trP trV : Tc W) (u : Unit)
    (hg : GoodRunT W p v x π trV) (hnb : ¬ Bad ((trC ++ [annE W v.cm u]) ++ (trP ++ trV)))
    (hfun : Trace.Fun ((trC ++ [annE W v.cm u]) ++ (trP ++ trV))) :
    ∃ i,
      L.decodeIndex (extEnc W trC v.cm) = some i ∧
      optR Rno i x ((extractorBTo W j wit).Ew v trC x π trP) := by
  obtain ⟨πT, πL, πB, trH, rest, e3, rfl, hmk, hocc, ha, hb, hc, zH, hzH⟩ := hg
  set tr : Tc W := (trC ++ [annE W v.cm u]) ++ (trP ++ (trH ++ rest)) with htr
  have hsub : trH ++ rest ⊆ tr := fun e he => List.mem_append_right _ (List.mem_append_right _ he)
  have hann : Announced W (trC ++ [annE W v.cm u]) v.cm := by
    cases u
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hext : extEnc W trC v.cm = extEnc W tr v.cm := by
    rw [← extEnc_ann trC v.cm u v.cm]
    exact hE _ _ v.cm hnb hann
  obtain ⟨_, _, ha'⟩ := runsIn_verifyB_of_strict hW.T (ha.mono hsub)
  obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hW.Lk (hb.mono hsub)
  obtain ⟨P1, P2, hc'⟩ := runsIn_verifyB_of_strict hW.B (hc.mono hsub)
  obtain ⟨ρ, rts, ph, hch, hw⟩ := hO tr π.cm x _ hnb hc'
  have hch' : RunsIn tr (chainS W π.cm x πB) (some (ρ, rts, ph)) := hch
  have hw' : L.decodeIndex (extEnc W tr π.cm) = none ∨
      ∃ i,
        L.decodeIndex (extEnc W tr π.cm) = some i ∧ Rno i x (wit x (extEnc W tr π.cm) (starB W tr πB ρ)) :=
    hw
  obtain ⟨i, hi, hr⟩ := pathLemmaB
    (Rno := fun i x => Rno i x (wit x (extEnc W tr π.cm) (starB W tr πB ρ))) (hT tr v.cm _ hnb ha')
    (hL tr v.cm π.cm _ hnb hb') hw'
  refine ⟨i, by rw [hext]; exact hi, ?_⟩
  -- the prefix that ends with the verifier's chain
  have hpre : ((trC ++ [annE W v.cm u]) ++ (trP ++ trH)) ++ rest = tr := by
    simp only [htr, List.append_assoc]
  have hfil : (trC ++ trP).filter isMk =
      ((trC ++ [annE W v.cm u]) ++ (trP ++ trH)).filter isMk := by
    have hann0 : [annE W v.cm u].filter isMk = [] := rfl
    simp only [List.filter_append, hmk, hann0, List.append_nil]
  have hsubH : trH ⊆ (trC ++ [annE W v.cm u]) ++ (trP ++ trH) := fun e he =>
    List.mem_append_right _ (List.mem_append_right _ he)
  have hsub3 : trC ++ trP ⊆ tr := fun e he =>
    (List.mem_append.1 he).elim (fun h => List.mem_append_left _ (List.mem_append_left _ h))
      fun h => List.mem_append_right _ (List.mem_append_left _ h)
  have hy : extEnc W (trC ++ trP) π.cm = extEnc W tr π.cm := by
    rw [extEnc_of_filter W hfil, ← hpre]
    exact hY _ _ π.cm (by rw [hpre]; exact hnb)
      ((cms_occur_chainB _ _ _ _ _ _ _ _ _ _ hne hzH π.cm (by simp)).mono hsubH)
  have hst : ∀ ρ', starB W (trC ++ trP) πB ρ' = starB W tr πB ρ' := fun ρ' => by
    rw [starB_of_filter W hfil, ← hpre]
    exact hR _ _ πB ρ' (by rw [hpre]; exact hnb) fun c hc => (hocc c hc).mono hsubH
  cases hfo : (chainSTo W j π.cm x πB).follow (trC ++ trP) with
  | none =>
    have hn : (extractorBTo W j wit).Ew v trC x π trP = none := by
      simp only [extractorBTo, e3, Option.bind_some, rhoTo, hfo, Option.join_none, Option.map_none]
    rw [hn]
    exact ⟨_, hr⟩
  | some z =>
    have hz : RunsIn (trC ++ trP) (chainSTo W j π.cm x πB) z := runsIn_of_follow hfo
    obtain ⟨ρ', hρ', hag⟩ := runsIn_chainTo j _ _ _ _ _ _ _ _ _ _ _ hch'
    have hzz : z = some ρ' := by
      have h1 := follow_of_runsIn hfun (hz.mono hsub3)
      have h2 := follow_of_runsIn hfun hρ'
      exact Option.some.inj (h1.symm.trans h2)
    subst hzz
    have hs : (extractorBTo W j wit).Ew v trC x π trP =
        some (wit x (extEnc W (trC ++ trP) π.cm) (starB W (trC ++ trP) πB ρ')) := by
      simp only [extractorBTo, e3, Option.bind_some, rhoTo, hfo, Option.join_some, Option.map_some]
    have hb2 : wit x (extEnc W tr π.cm) (starB W tr πB ρ') =
        wit x (extEnc W tr π.cm) (starB W tr πB ρ) :=
      hbl x _ _ _ (by unfold starB; rw [trStar_read, trStar_read])
        (trStar_plains_rho _ _ _ _ _ _ _ _ _)
        (by unfold starB; rw [trStar_rho, trStar_rho]; exact hag)
    rw [hs, hy, hst, hb2]
    exact hr

end Core

/-- Index binding with the natural extractor up to round j, from `hsub`, `hB`, `hW`, `hne`, `hbl`
and a verifier V' of the analysis that, for every fixed oracle, decides as V does, that flips no
coin and asks at most t' queries, and whose accepting runs are good (`GoodRunT`). The theorem is
about the scheme's own V; the bound counts the queries of V'. -/
theorem bindingOfRunTo (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (j : ℕ)
    (Ryes Rno : I → X → Wn → Prop) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    (N : LH.Nums) (hsub : ∀ i x w, Ryes i x w → Rno i x w) (hB : BcsAtKT W Rno wit N.εs)
    (hW : W.OKG) (hne : L.onlineBatch.loc.shape ≠ []) (hbl : TrBlind j wit)
    (V' : IVK lam L → X → Prf lam L → TypedOracleComputation lam W.K L Bool) (t' : ℕ)
    (hsame : ∀ f v x π, (V' v x π).runEager f = (V W p v x π).runEager f)
    (hdet : ∀ v x π, DetBound (V' v x π) t')
    (hgood : ∀ f v x π,
      ∀ o ∈ ((V' v x π).withTrace.runEager f).support, o.1 = true → GoodRunT W p v x π o.2) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))
      (ZKCP.Gen.withW (Option Wn) (argB W WP p)) (extractorBTo W j wit)
      (fun tC tP =>
        ((tC + tP + t' + 1 : ℕ) : ℝ≥0∞) * N.εs +
            2 * ((tC + tP + t' + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨Bad, hrare, -, hT, hL, hO, hE, hR, hY⟩ := hB
  have hpt : ∀ f : Fam (spec lam W.K L),
      PrCoins f (ZKCP.Gen.bindingExp
            (ZKCP.Gen.withW (Option Wn) (argB W WP p)) (extractorBTo W j wit) Ct Pt)
          (ZKCP.Gen.bindingBad (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))) ≤
        PrCoins f (joinedV W V' Ct Pt).withTrace {o | Bad o.2} := by
    intro f
    unfold PrCoins
    simp only [ZKCP.Gen.bindingExp, bind_eq, pure_eq, joinedV, withTrace_bind, OComp.bind_assoc,
      OComp.ask, OComp.withTrace, OComp.bind, OComp.runEager_bind, OComp.runEager]
    refine pr_bind_le_bind _ _ _ _ _ fun a ha => pr_bind_le_bind _ _ _ _ _ fun b hb => ?_
    have e1 : ((ZKCP.Gen.withW (Option Wn) (argB W WP p)).V a.1.1 b.1.1 b.1.2).runEager f =
        ((V' a.1.1 b.1.1 b.1.2).withTrace.runEager f).map Prod.fst :=
      ((runEager_withTrace_fst f _).trans (hsame f _ _ _)).symm
    rw [e1, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
    rintro ⟨hacc, hbad⟩
    by_contra hnb
    have hnb' : ¬ Bad ((a.2 ++ [annE W a.1.1.cm (f OracleName.ann a.1.1.cm)]) ++ (b.2 ++ c.2)) := by
      simpa [annE] using hnb
    have hfun : Trace.Fun ((a.2 ++ [annE W a.1.1.cm (f OracleName.ann a.1.1.cm)]) ++ (b.2 ++ c.2)) :=
      (((traceOf_support f _ ha).append (traceOf_ann W f a.1.1.cm)).append
        ((traceOf_support f _ hb).append (traceOf_support f _ hc))).fun
    obtain ⟨i, hi, hr⟩ := coreBTo hW hne hbl hT hL hO hE hR hY a.1.1 b.1.1 b.1.2 a.2 b.2 c.2 _
      (hgood f _ _ _ c hc hacc) hnb' hfun
    have hi' : (extractorBTo W j wit).Ei a.1.1 a.2 = some i := hi
    simp only [hi'] at hbad
    rcases hbad with hb | hb
    · exact hb ⟨_, hr⟩
    · exact hb hr
  calc
    Rom.Pr (ZKCP.Gen.bindingExp (ZKCP.Gen.withW (Option Wn) (argB W WP p))
            (extractorBTo W j wit) Ct Pt)
          (fun _ =>
            ZKCP.Gen.bindingBad (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))) ≤
        Rom.Pr (joinedV W V' Ct Pt).withTrace (fun _ => {o | Bad o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (joinedV W V' Ct Pt).withTrace.law {o | Bad o.2} := Pr_eq_law _ _
    _ ≤ ((tC + tP + t' + 1 : ℕ) : ℝ≥0∞) * N.εs +
          2 * ((tC + tP + t' + 1 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
        hrare Unit (joinedV W V' Ct Pt) _ (joinedV_queryBound W hdet hC hP)

theorem bindingBatchTo : Spec.bindingBatchTo :=
  fun I X Wn lam L W WP p j Ryes Rno wit N hsub hs hbl hlT hlL hlB hcoh hW hne =>
    bindingOfRunTo W WP p j Ryes Rno wit N hsub
      (bcsSoundBatchKT I X Wn lam L W Rno wit N.εs hs hlT hlL hlB hcoh hW) hW hne hbl (VC W p)
      (tVB W) (VC_same W p) (detBound_VC W p) (VC_goodT W p)

open ZKCP Compile.GenMap Compile.GenPub in
theorem bindingUpTo : Spec.bindingUpTo := by
  intro I X Wn lam L W WP p j Ryes Rno wit N hsub hs hbl hlT hlL hlB hcoh hW hne
  have hb := bindingBatchTo I X Wn lam L W WP p j Ryes Rno wit N hsub hs hbl hlT hlL hlB hcoh hW hne
  have h1 := GenPub.binding (A := Gen.withW (Option Wn) (argB W WP p)) pubK _ hb
  rw [pubArg_withW] at h1
  have h2 := GenMap.binding (via_withW (Option Wn) (via_K W WP p)) stripK_liftK _ h1
  unfold extractorBKTo
  exact Gen.binding_congr_V _ (A := Gen.withW (Option Wn) (argBK W WP p))
    (A' := Gen.withW (Option Wn) (argBKE W WP p))
    (fun v x π => congrFun (congrFun (congrFun (V_KE W WP p).symm v) x) π) h2

end Compile.Batch

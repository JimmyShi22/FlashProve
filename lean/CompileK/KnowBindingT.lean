-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowBindingT.lean: from traces to the experiment of index binding, with the natural
extractor for a wide witness map.

This file is about the step from a statement on lists of queries to the security experiment of index
binding, in which the extractor is not handed the verifier's queries.
The proofs of the statements of CompileK/KnowExtT.lean. The analogue of CompileK/KnowBinding.lean
for a wide witness map; that file's verifier of the analysis (`VC`: the slot's check first) and its
lemmas on it are used as they stand.
CompileK/KnowSoundT.lean (`BcsAtKT`) speaks of a trace that holds the verifier's queries. The
extractor is handed the committer's trace and the prover's.
  Part 1. Traces under a fixed oracle hold its answers (`traceOf_support`), so no point has two
  answers.
  Part 2. The root of the encoded index occurs in every trace in which a chain of at least one
  round, begun in the phase `.first`, runs to an end (result `some`; `cms_occur_chainB`); the
  extracted transcript and the extracted encoded index depend on a trace only through its Merkle
  entries (`starB_of_filter`, `extEnc_of_filter`).
  Part 3. `some_of_chain`; `coreBT`: outside Bad, after a good run (`GoodRun`,
  CompileK/KnowBinding.lean): if the extractor's two traces hold the slot's chain, the verifier
  messages that it reads there are those of the verifier's own run (a trace has one answer at a
  point), transcript and encoded index are those of the whole trace, and its value is a witness; if
  not, it says none, and a witness exists.
  Part 4. `bindingOfRunT`, `bindingBatchT : Spec.bindingBatchT`, `bindingUpT : Spec.bindingUpT`.
  `bindingOfRunT` is the analogue of `bindingOfRun` (CompileK/KnowBinding.lean) with the extractor,
  the relation, the hypothesis on traces and the core replaced, and with `hne`; `bindingUpT`:
  `bindingBatchT`, then the step of `bindingUp` (CompileK/KnowBindingUp.lean) for this extractor.
Each under the hypotheses of its statement.

Limits: what the head of CompileK/KnowExtT.lean lists as not said is not said here either: above
all, how often the extractor says none while the verifier accepts is not bounded here.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowBinding
import CompileK.KnowSoundT
import Rom.ExitDown

set_option autoImplicit false

noncomputable section

/-! ## Part 1. Traces under a fixed oracle -/

namespace Rom

variable {S : OSpec} {α : Type}

/-- A trace made under the oracle f holds the answers of f. -/
theorem traceOf_support (f : Fam S) (c : OComp S α) {o : α × Trace S}
    (ho : o ∈ (c.withTrace.runEager f).support) : Trace.Of f o.2 := by
  rw [withTrace_retr] at ho
  obtain ⟨o', -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ho
  intro oo q r hm
  obtain ⟨⟨o1, q1, r1⟩, -, he⟩ := List.mem_map.1 hm
  cases he
  rfl

end Rom

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem traceOf_ann (W : QueryLayout lam L) (f : Fam (spec lam W.K L)) (cm : Dig lam) :
    Trace.Of f [annE W cm (f OracleName.ann cm)] := by
  intro o q r hm
  cases List.mem_singleton.1 hm
  rfl

/-! ## Part 2. What occurs at a chain; what depends on Merkle entries alone -/

section Chain
variable {K : ℕ}

/-- The roots of the encoded indices (`cms.take 2`) occur in every trace in which a chain of at
least one round, begun in the phase `.first`, runs to an end. (They are in the chain's first query:
`Head.f1`, Compile/Batch/Oracles.lean.) -/
theorem cms_occur_chainB {tr : Trace (spec lam K L)} {t : Tag} {cms : List (Dig lam)} {x : Option X}
    {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      s ≠ [] →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i .first rts pls)
        (some (ρ, RTs, ph')) →
      ∀ c ∈ cms.take 2, (evM lam K L).OccursIn tr c
  | [], _, _, _, _, _, _, _, _, _, hne, _, _, _ => absurd rfl hne
  | _ :: _, (_, _), (_, _), _, _, _, _, (_, _), (_, _), (_, _), _, h, c, hc => by
      obtain ⟨cur, ans, ph₁, rts', hv, hq, -, -⟩ := runsIn_chainB_cons h
      cases hv with
      | f1 root ans hk => exact ⟨_, hq, List.mem_append_right _ hc⟩

end Chain

section Filter
variable (W : QueryLayout lam L)

theorem starB_of_filter {tr tr' : Tc W} (h : tr.filter isMk = tr'.filter isMk)
    (π : OneProtocolProof lam L.onlineBatch) (ρ : Rho L.onlineBatch.loc.shape) :
    starB W tr π ρ = starB W tr' π ρ :=
  trStar_congr _ _ _ _ _ _ _ fun c _ d j => by rw [← extLeaf_filter tr, h, extLeaf_filter]

theorem extEnc_of_filter {tr tr' : Tc W} (h : tr.filter isMk = tr'.filter isMk) (cm : Dig lam) :
    extEnc W tr cm = extEnc W tr' cm := by
  unfold extEnc
  congr 1
  funext q
  rw [← extLeaf_filter tr, h, extLeaf_filter]

end Filter

/-! ## Part 3. The deterministic core -/

theorem some_of_chain : Spec.some_of_chain := by
  intro I X Wn lam L W wit v trC trP x π πB z e3 hf hr
  have h1 : (chainS W π.cm x πB).follow (trC ++ trP) = some (some z) := follow_of_runsIn hf hr
  simp only [extractorBT, e3, Option.bind_some, rhoB, h1, Option.join_some, Option.map_some]

section Core
variable {W : QueryLayout lam L} {p : Params}

/-- Under the hypotheses below: outside Bad, after a good run, the extractor names a witness, or
says none and a witness exists. -/
theorem coreBT (hW : W.OKG) (hne : L.onlineBatch.loc.shape ≠ []) {Rno : I → X → Wn → Prop}
    {wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn} {Bad : Tc W → Prop}
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
    (hg : GoodRun W p v x π trV) (hnb : ¬ Bad ((trC ++ [annE W v.cm u]) ++ (trP ++ trV)))
    (hfun : Trace.Fun ((trC ++ [annE W v.cm u]) ++ (trP ++ trV))) :
    ∃ i,
      L.decodeIndex (extEnc W trC v.cm) = some i ∧ optR Rno i x ((extractorBT W wit).Ew v trC x π trP) := by
  obtain ⟨πT, πL, πB, trH, rest, e3, rfl, -, -, ha, hb, hc⟩ := hg
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
  -- the middle trace: the extractor's two traces with the announcement between them
  have hpre : ((trC ++ [annE W v.cm u]) ++ trP) ++ (trH ++ rest) = tr := by
    simp only [htr, List.append_assoc]
  have hfil : (trC ++ trP).filter isMk = ((trC ++ [annE W v.cm u]) ++ trP).filter isMk := by
    have hann0 : [annE W v.cm u].filter isMk = [] := rfl
    simp only [List.filter_append, hann0, List.append_nil]
  have hsub2 : trC ++ trP ⊆ (trC ++ [annE W v.cm u]) ++ trP := fun e he =>
    (List.mem_append.1 he).elim (fun h => List.mem_append_left _ (List.mem_append_left _ h))
      fun h => List.mem_append_right _ h
  have hsub3 : trC ++ trP ⊆ tr := fun e he => by
    rw [← hpre]
    exact List.mem_append_left _ (hsub2 he)
  cases hfo : (chainS W π.cm x πB).follow (trC ++ trP) with
  | none =>
    have hn : (extractorBT W wit).Ew v trC x π trP = none := by
      simp only [extractorBT, e3, Option.bind_some, rhoB, hfo, Option.join_none, Option.map_none]
    rw [hn]
    exact ⟨_, hr⟩
  | some z =>
    have hz : RunsIn (trC ++ trP) (chainS W π.cm x πB) z := runsIn_of_follow hfo
    have hzz : z = some (ρ, rts, ph) := by
      have h1 := follow_of_runsIn hfun (hz.mono hsub3)
      have h2 := follow_of_runsIn hfun hch'
      exact Option.some.inj (h1.symm.trans h2)
    subst hzz
    have hs : (extractorBT W wit).Ew v trC x π trP =
        some (wit x (extEnc W (trC ++ trP) π.cm) (starB W (trC ++ trP) πB ρ)) := by
      simp only [extractorBT, e3, Option.bind_some, rhoB, hfo, Option.join_some, Option.map_some]
    have hy : extEnc W (trC ++ trP) π.cm = extEnc W tr π.cm := by
      rw [extEnc_of_filter W hfil, ← hpre]
      exact hY _ _ π.cm (by rw [hpre]; exact hnb)
        ((cms_occur_chainB _ _ _ _ _ _ _ _ _ _ hne hz π.cm (by simp)).mono hsub2)
    have hst : starB W (trC ++ trP) πB ρ = starB W tr πB ρ := by
      rw [starB_of_filter W hfil, ← hpre]
      refine hR _ _ πB ρ (by rw [hpre]; exact hnb) fun c hc => ?_
      rw [rtsB_of_chainQB hz] at hc
      exact (roots_occur_chainB _ _ _ _ _ _ _ _ _ _ _ hz c hc).mono hsub2
    rw [hs, hy, hst]
    exact hr

end Core

/-! ## Part 4. Index binding -/

/-- Index binding with the natural extractor, from `hsub`, `hB`, `hW`, `hne` and a verifier V' of
the analysis that, for every fixed oracle, decides as V does, that flips no coin and asks at most t'
queries, and whose accepting runs are good. The theorem is about the scheme's own V; the bound
counts the queries of V'. -/
theorem bindingOfRunT (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (N : LH.Nums)
    (hsub : ∀ i x w, Ryes i x w → Rno i x w) (hB : BcsAtKT W Rno wit N.εs) (hW : W.OKG)
    (hne : L.onlineBatch.loc.shape ≠ []) (V' : IVK lam L → X → Prf lam L → TypedOracleComputation lam W.K L Bool) (t' : ℕ)
    (hsame : ∀ f v x π, (V' v x π).runEager f = (V W p v x π).runEager f)
    (hdet : ∀ v x π, DetBound (V' v x π) t')
    (hgood : ∀ f v x π,
      ∀ o ∈ ((V' v x π).withTrace.runEager f).support, o.1 = true → GoodRun W p v x π o.2) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))
      (ZKCP.Gen.withW (Option Wn) (argB W WP p)) (extractorBT W wit) (fun tC tP =>
        ((tC + tP + t' + 1 : ℕ) : ℝ≥0∞) * N.εs +
            2 * ((tC + tP + t' + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨Bad, hrare, -, hT, hL, hO, hE, hR, hY⟩ := hB
  have hpt : ∀ f : Fam (spec lam W.K L),
      PrCoins f
          (ZKCP.Gen.bindingExp (ZKCP.Gen.withW (Option Wn) (argB W WP p)) (extractorBT W wit) Ct Pt)
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
    obtain ⟨i, hi, hr⟩ := coreBT
      hW hne hT hL hO hE hR hY a.1.1 b.1.1 b.1.2 a.2 b.2 c.2 _ (hgood f _ _ _ c hc hacc) hnb' hfun
    have hi' : (extractorBT W wit).Ei a.1.1 a.2 = some i := hi
    simp only [hi'] at hbad
    rcases hbad with hb | hb
    · exact hb ⟨_, hr⟩
    · exact hb hr
  calc
    Rom.Pr (ZKCP.Gen.bindingExp (ZKCP.Gen.withW (Option Wn) (argB W WP p))
            (extractorBT W wit) Ct Pt)
          (fun _ =>
            ZKCP.Gen.bindingBad (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))) ≤
        Rom.Pr (joinedV W V' Ct Pt).withTrace (fun _ => {o | Bad o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (joinedV W V' Ct Pt).withTrace.law {o | Bad o.2} := Pr_eq_law _ _
    _ ≤ ((tC + tP + t' + 1 : ℕ) : ℝ≥0∞) * N.εs +
          2 * ((tC + tP + t' + 1 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
        hrare Unit (joinedV W V' Ct Pt) _ (joinedV_queryBound W hdet hC hP)

/-- The same with the bound `epsB`, from `hsub`, the event Bad of one wire (`hB`), `hW` and `hne`,
with the verifier of the analysis of CompileK/KnowBinding.lean. -/
theorem bindingBatchTAt (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (Ryes Rno : I → X → Wn → Prop) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    (N : LH.Nums) (hsub : ∀ i x w, Ryes i x w → Rno i x w) (hB : BcsAtKT W Rno wit N.εs)
    (hW : W.OKG) (hne : L.onlineBatch.loc.shape ≠ []) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))
      (ZKCP.Gen.withW (Option Wn) (argB W WP p)) (extractorBT W wit) (epsB W N) :=
  bindingOfRunT W WP p Ryes Rno wit N hsub hB hW hne (VC W p) (tVB W) (VC_same W p)
    (detBound_VC W p) (VC_good W p)

theorem bindingBatchT : Spec.bindingBatchT :=
  fun I X Wn lam L W WP p Ryes Rno wit N hsub hs hlT hlL hlB hcoh hW hne =>
    bindingBatchTAt W WP p Ryes Rno wit N hsub
      (bcsSoundBatchKT I X Wn lam L W Rno wit N.εs hs hlT hlL hlB hcoh hW) hW hne

open ZKCP Compile.GenMap Compile.GenPub in
theorem bindingUpT : Spec.bindingUpT := by
  intro I X Wn lam L W WP p Ryes Rno wit N hsub hs hlT hlL hlB hcoh hW hne
  have hb := bindingBatchT I X Wn lam L W WP p Ryes Rno wit N hsub hs hlT hlL hlB hcoh hW hne
  have h1 := GenPub.binding (A := Gen.withW (Option Wn) (argB W WP p)) pubK _ hb
  rw [pubArg_withW] at h1
  have h2 := GenMap.binding (via_withW (Option Wn) (via_K W WP p)) stripK_liftK _ h1
  unfold extractorBKT
  exact Gen.binding_congr_V _ (A := Gen.withW (Option Wn) (argBK W WP p))
    (A' := Gen.withW (Option Wn) (argBKE W WP p))
    (fun v x π => congrFun (congrFun (congrFun (V_KE W WP p).symm v) x) π) h2

end Compile.Batch

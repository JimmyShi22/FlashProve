-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsMore.lean: short lemmas behind the entry's arm with the answers alone
(LinkAns.lean, LinkAnsPr.lean, LinkAnsOne.lean).

  `arm_overOne`      an arm as an algorithm over the hash function (`OComp.overOne`: each typed
                     query becomes the calls for its blocks) has, at every function g, the verdict
                     of the arm's run at the typed oracle functions that m reads out of g
  `arm_pr_hash`      `arm_pr_one` with the arm so run: the maker, then the arm, both asking the one
                     function
  `extEnc_logOne`, `linkHolds_logOne`   the words under the roots, read off the typed log, are those
                     read off the one-block entries of the maker's log of strings, then the arm's
                     log
  `VLA'_det`         the run of the arm with the lax Link is the conjunction of the three runs
  `badLA_len_rare`   the other half of the lift: for every algorithm B over the typed oracles with
                     at most n queries, its lengthened log lies in `BadLA` with probability at most
                     5n εs + 2 (5n + 1)² / 2^lam
  `linkA_fixes_len`  the words stay, from the lengthened log: if the lengthened log of tr ++ tr'
                     lies outside `BadLA`, the word under a root whose first seed query stands in
                     tr is the same at tr and at tr ++ tr'

Limits: those in the heads of LinkAnsPr.lean and LinkAnsOne.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsOne

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-! ## The arm as an algorithm over the hash function -/

/-- An algorithm without coins has, under fixed oracle functions, the value of its run. -/
theorem runEager_noCoin {Sp : OSpec} {α : Type} (G : Fam Sp) (c : OComp Sp α) (hc : c.NoCoin) :
    c.runEager G = PMF.pure (c.withTrace.det G).1 := by
  rw [← runEager_withTrace_fst G c, runEager_withTrace_det G c hc, PMF.pure_map]

/-- An arm over the hash function has, at every function, the verdict of its run at the typed oracle
functions read out of that function. -/
theorem arm_overOne {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ z, (V z).NoCoin) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (g : Fam (rom lam)) (z : OutLA lam L aL) :
    ((V z).overOne m).runEager g = PMF.pure (runA W V (readBlocks m g) z).1 := by
  rw [runEager_overOne, runEager_noCoin _ _ (hV z)]
  rfl

/-- An arm is sound against every maker over one hash function, the arm itself asking that function:
the maker runs, then the arm; the arm accepts, and what it promises fails on the typed log, with
probability at most n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + tVL) and t bounds the maker's
queries. The premises are those of `arm_pr` (LinkAnsPr.lean): Link's soundness round by round (hsL),
its locality (hlL), the annotation's coherence (hcL), `OKLA W`, `AnsOK cA`, `S.Law εs`, the bound on
the rounds' errors (hbL), `IsArm`. m is any coding. -/
theorem arm_pr_hash {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr (A.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) x.1) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
            x.1.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine le_trans (le_of_eq ?_) (arm_pr_one hsL hlL hcL hW hA hSd hbL hV m A t hq)
  unfold Rom.Pr
  refine MeasureTheory.lintegral_congr fun g => ?_
  unfold PrCoins
  have e : (A.withTrace.bind fun o => ((V o.1).overOne m).bind fun b =>
      (OComp.pure (o, b) : OComp (rom lam) ((OutLA lam L aL × Trace (rom lam)) × Bool))).runEager g
          =
      (A.withTrace.runEager g).map fun o => (o, (runA W V (readBlocks m g) o.1).1) := by
    rw [OComp.runEager_bind, ← PMF.bind_pure_comp]
    refine congrArg _ (funext fun o => ?_)
    rw [OComp.runEager_bind, arm_overOne (fun z => noCoin_of_detBound (hV.det z)), PMF.pure_bind]
    rfl
  rw [e, pr_map]
  rfl

/-! ## The words, read off the maker's log of strings -/

/-- The one-block entries read off a log of strings are one-block entries. -/
theorem single_singleTr {Sp : OSpec} (m : OracleCoding Sp lam) :
    ∀ tr : Trace (rom lam), single m (singleTr m tr) = singleTr m tr
  | [] => rfl
  | e :: tr => by
    have ih := single_singleTr m tr
    have e1 : singleTr m (e :: tr) = singleTr m [e] ++ singleTr m tr :=
      singleTr_append m [e] tr
    obtain ⟨u, s, r⟩ := e
    cases u
    rw [e1, singleTr_one]
    unfold single at ih ⊢
    rw [List.filter_append, ih]
    by_cases hb : m.blocks (m.dec s).1 = 1
    · simp [hb]
    · simp [hb]

/-- A log with g's answers is not moved when its answers are replaced by g's. -/
theorem retr_of_ans {Sp : OSpec} (g : Fam Sp) :
    ∀ tr : Trace Sp, (∀ e ∈ tr, e.2.2 = g e.1 e.2.1) → retr g tr = tr
  | [], _ => rfl
  | e :: tr, h => by
    have ih := retr_of_ans g tr fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h0 := h e List.mem_cons_self
    obtain ⟨o, q, r⟩ := e
    show (⟨o, q, g o q⟩ : QA Sp) :: retr g tr = _
    rw [ih, ← (show r = g o q from h0)]

/-- The word under a root, read off the typed log of maker and arm, is the word read off the
one-block entries of the maker's log of strings, then the arm's log. Asked: a leaf and a node are
one block of the hash function; the maker's log holds g's answers. -/
theorem extEnc_logOne (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (g : Fam (rom lam)) (o : OutLA lam L aL × Trace (rom lam))
    (hans : ∀ e ∈ o.2, e.2.2 = g e.1 e.2.1) (cm : Dig lam) :
    extEnc W (logOne W V m (readBlocks m g) o) cm =
      extEnc W (singleTr m o.2 ++ (runA W V (readBlocks m g) o.1).2) cm := by
  rw [← extEnc_single W m hl hn (logOne W V m (readBlocks m g) o),
    ← extEnc_single W m hl hn (singleTr m o.2 ++ (runA W V (readBlocks m g) o.1).2)]
  have e : single m (logOne W V m (readBlocks m g) o) =
      single m (singleTr m o.2 ++ (runA W V (readBlocks m g) o.1).2) := by
    have e1 : single m (upTr m (readBlocks m g) o.2) = single m (singleTr m o.2) := by
      rw [single_upTr, glue_readBlocks, retr_of_ans g o.2 hans, single_singleTr]
    unfold logOne
    unfold single at e1 ⊢
    rw [List.filter_append, List.filter_append, e1]
  rw [e]

/-- So what the arm promises is the same of the two logs. -/
theorem linkHolds_logOne (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (g : Fam (rom lam)) (o : OutLA lam L aL × Trace (rom lam))
    (hans : ∀ e ∈ o.2, e.2.2 = g e.1 e.2.1) (cm cm' : Dig lam) (rec rec' : L.Rec) :
    LinkHolds W (logOne W V m (readBlocks m g) o) cm cm' rec rec' ↔
      LinkHolds W (singleTr m o.2 ++ (runA W V (readBlocks m g) o.1).2) cm cm' rec rec' := by
  unfold LinkHolds
  rw [extEnc_logOne V m hl hn g o hans cm, extEnc_logOne V m hl hn g o hans cm']

/-! ## The run of the arm with the lax Link -/

/-- The run of the arm with the lax Link is the conjunction of the three runs. -/
theorem VLA'_det (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam))
    (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (cm cm' : Dig lam) (r r' : L.Rec)
    (π : OneProtocolProof lam (batLC L aL)) :
    (VLA' W S cA cm cm' r r' π).det g =
      ((outOfDomainSeedIs W S cm r.1).det g && (outOfDomainSeedIs W S cm' r'.1).det g &&
        (vLA' W cA cm cm' r r' π).det g) := by
  unfold VLA'
  simp only [OComp.det_bind]
  rfl

/-! ## The other half of the lift; the words stay -/

/-- For every algorithm over the typed oracles with at most n queries: its lengthened log lies in
`BadLA` with probability at most 5n εs + 2 (5n + 1)² / 2^lam. With `arm_lift` this is the whole
lift. Premises: `S.Law εs`, the bound on the rounds' errors (hbL), the laws of Link's wire
(hLk). -/
theorem badLA_len_rare {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞} (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hLk : (wLC W).OKG) {β : Type}
    (B : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (n : ℕ) (hB : B.QueryBound n) :
    Rom.Pr B.withTrace (fun f => {o | BadLA W S cA εL (lenB (preS W S) f o.2)}) ≤
      ((n * (1 + 4) : ℕ) : ℝ≥0∞) * εs + 2 * ((n * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hn : ∀ o q, (preSeeds W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preSeeds W S o q)
  have e : Rom.Pr B.withTrace (fun f => {o | BadLA W S cA εL (lenB (preS W S) f o.2)}) =
      Rom.Pr (between (preS W S) B).withTrace (fun _ => {o | BadLA W S cA εL o.2}) := by
    unfold Rom.Pr
    refine MeasureTheory.lintegral_congr fun f => ?_
    unfold PrCoins
    rw [between_law (preS W S) hn f, pr_map]
    rfl
  rw [e, Pr_eq_law]
  exact badLA_rare hSd hbL hLk _ _
    (between_bound (preS W S) 4 (fun o q => (detBound_preSeeds W S o q).queryBound) _ _ hB)

/-- The words stay, from the lengthened log: if the lengthened log of tr ++ tr' lies outside `BadLA`
(hB) and the first seed query of the root cm stands in tr (h), the word under cm is the same at tr
and at tr ++ tr'. -/
theorem linkA_fixes_len {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} (f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) {tr tr' : Tc W}
    (hB : ¬ BadLA W S cA εL (lenB (preS W S) f (tr ++ tr'))) {cm : Dig lam} {a0 : FsAns lam W.K}
    (h : fbE S.t (seedQ0 W S cm) a0 ∈ tr) : extEnc W tr cm = extEnc W (tr ++ tr') cm := by
  have h1 := linkA_fixes W S (cA := cA) (εL := εL) (tr := lenB (preS W S) f tr)
    (tr' := lenB (preS W S) f tr') (by rw [← lenB_append]; exact hB)
    (mem_lenB (preS W S) f _ _ h)
  rwa [← lenB_append, extEnc_lenB, extEnc_lenB] at h1

end TypedOracleCompiler.Compile.Batch.Cms

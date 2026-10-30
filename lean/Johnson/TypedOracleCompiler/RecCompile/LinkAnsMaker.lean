-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsMaker.lean: the entry's arm with the answers alone: what it promises,
said of the maker's log of strings alone.

In LinkAnsStay.lean the two words are read off the maker's log followed by the arm's log. Here they
are read off the maker's log alone: what the maker itself has hashed determines them. The ground:
the arm begins with the seed queries of the two roots; outside the rare event the word under a root
is fixed once the root's first seed query is asked (`Stays`); and a word does not see entries at the
Fiat-Shamir oracles.

  `pr_one_eq`         an event on the typed experiment at the maker brought down, as an event on the
                      maker's run over the hash function
  `arm_pr_stay_one`   `arm_pr_stay` over one hash function, with `Stays` said of the typed log
  `HeadSeeds`         an arm's log begins with entries at the Fiat-Shamir oracles among which is the
                      first seed query of the first root, then such entries among which is that of
                      the further root; `headSeeds_armL`, `headSeeds_armS`
  `linkHolds_maker`   on a log that stays: what the arm promises of maker's log and arm's log, it
                      promises of the maker's log
  `arm_pr_maker`      the bound: the maker runs, then the arm, both asking the one function; the arm
                      accepts, and what it promises fails on the one-block entries of the maker's
                      log of strings: with probability at most n εs + 2 (n + 1)² / 2^lam,
                      n = 5 (t + tVL)

Limits: soundness alone. This is said under the hypotheses that stand in the statement itself, which
this comment does not list; it is no claim that they hold.
  * One maker makes roots, records and proof string in one run, so its log holds all its hashes. The
    theorem does not say that the tables were already fixed when a root was first published
    (LinkAnsTwoStage.lean, LinkAnsKeyStage.lean: two stages).
  * The words are those that the maker's log determines at the end of the maker's run. That they
    stay from a root's first seed query on is `arm_pr_stay_one`, said of the typed log, which holds
    the maker's own seed queries; the one-block entries of a log of strings hold none (where K is
    not 0; a word does not see them in any case).
  * The theorem is for every coding m, and none is given here. One exists where the instances are
    countable, by choice (Johnson/Flat/EntryCoding.lean [not in this library; so here read: not
    proved in this library]); none is shown to be
    the programs'. m, the wires, the code of the answers and the arm are fixed before the function
    is drawn, `S.cfg` with them. The maker puts out typed values, not bytes.
  * Where the first table decodes to nothing, nothing is said of the further table.
  * n = 5 (t + tVL): t counts the maker's calls on strings, `tVL` the arm's typed queries.
  * The limits in the heads of LinkAnsPr.lean, LinkAnsOne.lean and LinkAnsStay.lean hold here too,
    but for four that are lifted here: the words are not read off the verifier's queries; the
    arm is an algorithm over the function; that the words stay is carried to one hash function
    (`arm_pr_stay_one`); the words are not those at the end of both logs.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsStay

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

/-! ## From the typed experiment to one hash function, for any event -/

/-- An event on the typed experiment at the maker brought down has the probability of the same event
on the maker's run over the hash function, at the arm's verdict and the typed log. -/
theorem pr_one_eq {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ z, (V z).NoCoin) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (E : Set ((OutLA lam L aL × Bool) × Tc W)) :
    Rom.Pr A.withTrace
        (fun g => {o | ((o.1, (runA W V (readBlocks m g) o.1).1),
          logOne W V m (readBlocks m g) o) ∈ E}) =
      Rom.Pr (joinedA W V (down m A)).withTrace (fun _ => E) := by
  have key : ∀ F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)),
      PrCoins (glue m F) A.withTrace
          {o | ((o.1, (runA W V (readBlocks m (glue m F)) o.1).1),
            logOne W V m (readBlocks m (glue m F)) o) ∈ E} =
        PrCoins F (joinedA W V (down m A)).withTrace E := by
    intro F
    unfold PrCoins
    rw [joinedA_down W V m hV, pr_map, readBlocks_glue]
    rfl
  unfold Rom.Pr
  rw [lintegral_glue m (fun g => PrCoins g A.withTrace
      {o | ((o.1, (runA W V (readBlocks m g) o.1).1), logOne W V m (readBlocks m g) o) ∈ E})]
  · simp only [key]
  · simp only [key]
    exact measurable_PrCoins _ _

/-- The maker, then the arm as an algorithm over the hash function: under g, the maker's run with
the arm's verdict laid beside it. -/
theorem runEager_hash {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ z, (V z).NoCoin) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (g : Fam (rom lam)) :
    (A.withTrace.bind fun o => ((V o.1).overOne m).bind fun b =>
      (OComp.pure (o, b) : OComp (rom lam) ((OutLA lam L aL × Trace (rom lam)) × Bool))).runEager g
          =
      (A.withTrace.runEager g).map fun o => (o, (runA W V (readBlocks m g) o.1).1) := by
  rw [OComp.runEager_bind, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun o => ?_)
  rw [OComp.runEager_bind, arm_overOne hV, PMF.pure_bind]
  rfl

/-- `arm_pr_stay` over one hash function: the event "the arm accepts and what it promises fails, or
the words do not stay", on the typed log of the maker and the arm, has probability at most
n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + tVL) and t bounds the maker's queries to the function
(hq); the arm is run at the typed oracle functions that m reads out of the function. The premises
are those of `arm_pr` (LinkAnsPr.lean): Link's soundness round by round (hsL), its locality (hlL),
the annotation's coherence (hcL), `OKLA W`, `AnsOK cA`, `S.Law εs`, the bound on the rounds' errors
(hbL), `IsArm`. m is any coding. -/
theorem arm_pr_stay_one {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr A.withTrace
        (fun g => {o | ((runA W V (readBlocks m g) o.1).1 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1) ∨
          ¬ Stays W S (logOne W V m (readBlocks m g) o)}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  le_trans (le_of_eq (pr_one_eq (fun z => noCoin_of_detBound (hV.det z)) m A
      {o | (o.1.2 = true ∧ ¬ LinkHolds W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1) ∨
        ¬ Stays W S o.2}))
    (arm_pr_stay hsL hlL hcL hW hA hSd hbL hV (down m A) t (queryBound_down m A t hq))

/-! ## An arm begins with the seed queries -/

/-- The log of the test of a seed: the root's two seed queries. -/
theorem log_seedIs (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (c : Dig lam) (s : L.OutOfDomainSeed) :
    ((outOfDomainSeedIs W S c s).withTrace.det G).2 =
      [fbE S.t (seedQ0 W S c) (G (OracleName.fb S.t) (seedQ0 W S c)),
        fbE S.t (seedQ1 W S (link (show FsAns lam W.K from G (OracleName.fb S.t) (seedQ0 W S c))))
          (G (OracleName.fb S.t)
            (seedQ1 W S (link (show FsAns lam W.K from G (OracleName.fb S.t) (seedQ0 W S c)))))] := rfl

/-- An arm's log begins with entries at the Fiat-Shamir oracles among which is the first seed query
of the first root, then such entries among which is that of the further root. -/
def HeadSeeds (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool) : Prop :=
  ∀ (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutLA lam L aL),
    ∃ (l0 l1 rest : Tc W) (a0 b0 : FsAns lam W.K), (runA W V G z).2 = l0 ++ (l1 ++ rest) ∧
      fbE S.t (seedQ0 W S z.1) a0 ∈ l0 ∧ fbE S.t (seedQ0 W S z.2.1) b0 ∈ l1 ∧
      (∀ e ∈ l0, notFb W e = false) ∧ ∀ e ∈ l1, notFb W e = false

/-- The two entries of the log of a seed's test are entries at a Fiat-Shamir oracle. -/
theorem notFb_log_seedIs (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (c : Dig lam) (s : L.OutOfDomainSeed) :
    ∀ e ∈ ((outOfDomainSeedIs W S c s).withTrace.det G).2, notFb W e = false := by
  intro e he
  rw [log_seedIs] at he
  rcases List.mem_cons.1 he with rfl | he
  · rfl
  · rw [List.mem_singleton.1 he]
    rfl

/-- The log of two algorithms and then a third. -/
theorem log_three {Sp : OSpec} {α β γ : Type} (G : Fam Sp) (c1 : OComp Sp α) (c2 : OComp Sp β)
    (k : α → β → OComp Sp γ) :
    ((c1.bind fun a => c2.bind fun b => k a b).withTrace.det G).2 =
      (c1.withTrace.det G).2 ++ ((c2.withTrace.det G).2 ++
        ((k (c1.withTrace.det G).1 (c2.withTrace.det G).1).withTrace.det G).2) := by
  rw [log_bind, log_bind]

/-- The arm with the lax Link begins with the seed queries. -/
theorem headSeeds_armL (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) :
    HeadSeeds W S (armL W S cA) := by
  intro G z
  have e := log_three G (outOfDomainSeedIs W S z.1 z.2.2.1.1) (outOfDomainSeedIs W S z.2.1 z.2.2.2.1.1) fun s0 s1 =>
    (vLA' W cA z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2).bind fun b => OComp.pure (s0 && s1 && b)
  exact ⟨_, _, _, G (OracleName.fb S.t) (seedQ0 W S z.1), G (OracleName.fb S.t) (seedQ0 W S z.2.1), e,
    by rw [log_seedIs]; exact List.mem_cons_self, by rw [log_seedIs]; exact List.mem_cons_self,
    notFb_log_seedIs S G _ _, notFb_log_seedIs S G _ _⟩

/-- The arm with the strict Link begins with the seed queries. -/
theorem headSeeds_armS (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params) :
    HeadSeeds W S (armS W S cA p) := by
  intro G z
  have e := log_three G (outOfDomainSeedIs W S z.1 z.2.2.1.1) (outOfDomainSeedIs W S z.2.1 z.2.2.2.1.1) fun s0 s1 =>
    (verifyLinkProof W cA p z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2).bind fun b => OComp.pure (s0 && s1 && b)
  exact ⟨_, _, _, G (OracleName.fb S.t) (seedQ0 W S z.1), G (OracleName.fb S.t) (seedQ0 W S z.2.1), e,
    by rw [log_seedIs]; exact List.mem_cons_self, by rw [log_seedIs]; exact List.mem_cons_self,
    notFb_log_seedIs S G _ _, notFb_log_seedIs S G _ _⟩

/-! ## The words are the maker's -/

/-- A word does not see entries at the Fiat-Shamir oracles that are laid behind a trace. -/
theorem extEnc_append_fb (tr l : Tc W) (hl : ∀ e ∈ l, notFb W e = false) (cm : Dig lam) :
    extEnc W (tr ++ l) cm = extEnc W tr cm := by
  have h0 : l.filter (notFb W) = [] :=
    List.filter_eq_nil_iff.2 fun e he => by rw [hl e he]; exact Bool.false_ne_true
  rw [← extEnc_filter W (tr ++ l), List.filter_append, h0, List.append_nil, extEnc_filter]

/-- On a log that stays: what the arm promises of the maker's log followed by the arm's, it promises
of the maker's log. -/
theorem linkHolds_maker {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hH : HeadSeeds W S V)
    (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutLA lam L aL) (trA : Tc W)
    (hst : Stays W S (trA ++ (runA W V G z).2))
    (h : LinkHolds W (trA ++ (runA W V G z).2) z.1 z.2.1 z.2.2.1 z.2.2.2.1) :
    LinkHolds W trA z.1 z.2.1 z.2.2.1 z.2.2.2.1 := by
  obtain ⟨l0, l1, rest, a0, b0, e, h0, h1, f0, f1⟩ := hH G z
  have e0 : extEnc W trA z.1 = extEnc W (trA ++ (runA W V G z).2) z.1 := by
    rw [← extEnc_append_fb trA l0 f0 z.1]
    exact hst (trA ++ l0) (l1 ++ rest) z.1 a0 (by rw [e, List.append_assoc])
      (List.mem_append_right _ h0)
  have e1 : extEnc W trA z.2.1 = extEnc W (trA ++ (runA W V G z).2) z.2.1 := by
    rw [← extEnc_append_fb trA (l0 ++ l1) (fun x hx => (List.mem_append.1 hx).elim (f0 x) (f1 x))
      z.2.1]
    exact hst (trA ++ (l0 ++ l1)) rest z.2.1 b0 (by rw [e]; simp only [List.append_assoc])
      (List.mem_append_right _ (List.mem_append_right _ h1))
  unfold LinkHolds at h ⊢
  rw [e0, e1]
  exact h

/-- The word under a root, read off the maker's typed log, is the word read off the one-block
entries of its log of strings. Asked: the log holds g's answers, and lam is not 0. -/
theorem extEnc_upTr (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (g : Fam (rom lam)) (tr : Trace (rom lam)) (hans : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1)
    (cm : Dig lam) :
    extEnc W (upTr m (readBlocks m g) tr) cm = extEnc W (singleTr m tr) cm := by
  rw [← extEnc_single W m (blocks_leaf hlam m) (blocks_node hlam m) (upTr m (readBlocks m g) tr),
    ← extEnc_single W m (blocks_leaf hlam m) (blocks_node hlam m) (singleTr m tr),
    single_upTr, glue_readBlocks, retr_of_ans g tr hans, single_singleTr]

/-- An arm that begins with the seed queries is sound against every maker over one hash function,
the words being those that the maker's own log of strings determines: the maker runs, then the arm,
both asking the one function; the arm accepts, and what it promises fails on the one-block entries
of the maker's log of strings, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 5 (t + tVL) and t bounds the maker's queries. The premises are those of `arm_pr`
(LinkAnsPr.lean): Link's soundness round by round (hsL), its locality (hlL), the annotation's
coherence (hcL), `OKLA W`, `AnsOK cA`, `S.Law εs`, the bound on the rounds' errors (hbL), `IsArm`;
and the arm begins with the seed queries (`HeadSeeds`), and lam is not 0. m is any coding. -/
theorem arm_pr_maker {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (hH : HeadSeeds W S V) (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr (A.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧
          ¬ LinkHolds W (singleTr m x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine le_trans ?_ (arm_pr_stay_one hsL hlL hcL hW hA hSd hbL hV m A t hq)
  refine MeasureTheory.lintegral_mono fun g => ?_
  unfold PrCoins
  rw [runEager_hash (fun z => noCoin_of_detBound (hV.det z)) m A g, pr_map]
  refine pr_mono_support _ _ _ fun o ho hE => ?_
  obtain ⟨hacc, hbad⟩ := hE
  have hacc' : (runA W V (readBlocks m g) o.1).1 = true := hacc
  by_contra hno
  have hno' : ¬ (((runA W V (readBlocks m g) o.1).1 = true ∧
      ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1) ∨
      ¬ Stays W S (logOne W V m (readBlocks m g) o)) := hno
  have hst : Stays W S (logOne W V m (readBlocks m g) o) := by
    by_contra h
    exact hno' (Or.inr h)
  have hlh : LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1
      o.1.2.2.2.1 := by
    by_contra h
    exact hno' (Or.inl ⟨hacc', h⟩)
  have h1 := linkHolds_maker hH (readBlocks m g) o.1 (upTr m (readBlocks m g) o.2) hst hlh
  refine hbad ?_
  have hans := support_withTrace_ans g A o ho
  show LinkHolds W (singleTr m o.2) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1
  unfold LinkHolds at h1 ⊢
  rw [← extEnc_upTr hlam m g o.2 hans, ← extEnc_upTr hlam m g o.2 hans]
  exact h1

end TypedOracleCompiler.Compile.Batch.Cms

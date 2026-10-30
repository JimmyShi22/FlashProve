-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/KeyAnsPr.lean: the key's arm is sound against every maker over the typed
oracles: the like of LinkAnsPr.lean for Test and one root.

KeyAns.lean's theorem is on traces that have an order (before each first query of a chain of Test
stand the seed queries of its root) and hold the answers of one family of oracle functions. A
cheating prover need not ask in that order. Here both conditions are lifted, for every algorithm, at
a price on the number of queries: in the analysis alone, the two seed queries of the root are laid
before each first query of a chain of Test. So each query is charged three times: itself, and these
two.

Main names:
  `preTest`, `preSeedsT`, `preST`: what the analysis lays before a query.
  `seedsFirstT_of_asksFirst`: a trace so lengthened has the order.
  `extEnc_lenBT`: the word under a root does not see the entries laid in.
  `testA_fixes`: outside `BadTA` the word under a root is fixed once the first query of the root's
    seed is asked.
  `IsArmT`, `armTS`, `armTL`, `isArmT_armTS`, `isArmT_armTL`: an arm; the arm with the strict and
    with the lax Test.
  `joinedT`: the maker, then an arm on what the maker has put out.
  `armT_lift`: the lift on one log: outside `BadTA` of the lengthened log a yes of the arm holds
    what it promises of the log itself.
  `armT_pr`: an arm accepts, and what it promises fails on the trace of the maker and the arm, with
    probability at most n εs + 2 (n + 1)² / 2^lam, n = 3 (t + tVT).

The proofs are those of LinkAnsPr.lean, whose tools on logs and on the seed queries are used as they
are.

Limits: soundness alone; typed oracles, drawn independently; the words are those at the end of the
whole trace, the arm's queries included (KeyAnsStage.lean: the committer's). Test's soundness round
by round is a premise. The maker puts out typed values, not bytes. No yes is shown: the bound would
hold of an arm that refuses everything.
  * The premises that `armT_pr`'s docstring names are laws of letters here. Nothing in this folder
    pays them at the key file's protocol or at a written wiring: not Test's soundness round by
    round, not `OKTA W` (among its laws: K uniform digests give an exactly uniform verifier
    message), not `AnsOK cA`, not `S.Law εs`. Wire.lean makes a wire with the whole verifier's laws
    (`OKC`) at a passed object with local rounds alone, given a lawful code of whole records
    (`S.OK`); no lemma carries that to `OKTA`. That they can be met together is not shown; until it
    is, the theorem may be true and empty.
  * No wire is made at an annotation with shared rounds. If Test has shared rounds, the joining
    query (F4) repeats the whole list, answers included.
  * W, S, cA and the arm are fixed before the oracles are drawn, `S.cfg` with them.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.KeyAns
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPr

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-! ## What is asked before a query -/

/-- before a first query of a chain of Test: the seed queries of the first entry of its list -/
def preTest (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.test) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  if q.round = 0 then
    match q.head with
    | .f1 cms _ _ => askSeeds W S (cms.take 1)
    | _ => OComp.pure ()
  else OComp.pure ()

/-- what the analysis lays before a query -/
def preSeedsT : (o : OracleName) → domOf lam (typedOracleCarrier L Bd aT aL) o → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit
  | OracleName.fb Tag.test, q => preTest W S q
  | _, _ => OComp.pure ()

/-- the same, at the types of the oracles' specification -/
abbrev preST : (o : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).ι) →
    (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o → OComp (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) Unit :=
  preSeedsT W S

/-- It draws no coin and asks at most two queries. -/
theorem detBound_preTest (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.test) :
    DetBound (preTest W S q) 2 := by
  unfold preTest
  split
  · split
    · rename_i cms _ _ _
      exact (detBound_askSeeds W S _).mono (by
        have := List.length_take_le 1 cms
        omega)
    · exact detBound_pure _ _
  · exact detBound_pure _ _

/-- It draws no coin and asks at most two queries. -/
theorem detBound_preSeedsT (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    DetBound (preSeedsT W S o q) 2 := by
  cases o with
  | fb t => cases t <;> first | exact detBound_preTest W S q | exact detBound_pure _ _
  | _ => exact detBound_pure _ _

variable (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- Before a query of a round other than 0 nothing is laid. -/
theorem preSeedsT_round {t : Tag} (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) (h : q.round ≠ 0) :
    preSeedsT W S (OracleName.fb t) q = OComp.pure () := by
  cases t
  · show preTest W S q = _
    unfold preTest
    rw [if_neg h]
  · rfl
  · rfl

/-- What is laid in are queries at the seeds' oracle, in rounds other than 0. -/
theorem round_preSeedsT (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ∀ x ∈ ((preSeedsT W S o q).withTrace.det g).2,
      ∃ (q' : FbIn lam (typedOracleCarrier L Bd aT aL) S.t) (a : FsAns lam W.K),
        x = fbE S.t q' a ∧ q'.round ≠ 0 := by
  intro x hx
  cases o with
  | fb t =>
    cases t with
    | test =>
      have hx' : x ∈ ((preTest W S q).withTrace.det g).2 := hx
      unfold preTest at hx'
      split at hx'
      · split at hx'
        · exact round_log W S g _ x hx'
        · exact absurd hx' List.not_mem_nil
      · exact absurd hx' List.not_mem_nil
    | _ => exact absurd hx List.not_mem_nil
  | _ => exact absurd hx List.not_mem_nil

/-- Before what is laid in nothing is laid. -/
theorem idle_preSeedsT (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ∀ x ∈ ((preSeedsT W S o q).withTrace.det g).2,
      ((preSeedsT W S x.1 x.2.1).withTrace.det g).2 = [] := by
  intro x hx
  obtain ⟨q', a, rfl, hr⟩ := round_preSeedsT W S g o q x hx
  show ((preSeedsT W S (OracleName.fb S.t) q').withTrace.det g).2 = []
  rw [preSeedsT_round W S q' hr]
  rfl

/-- A trace so lengthened has the order. -/
theorem seedsFirstT_of_asksFirst (σ : Tc W) (h : AsksFirst (preST W S) g σ) :
    SeedsFirstT W S σ := by
  intro pre q a post cms x salt htr hr hq c hc
  have hb := asksFirst_before (preST W S) g σ h (idle_preSeedsT W S g) pre (fbE Tag.test q a) post
    htr
  have e : preSeedsT W S (OracleName.fb Tag.test) q = askSeeds W S (cms.take 1) := by
    show preTest W S q = _
    unfold preTest
    rw [if_pos hr, hq]
  have hb' : ∀ x ∈ ((askSeeds W S (cms.take 1)).withTrace.det g).2, x ∈ pre := by
    rw [← e]
    exact hb
  exact (seedAsked_log W S g _ c hc).mono hb'

/-! ## The word under a root does not see the entries laid in -/

/-- The entries at other than the Fiat-Shamir oracles are those of the trace itself. -/
theorem filter_lenBT : ∀ σ : Tc W,
    (lenB (preST W S) g σ).filter (notFb W) = σ.filter (notFb W)
  | [] => rfl
  | e :: σ => by
    show (((preSeedsT W S e.1 e.2.1).withTrace.det g).2 ++ e :: lenB (preST W S) g σ).filter
      (notFb W) = _
    have h0 : (((preSeedsT W S e.1 e.2.1).withTrace.det g).2).filter (notFb W) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨q', a, rfl, -⟩ := round_preSeedsT W S g e.1 e.2.1 x hx
      simp [notFb, fbE]
    rw [List.filter_append, h0, List.nil_append, List.filter_cons, List.filter_cons,
      filter_lenBT σ]

/-- So the word under a root does not see the entries laid in. -/
theorem extEnc_lenBT (σ : Tc W) (cm : Dig lam) :
    extEnc W (lenB (preST W S) g σ) cm = extEnc W σ cm := by
  rw [← extEnc_filter W (lenB (preST W S) g σ), filter_lenBT, extEnc_filter]

/-! ## The word stays -/

/-- Outside the set `BadTA` the word under a root is fixed once the first query of the root's seed
is asked. No other premise. -/
theorem testA_fixes {cA : L.OutOfDomainAnswer → List (Dig lam)} {εT : Err L.offline.shape} {tr tr' : Tc W}
    (hB : ¬ BadTA W S cA εT (tr ++ tr')) {cm : Dig lam} {a0 : FsAns lam W.K}
    (h : fbE S.t (seedQ0 W S cm) a0 ∈ tr) : extEnc W tr cm = extEnc W (tr ++ tr') cm :=
  seed_fixes (fun hM => hB (Or.inl (Or.inl hM))) h

/-! ## The bound -/

variable (cA : L.OutOfDomainAnswer → List (Dig lam))

/-- An arm: an algorithm on what a maker puts out that draws no coin, asks at most `tVT` queries,
and whose yes holds the yes of the seed's test and of the lax Test at some proof string. -/
structure IsArmT (V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool) : Prop where
  det : ∀ z, DetBound (V z) (tVT W)
  yes : ∀ z tr, RunsIn tr (V z) true →
    RunsIn tr (outOfDomainSeedIs W S z.1 z.2.1.1) true ∧ ∃ π', RunsIn tr (vTA' W cA z.1 z.2.1 π') true

/-- the arm with the strict Test -/
def armTS (p : Params) (z : OutTA lam L aT) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  VTA W S cA p z.1 z.2.1 z.2.2

/-- the arm with the lax Test -/
def armTL (z : OutTA lam L aT) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  VTA' W S cA z.1 z.2.1 z.2.2

/-- The arm with the strict Test is an arm, if Test's wire has its laws. -/
theorem isArmT_armTS (hT : (wTC W).OKG) (p : Params) : IsArmT W S cA (armTS W S cA p) :=
  ⟨fun _ => detBound_VTA W S cA p _ _ _, fun _ _ h => yes_VTA hT p h⟩

/-- The arm with the lax Test is an arm. -/
theorem isArmT_armTL : IsArmT W S cA (armTL W S cA) :=
  ⟨fun _ => detBound_VTA' W S cA _ _ _, fun _ _ h => yes_VTA' h⟩

/-- The maker, then an arm on what the maker has put out. -/
def joinedT (V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutTA lam L aT)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutTA lam L aT × Bool) :=
  A.bind fun z => (V z).bind fun b => OComp.pure (z, b)

variable {W S cA}

/-- The maker and the arm ask at most t + tVT queries. -/
theorem joinedT_queryBound {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : IsArmT W S cA V) {A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutTA lam L aT)}
    {t : ℕ} (hA : A.QueryBound t) : (joinedT W V A).QueryBound (t + tVT W) := by
  have h : (joinedT W V A).QueryBound (t + (tVT W + 0)) := by
    unfold joinedT
    exact hA.bind fun z => (hV.det z).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- On one outcome: a trace σ with the answers of one family f, in which an arm runs and says yes,
and whose lengthened form lies outside `BadTA`: what the arm promises holds on σ. The premises are
those of `testA_key` (KeyAns.lean), and V is an arm (`IsArmT`). -/
theorem armT_lift {εT : Err L.offline.shape}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : AnsOK cA)
    {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArmT W S cA V)
    (f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) {σ : Tc W}
    (hans : ∀ e ∈ σ, e.2.2 = f e.1 e.2.1) {z : OutTA lam L aT} (hrun : RunsIn σ (V z) true)
    (hnb : ¬ BadTA W S cA εT (lenB (preST W S) f σ)) : KeyHolds W σ z.1 z.2.1 := by
  have hn : ∀ o q, (preSeedsT W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preSeedsT W S o q)
  obtain ⟨hs0, _, hb⟩ := hV.yes z _ (hrun.mono fun e he => mem_lenB (preST W S) f _ e he)
  have h := testA_sound' hsT hlT hcT hW hA (lenB_ans (preST W S) hn f _ hans)
    (seedsFirstT_of_asksFirst W S f _ ⟨_, rfl⟩) hnb hs0 hb
  unfold KeyHolds at h ⊢
  simpa only [extEnc_lenBT] using h

/-- An arm (`IsArmT`) is sound against every maker: it accepts, and what it promises fails on the
trace of the maker and the arm, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 3 (t + tVT) and t bounds the maker's queries (hq). Premises: Test is sound round by round, with
the errors εT, for the language "the record's seed is a collision seed of the word, or word and
record decode to something" (hsT); Test's verifier is local (hlT); the annotation aT is coherent
(hcT); the wires that Test reads have their laws (`OKTA W`); the code of the answers is one to one,
with one length (`AnsOK cA`; the length is not read by this arm); the seed's law at εs (`S.Law εs`);
no round's error, counted as often as the request tree has leaves where the round is shared, is
above εs (hbT). -/
theorem armT_pr {εT : Err L.offline.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArmT W S cA V)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutTA lam L aT)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr (joinedT W V A).withTrace
        (fun _ => {o | o.1.2 = true ∧ ¬ KeyHolds W o.2 o.1.1.1 o.1.1.2.1}) ≤
      (((t + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hn : ∀ o q, (preSeedsT W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preSeedsT W S o q)
  have hpt : ∀ f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)),
      PrCoins f (joinedT W V A).withTrace
          {o | o.1.2 = true ∧ ¬ KeyHolds W o.2 o.1.1.1 o.1.1.2.1} ≤
        PrCoins f (between (preST W S) (joinedT W V A)).withTrace
          {o | BadTA W S cA εT o.2} := by
    intro f
    unfold PrCoins
    rw [between_law (preST W S) hn f]
    refine pr_le_pr_map _ _ _ _ fun o ho => ?_
    rintro ⟨hacc, hbad⟩
    show BadTA W S cA εT (lenB (preST W S) f o.2)
    by_contra hnb
    -- the outcome falls into the maker's and the arm's
    obtain ⟨a, -, b, hb, rfl⟩ := support_withTrace_bind f A _ o ho
    obtain ⟨c, hc, d, hd, rfl⟩ := support_withTrace_bind f _ _ b hb
    have hd' : d = ((a.1, c.1), []) := by
      simpa [OComp.withTrace, OComp.runEager] using hd
    subst hd'
    have hc1 : c.1 = true := hacc
    have hrun : RunsIn c.2 (V a.1) true := by
      have := runsIn_of_mem_support (hV.det a.1) f c hc
      rwa [hc1] at this
    exact hbad (armT_lift hsT hlT hcT hW hA hV f (support_withTrace_ans f _ _ ho)
      (hrun.mono fun e he => List.mem_append_right _ (List.mem_append_left _ he)) hnb)
  calc
    Rom.Pr (joinedT W V A).withTrace
          (fun _ => {o | o.1.2 = true ∧ ¬ KeyHolds W o.2 o.1.1.1 o.1.1.2.1}) ≤
        Rom.Pr (between (preST W S) (joinedT W V A)).withTrace
          (fun _ => {o | BadTA W S cA εT o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (between (preST W S) (joinedT W V A)).withTrace.law
          {o | BadTA W S cA εT o.2} := Pr_eq_law _ _
    _ ≤ _ := badTA_rare hSd hbT hW.T _ _
        (between_bound (preST W S) 2 (fun o q => (detBound_preSeedsT W S o q).queryBound) _ _
          (joinedT_queryBound hV hq))

end TypedOracleCompiler.Compile.Batch.Cms

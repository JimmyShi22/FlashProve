-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/ProofAnsPr.lean: the proof's arm (ProofAns.lean) is sound against every maker
over the typed oracles.

As LinkAnsPr.lean for the entry's arm and KeyAnsPr.lean for the key's: in the analysis alone the two
seed queries of the first entry of its list are laid before each first query of a chain of the
session, so that every trace has the order that soundness on a trace asks; a word does not see the
entries laid in.

  `preSess`, `preSeedsB`   what the analysis lays before a query
  `seedsFirstB_of_asksFirst`, `extEnc_lenBB`   a trace so lengthened has the order; the word under a
                    root does not see what is laid in
  `sessA_fixes`     outside `BadBA` the word under a root is fixed once the root's first seed query
                    is asked
  `IsArmB`, `armBS`, `armBL`, `isArmB_armBS`, `isArmB_armBL`, `joinedB`   an arm; the arm with the
                    strict and with the lax session; they are arms; the maker, then an arm
  `badBA_len_rare`  an algorithm's lengthened log lies in `BadBA` with small probability
  `armB_lift`       the lift on one log: outside `BadBA` of the lengthened log a yes of the arm
                    holds what it promises of the log itself
  `armB_pr`         the bound: n εs + 2 (n + 1)² / 2^lam, n = 3 (t + tVB)

The session's soundness is a hypothesis (hsB): the fifth clause of `HolographicProtocol.SoundAtR`
(Hiop/RecInterface.lean).

Limits: those in the head of ProofAns.lean; typed oracles (no step to one hash function here). The
word is the one that the whole trace determines, the arm's queries included.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.ProofAns
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
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-! ## What is asked before a query -/

/-- before a first query of a chain of the session: the seed queries of the first entry of its list
-/
def preSess (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.onl) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  if q.round = 0 then
    match q.head with
    | .f1 cms _ _ => askSeeds W S (cms.take 1)
    | _ => OComp.pure ()
  else OComp.pure ()

/-- what the analysis lays before a query -/
def preSeedsB : (o : OracleName) → domOf lam (typedOracleCarrier L Bd aT aL) o → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit
  | OracleName.fb Tag.onl, q => preSess W S q
  | _, _ => OComp.pure ()

/-- the same, at the types of the oracles' specification -/
abbrev preSB : (o : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).ι) →
    (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o → OComp (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) Unit :=
  preSeedsB W S

/-- It draws no coin and asks at most two queries. -/
theorem detBound_preSess (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.onl) :
    DetBound (preSess W S q) 2 := by
  unfold preSess
  split
  · split
    · rename_i cms _ _ _
      exact (detBound_askSeeds W S _).mono (by
        have := List.length_take_le 1 cms
        omega)
    · exact detBound_pure _ _
  · exact detBound_pure _ _

/-- It draws no coin and asks at most two queries. -/
theorem detBound_preSeedsB (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    DetBound (preSeedsB W S o q) 2 := by
  cases o with
  | fb t => cases t <;> first | exact detBound_preSess W S q | exact detBound_pure _ _
  | _ => exact detBound_pure _ _

variable (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- Before a query of a round other than 0 nothing is laid. -/
theorem preSeedsB_round {t : Tag} (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) (h : q.round ≠ 0) :
    preSeedsB W S (OracleName.fb t) q = OComp.pure () := by
  cases t
  · rfl
  · rfl
  · show preSess W S q = _
    unfold preSess
    rw [if_neg h]

/-- What is laid in are queries at the seeds' oracle, in rounds other than 0. -/
theorem round_preSeedsB (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ∀ x ∈ ((preSeedsB W S o q).withTrace.det g).2,
      ∃ (q' : FbIn lam (typedOracleCarrier L Bd aT aL) S.t) (a : FsAns lam W.K),
        x = fbE S.t q' a ∧ q'.round ≠ 0 := by
  intro x hx
  cases o with
  | fb t =>
    cases t with
    | onl =>
      have hx' : x ∈ ((preSess W S q).withTrace.det g).2 := hx
      unfold preSess at hx'
      split at hx'
      · split at hx'
        · exact round_log W S g _ x hx'
        · exact absurd hx' List.not_mem_nil
      · exact absurd hx' List.not_mem_nil
    | _ => exact absurd hx List.not_mem_nil
  | _ => exact absurd hx List.not_mem_nil

/-- Before what is laid in nothing is laid. -/
theorem idle_preSeedsB (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ∀ x ∈ ((preSeedsB W S o q).withTrace.det g).2,
      ((preSeedsB W S x.1 x.2.1).withTrace.det g).2 = [] := by
  intro x hx
  obtain ⟨q', a, rfl, hr⟩ := round_preSeedsB W S g o q x hx
  show ((preSeedsB W S (OracleName.fb S.t) q').withTrace.det g).2 = []
  rw [preSeedsB_round W S q' hr]
  rfl

/-- A trace so lengthened has the order. -/
theorem seedsFirstB_of_asksFirst (σ : Tc W) (h : AsksFirst (preSB W S) g σ) :
    SeedsFirstB W S σ := by
  intro pre q a post cms x salt htr hr hq c hc
  have hb := asksFirst_before (preSB W S) g σ h (idle_preSeedsB W S g) pre (fbE Tag.onl q a) post
    htr
  have e : preSeedsB W S (OracleName.fb Tag.onl) q = askSeeds W S (cms.take 1) := by
    show preSess W S q = _
    unfold preSess
    rw [if_pos hr, hq]
  have hb' : ∀ x ∈ ((askSeeds W S (cms.take 1)).withTrace.det g).2, x ∈ pre := by
    rw [← e]
    exact hb
  exact (seedAsked_log W S g _ c hc).mono hb'

/-! ## The word under a root does not see the entries laid in -/

/-- The entries at other than the Fiat-Shamir oracles are those of the trace itself. -/
theorem filter_lenBB : ∀ σ : Tc W,
    (lenB (preSB W S) g σ).filter (notFb W) = σ.filter (notFb W)
  | [] => rfl
  | e :: σ => by
    show (((preSeedsB W S e.1 e.2.1).withTrace.det g).2 ++ e :: lenB (preSB W S) g σ).filter
      (notFb W) = _
    have h0 : (((preSeedsB W S e.1 e.2.1).withTrace.det g).2).filter (notFb W) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨q', a, rfl, -⟩ := round_preSeedsB W S g e.1 e.2.1 x hx
      simp [notFb, fbE]
    rw [List.filter_append, h0, List.nil_append, List.filter_cons, List.filter_cons,
      filter_lenBB σ]

/-- So the word under a root does not see the entries laid in. -/
theorem extEnc_lenBB (σ : Tc W) (cm : Dig lam) :
    extEnc W (lenB (preSB W S) g σ) cm = extEnc W σ cm := by
  rw [← extEnc_filter W (lenB (preSB W S) g σ), filter_lenBB, extEnc_filter]

/-! ## The word stays -/

/-- Outside the set `BadBA` the word under a root is fixed once the first query of the root's seed
is asked. No other premise. -/
theorem sessA_fixes {cA : L.OutOfDomainAnswer → List (Dig lam)} {εB : Err L.onlineBatch.loc.shape}
    {State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool} {tr tr' : Tc W}
    (hB : ¬ BadBA W S cA εB State (tr ++ tr')) {cm : Dig lam} {a0 : FsAns lam W.K}
    (h : fbE S.t (seedQ0 W S cm) a0 ∈ tr) : extEnc W tr cm = extEnc W (tr ++ tr') cm :=
  seed_fixes (fun hM => hB (Or.inl (Or.inl hM))) h

/-! ## The bound -/

variable (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

/-- An arm: an algorithm on what a maker puts out that draws no coin, asks at most `tVB` queries,
and whose yes holds the yes of the seed's test and of the lax session at some proof string. -/
structure IsArmB (V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool) : Prop where
  det : ∀ z, DetBound (V z) (tVB W)
  yes : ∀ z tr, RunsIn tr (V z) true →
    RunsIn tr (outOfDomainSeedIs W S z.1 z.2.2.1.1) true ∧
      ∃ π', RunsIn tr (vBA' W cA r₀ z.1 z.2.1 z.2.2.1 π') true

/-- the arm with the strict session -/
def armBS (p : Params) (z : OutBA lam L) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  VBA W S cA r₀ p z.1 z.2.1 z.2.2.1 z.2.2.2

/-- the arm with the lax session -/
def armBL (z : OutBA lam L) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  VBA' W S cA r₀ z.1 z.2.1 z.2.2.1 z.2.2.2

/-- The arm with the strict session is an arm, if the session's wire has its laws. -/
theorem isArmB_armBS (hB : (wBC W).OKG) (p : Params) : IsArmB W S cA r₀ (armBS W S cA r₀ p) :=
  ⟨fun _ => detBound_VBA W S cA r₀ p _ _ _ _, fun _ _ h => yes_VBA hB p h⟩

/-- The arm with the lax session is an arm. -/
theorem isArmB_armBL : IsArmB W S cA r₀ (armBL W S cA r₀) :=
  ⟨fun _ => detBound_VBA' W S cA r₀ _ _ _ _, fun _ _ h => yes_VBA' h⟩

/-- The maker, then an arm on what the maker has put out. -/
def joinedB (V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutBA lam L)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutBA lam L × Bool) :=
  A.bind fun z => (V z).bind fun b => OComp.pure (z, b)

variable {W S cA r₀}

/-- The maker and the arm ask at most t + tVB queries. -/
theorem joinedB_queryBound {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : IsArmB W S cA r₀ V) {A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutBA lam L)}
    {t : ℕ} (hA : A.QueryBound t) : (joinedB W V A).QueryBound (t + tVB W) := by
  have h : (joinedB W V A).QueryBound (t + (tVB W + 0)) := by
    unfold joinedB
    exact hA.bind fun z => (hV.det z).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- On one outcome: a trace σ with the answers of one family f, in which an arm runs and says yes,
and whose lengthened form lies outside `BadBA`: what the arm promises holds on σ. Premise: the
session's clause at the states (`SessAt`, ProofAns.lean). -/
theorem armB_lift {Rt : I → X → Prop} {εB : Err L.onlineBatch.loc.shape}
    {State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool} (hSt : SessAt W S cA r₀
                                          Rt εB State)
    {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArmB W S cA r₀ V)
    (f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) {σ : Tc W}
    (hans : ∀ e ∈ σ, e.2.2 = f e.1 e.2.1) {z : OutBA lam L} (hrun : RunsIn σ (V z) true)
    (hnb : ¬ BadBA W S cA εB State (lenB (preSB W S) f σ)) :
    ProofHolds W Rt σ z.1 z.2.1 z.2.2.1 := by
  have hn : ∀ o q, (preSeedsB W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preSeedsB W S o q)
  obtain ⟨hs0, _, hb⟩ := hV.yes z _ (hrun.mono fun e he => mem_lenB (preSB W S) f _ e he)
  have h := sessA_sound' hSt (lenB_ans (preSB W S) hn f _ hans)
    (seedsFirstB_of_asksFirst W S f _ ⟨_, rfl⟩) hnb hs0 hb
  unfold ProofHolds at h ⊢
  simpa only [extEnc_lenBB] using h

/-- For every algorithm with at most n queries: its lengthened log lies in `BadBA` with probability
at most 3n εs + 2 (3n + 1)² / 2^lam. Premises: the seed's law, the bound on the rounds' errors, the
law of the session's lane, the number of slots. -/
theorem badBA_len_rare {εB : Err L.onlineBatch.loc.shape} {State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr
            L.onlineBatch.loc.shape → Bool} {εs : ℝ≥0∞}
    (hSd : S.Law εs) (hbB : Err.Below εB εs) (oB : (laneBA W S cA εB State).OK L.maxBatchSize)
    (hN : L.maxBatchSize = 2 ^ W.depthReq) {β : Type} (B : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (n : ℕ)
    (hB : B.QueryBound n) :
    Rom.Pr B.withTrace (fun f => {o | BadBA W S cA εB State (lenB (preSB W S) f o.2)}) ≤
      ((n * (1 + 2) : ℕ) : ℝ≥0∞) * εs + 2 * ((n * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hn : ∀ o q, (preSeedsB W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preSeedsB W S o q)
  have hpt : ∀ f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)),
      PrCoins f B.withTrace {o | BadBA W S cA εB State (lenB (preSB W S) f o.2)} ≤
        PrCoins f (between (preSB W S) B).withTrace {o | BadBA W S cA εB State o.2} := by
    intro f
    unfold PrCoins
    rw [between_law (preSB W S) hn f]
    exact pr_le_pr_map _ _ _ _ fun o _ h => h
  calc
    Rom.Pr B.withTrace (fun f => {o | BadBA W S cA εB State (lenB (preSB W S) f o.2)}) ≤
        Rom.Pr (between (preSB W S) B).withTrace (fun _ => {o | BadBA W S cA εB State o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (between (preSB W S) B).withTrace.law {o | BadBA W S cA εB State o.2} :=
      Pr_eq_law _ _
    _ ≤ _ := badBA_rare hSd hbB oB hN _ _
        (between_bound (preSB W S) 2 (fun o q => (detBound_preSeedsB W S o q).queryBound) _ _ hB)

/-- An arm (`IsArmB`) is sound against every maker over the typed oracles: it accepts, and what it
promises (at the relation "some w has Rno i x w"; no extractor is stated) fails on the trace of the
maker and the arm, with probability at most n εs + 2 (n + 1)² / 2^lam, where n = 3 (t + tVB) and t
bounds the maker's queries (hq). Premises: the session is sound round by round with a witness, with
the errors εB, at the batch's number of slots, at every record (hsB: the fifth clause of
`HolographicProtocol.SoundAtR`); its verifier is local (hlB); its annotation is coherent (hco); the wires that the
session reads have their laws (`OKBA W`); the code of the answers is one to one, with one length
(`AnsOK cA`); the seed's law at εs (`S.Law εs`); no round's error is above εs (hbB). -/
theorem armB_pr {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : AnsOK cA)
    (hSd : S.Law εs) (hbB : Err.Below εB εs)
    {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArmB W S cA r₀ V)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutBA lam L)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr (joinedB W V A).withTrace
        (fun _ => {o | o.1.2 = true ∧
          ¬ ProofHolds W (fun i x => ∃ w, Rno i x w) o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1}) ≤
      (((t + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  obtain ⟨State, hSt⟩ := sessA_key (S := S) (r₀ := r₀) Rno wit hsB hlB hco hW hA
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_)
    (badBA_len_rare hSd hbB hSt.1 hW.slots (joinedB W V A) _ (joinedB_queryBound hV hq))
  unfold PrCoins
  refine pr_mono_support _ _ _ fun o ho => ?_
  rintro ⟨hacc, hbad⟩
  show BadBA W S cA εB State (lenB (preSB W S) f o.2)
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
  exact hbad (armB_lift hSt hV f (support_withTrace_ans f _ _ ho)
    (hrun.mono fun e he => List.mem_append_right _ (List.mem_append_left _ he)) hnb)

end TypedOracleCompiler.Compile.Batch.Cms

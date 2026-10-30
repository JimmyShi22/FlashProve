-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/ProofAnsStage.lean: the proof's arm (ProofAns.lean, ProofAnsPr.lean) is sound
against every maker over one hash function, the arm itself asking that function, and the word under
the root being the one that the maker's own log of strings determines.

As LinkAnsMaker.lean for the entry's arm. The maker runs over the hash function and puts out a root,
an instance, a record and the session's proof string; then the arm runs, through a coding m of its
typed queries. The arm begins with the seed queries of the root; outside the rare event the word
under a root is fixed once the root's first seed query is asked; a word does not see entries at the
Fiat-Shamir oracles. So the word is read off the maker's log alone.

  `runB`            the run of an arm at typed oracle functions: its verdict and its log
  `armB_overOne`    over the hash function the arm has the verdict of that run
  `HeadSeedB`, `headSeedB_armBL`, `headSeedB_armBS`   an arm's log begins with the root's seed
                    queries
  `joinedB1`, `expB`   the typed algorithm of the analysis; the experiment over one hash function
  `oneB_lift`       the lift on one outcome: outside `BadBA` of the lengthened log a yes of the arm
                    holds what it promises of the word that the maker's typed log determines
  `armB_pr_maker`   the bound: n εs + 2 (n + 1)² / 2^lam, n = 3 (t + tVB)

The session's soundness is a hypothesis (hsB): the fifth clause of `HolographicProtocol.SoundAtR`
(Hiop/RecInterface.lean).

Limits: soundness alone.
  * One maker makes root, instance, record and proof string in one run, so its log holds all its
    hashes. The word is the one that the log determines at the end of the maker's run.
  * The way out: "word and record decode to nothing" (ProofAns.lean: `holds_three` closes it, given
    what the key's and the entry's arm promise of the same words).
  * The theorem is for every coding m, a one-to-one map of the typed points onto all bit strings,
    and none is given here; none is shown to be the programs'. m, the wires, the code of the
    answers, the fixed record r₀ and the arm are fixed before the function is drawn, `S.cfg` with
    them. The maker puts out typed values, not bytes.
  * n = 3 (t + tVB): t counts the maker's calls on strings, `tVB` the arm's typed queries.
  * Not here: a form in two stages, in which the word is read off a log that ends before the
    session. ThreeArms.lean joins the three arms in one experiment, at codings that agree on the
    leaf and node oracles (WordCodings.lean); there committer and prover together are the maker of
    this file.
  * The other limits in the head of ProofAns.lean hold.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.ProofAnsPr
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsTwoStage

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

/-! ## The run of an arm -/

/-- The run of an arm at typed oracle functions: its verdict and its log. -/
def runB (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutBA lam L) : Bool × Tc W :=
  (V z).withTrace.det G

/-- An arm over the hash function has, at every function, the verdict of its run at the typed oracle
functions read out of that function. -/
theorem armB_overOne {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ z, (V z).NoCoin) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (g : Fam (rom lam)) (z : OutBA lam L) :
    ((V z).overOne m).runEager g = PMF.pure (runB W V (readBlocks m g) z).1 := by
  rw [runEager_overOne, runEager_noCoin _ _ (hV z)]
  rfl

/-- The log of an arm, run at F, holds F's answers. -/
theorem ans_runB {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ z, (V z).NoCoin) (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutBA lam L) :
    ∀ e ∈ (runB W V F z).2, e.2.2 = F e.1 e.2.1 := by
  refine support_withTrace_ans F (V z) (runB W V F z) ?_
  rw [runEager_withTrace_det F _ (hV z), PMF.support_pure]
  rfl

/-- A yes of the run at F is a run in its log. -/
theorem runsIn_runB {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} {n : ℕ}
    (hV : ∀ z, DetBound (V z) n) (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (z : OutBA lam L) (h : (runB W V F z).1 = true) : RunsIn (runB W V F z).2 (V z) true := by
  have h1 := runsIn_of_mem_support (hV z) F (runB W V F z) (by
    rw [runEager_withTrace_det F _ (noCoin_of_detBound (hV z)), PMF.support_pure]
    rfl)
  rwa [h] at h1

/-- An arm's log begins with entries at the Fiat-Shamir oracles among which is the first seed query
of the root. -/
def HeadSeedB (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool) : Prop :=
  ∀ (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutBA lam L),
    ∃ (l0 rest : Tc W) (a0 : FsAns lam W.K), (runB W V G z).2 = l0 ++ rest ∧
      fbE S.t (seedQ0 W S z.1) a0 ∈ l0 ∧ ∀ e ∈ l0, notFb W e = false

/-- The arm with the lax session begins with the seed queries. -/
theorem headSeedB_armBL (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam))
    (r₀ : L.Rec) : HeadSeedB W S (armBL W S cA r₀) := by
  intro G z
  have e := log_bind G (outOfDomainSeedIs W S z.1 z.2.2.1.1) fun s0 =>
    (vBA' W cA r₀ z.1 z.2.1 z.2.2.1 z.2.2.2).bind fun b => OComp.pure (s0 && b)
  exact ⟨_, _, G (OracleName.fb S.t) (seedQ0 W S z.1), e,
    by rw [log_seedIs]; exact List.mem_cons_self, notFb_log_seedIs S G _ _⟩

/-- The arm with the strict session begins with the seed queries. -/
theorem headSeedB_armBS (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam))
    (r₀ : L.Rec) (p : Params) : HeadSeedB W S (armBS W S cA r₀ p) := by
  intro G z
  have e := log_bind G (outOfDomainSeedIs W S z.1 z.2.2.1.1) fun s0 =>
    (verifyOnlineProof W cA r₀ p z.1 z.2.1 z.2.2.1 z.2.2.2).bind fun b => OComp.pure (s0 && b)
  exact ⟨_, _, G (OracleName.fb S.t) (seedQ0 W S z.1), e,
    by rw [log_seedIs]; exact List.mem_cons_self, notFb_log_seedIs S G _ _⟩

/-! ## The words stay, from the lengthened log -/

/-- If the lengthened log of tr ++ tr' lies outside `BadBA` (hB) and the first seed query of the
root cm stands in tr (h), the word under cm is the same at tr and at tr ++ tr'. -/
theorem sessA_fixes_len {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εB : Err L.onlineBatch.loc.shape} {State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape →
                Bool}
    (f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) {tr tr' : Tc W}
    (hB : ¬ BadBA W S cA εB State (lenB (preSB W S) f (tr ++ tr'))) {cm : Dig lam}
    {a0 : FsAns lam W.K} (h : fbE S.t (seedQ0 W S cm) a0 ∈ tr) :
    extEnc W tr cm = extEnc W (tr ++ tr') cm := by
  have h1 := sessA_fixes W S (cA := cA) (εB := εB) (State := State)
    (tr := lenB (preSB W S) f tr) (tr' := lenB (preSB W S) f tr')
    (by rw [← lenB_append]; exact hB) (mem_lenB (preSB W S) f _ _ h)
  rwa [← lenB_append, extEnc_lenBB, extEnc_lenBB] at h1

/-! ## The two algorithms -/

/-- The typed algorithm of the analysis: the maker, then the arm. -/
def joinedB1 (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutBA lam L)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  A.bind fun z => (V z).bind fun _ => OComp.pure ()

/-- The analysis' algorithm asks at most the maker's queries and the arm's. -/
theorem joinedB1_queryBound {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} {n : ℕ}
    (hV : ∀ z, DetBound (V z) n) {A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutBA lam L)} {t : ℕ}
    (hA : A.QueryBound t) : (joinedB1 W V A).QueryBound (t + n) := by
  have h : (joinedB1 W V A).QueryBound (t + (n + 0)) := by
    unfold joinedB1
    exact hA.bind fun z => (hV z).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- The experiment over one hash function: the maker, with its log of strings; then the arm. The
arm's calls stand in no log. -/
def expB (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Mk : OComp (rom lam) (OutBA lam L)) :
    OComp (rom lam) ((OutBA lam L × Trace (rom lam)) × Bool) :=
  Mk.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b)

/-! ## One outcome -/

/-- One outcome: outside `BadBA` of the lengthened typed log of the maker and the arm, a yes of the
arm holds what it promises of the word that the maker's typed log determines under the root.
Premises: the session's clause at some states (`SessAt`), `IsArmB`, `HeadSeedB`. -/
theorem oneB_lift {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {Rt : I → X → Prop} {εB : Err L.onlineBatch.loc.shape} {State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr
                L.onlineBatch.loc.shape → Bool}
    (hSt : SessAt W S cA r₀ Rt εB State) (hV : IsArmB W S cA r₀ V) (hH : HeadSeedB W S V)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutBA lam L) (tr : Trace (rom lam))
    (hacc : (runB W V F z).1 = true)
    (hnb : ¬ BadBA W S cA εB State (lenB (preSB W S) F (upTr m F tr ++ (runB W V F z).2))) :
    ProofHoldsAt L Rt (extEnc W (upTr m F tr) z.1) z.2.1 z.2.2.1 := by
  have hans : ∀ e ∈ upTr m F tr ++ (runB W V F z).2, e.2.2 = F e.1 e.2.1 := by
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact ans_upTr m F tr e h
    · exact ans_runB (fun z => noCoin_of_detBound (hV.det z)) F z e h
  have hrun : RunsIn (upTr m F tr ++ (runB W V F z).2) (V z) true :=
    (runsIn_runB hV.det F z hacc).mono fun e he => List.mem_append_right _ he
  have hlh := armB_lift hSt hV F hans hrun hnb
  obtain ⟨l0, rest, a0, e, h0, f0⟩ := hH F z
  have e1 : extEnc W (upTr m F tr) z.1 = extEnc W (upTr m F tr ++ (runB W V F z).2) z.1 := by
    have hsp : upTr m F tr ++ (runB W V F z).2 = (upTr m F tr ++ l0) ++ rest := by
      rw [e, List.append_assoc]
    have h2 := sessA_fixes_len (S := S) (cA := cA) (εB := εB) (State := State) F
      (tr := upTr m F tr ++ l0) (tr' := rest) (by rw [← hsp]; exact hnb) (cm := z.1) (a0 := a0)
      (List.mem_append_right _ h0)
    rw [← hsp] at h2
    rw [← h2, extEnc_append_fb _ _ f0]
  unfold ProofHolds at hlh
  rw [e1]
  exact hlh

/-! ## The bound -/

/-- An arm (`IsArmB`) that begins with the seed queries (`HeadSeedB`) is sound against every maker
over one hash function, the arm itself asking that function: the maker runs, then the arm; the arm
accepts, and what it promises (at the relation "some w has Rno i x w"; no extractor is stated) fails
of the word that the one-block entries of the maker's log of strings determine under the root, with
probability at most n εs + 2 (n + 1)² / 2^lam, where n = 3 (t + tVB) and t bounds the maker's calls
(hq). The other premises are those of `armB_pr` (ProofAnsPr.lean): the session's soundness with a
witness at the batch's number of slots (hsB), its locality (hlB), its annotation's coherence (hco),
`OKBA W`, `AnsOK cA`, `S.Law εs`, the bound on the rounds' errors (hbB); and lam is not 0. m is any
coding. -/
theorem armB_pr_maker {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : AnsOK cA)
    (hSd : S.Law εs) (hbB : Err.Below εB εs)
    {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArmB W S cA r₀ V)
    (hH : HeadSeedB W S V) (hlam : 0 < lam)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Mk : OComp (rom lam) (OutBA lam L))
    (t : ℕ) (hq : Mk.QueryBound t) :
    Rom.Pr (expB W V m Mk)
        (fun _ => {x | x.2 = true ∧
          ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w) (extEnc W (singleTr m x.1.2) x.1.1.1)
            x.1.1.2.1 x.1.1.2.2.1}) ≤
      (((t + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  obtain ⟨State, hSt⟩ := sessA_key (S := S) (r₀ := r₀) Rno wit hsB hlB hco hW hA
  have hnc : ∀ z, (V z).NoCoin := fun z => noCoin_of_detBound (hV.det z)
  refine le_trans ?_ (badBA_len_rare hSd hbB hSt.1 hW.slots (joinedB1 W V (down m Mk)) _
    (joinedB1_queryBound hV.det (queryBound_down m Mk t hq)))
  rw [Pr_down m]
  refine MeasureTheory.lintegral_mono fun F => ?_
  unfold PrCoins
  rw [runEager_down]
  simp only [expB, joinedB1, Rom.withTrace_bind, OComp.bind_assoc, OComp.withTrace,
    OComp.bind, OComp.runEager_bind, OComp.runEager, withTrace_down, PMF.bind_map,
    Function.comp_def]
  refine pr_bind_le_bind _ _ _ _ _ fun a ha => ?_
  rw [armB_overOne hnc, readBlocks_glue, PMF.pure_bind, runEager_withTrace_det F _ (hnc _),
    PMF.pure_bind]
  refine pr_pure_le_pure ?_
  rintro ⟨hacc, hbad⟩
  by_contra hnb
  have hnb' : ¬ BadBA W S cA εB State
      (lenB (preSB W S) F (upTr m F a.2 ++ (runB W V F a.1).2)) := by
    simpa [runB] using hnb
  have h := oneB_lift hSt hV hH m F a.1 a.2 hacc hnb'
  refine hbad ?_
  have hans := support_withTrace_ans (glue m F) Mk a ha
  have u0 := extEnc_upTr (W := W) hlam m (glue m F) a.2 hans a.1.1
  rw [readBlocks_glue] at u0
  show ProofHoldsAt L _ (extEnc W (singleTr m a.2) a.1.1) a.1.2.1 a.1.2.2.1
  rw [← u0]
  exact h

end TypedOracleCompiler.Compile.Batch.Cms

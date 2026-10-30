-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/KeyAnsStage.lean: the key's arm over one hash function, in two stages: the
committer publishes a root with its record; the prover names Test's proof string; the arm runs,
itself asking the one function. The like of LinkAnsTwoStage.lean and LinkAnsKeyStage.lean for Test
and one root.

What it says: for every coding m of the typed oracles, every committer and every prover over one
random function on bit strings: except with probability at most the bound, if the arm says yes, then
the record's seed is no collision seed of the word that the committer's own leaf and node hashes
determine under the root, and that word and the record decode to something. The event names the
committer's log of strings, its root and record, and the arm's verdict: nothing of the prover's log.

How, as in LinkAnsTwoStage.lean: in the analysis alone the root is announced behind the first stage
(one query to the typed oracle `OracleName.ann`, whose answer holds nothing). Outside the rare set the word
under an announced root stays. The experiment itself holds no announcement.

Main names:
  `runT`, `armT_overOne`, `ans_runT`, `runsIn_runT`: an arm's run under oracle functions: its
    verdict and its log; over the hash function it has that verdict; its log holds the functions'
    answers.
  `badTA_len_rare`: an algorithm's trace, lengthened as in KeyAnsPr.lean, ends in `BadTA` with
    probability at most n εs + 2 (n + 1)² / 2^lam at n = 3 times the number of its queries.
  `joinedT2`, `joinedT2_queryBound`, `logT2`: the analysis' algorithm over the typed oracles
    (committer, announcement, prover, arm); its number of queries; its log.
  `expT`: the experiment over one hash function, with the two logs of strings.
  `keyT_lift`: the lift on one outcome: outside `BadTA` of the lengthened log a yes of the arm holds
    what it promises of the word that the committer's typed log determines.
  `armT_pr_key`: the bound, at n = 3 (tC + tP + 1 + tVT).

Limits: soundness alone.
  * One random function; the arm is the idealised, typed check, asking that function through m.
  * "Publish" means: hand a typed root and a typed record to the arm. There is no commitment ID, no
    key file and no byte in it. Not here, and needed for a whole verifier: the ID's step, the proof
    file's arm, and the join of the arms.
  * The premises that `armT_pr`'s docstring names are laws of letters here. Nothing in this folder
    pays them at the key file's protocol or at a written wiring: not Test's soundness round by
    round, not `OKTA W` (among its laws: K uniform digests give an exactly uniform verifier
    message), not `AnsOK cA`, not `S.Law εs`. Wire.lean makes a wire with the whole verifier's laws
    (`OKC`) at a passed object with local rounds alone, given a lawful code of whole records
    (`S.OK`); no lemma carries that to `OKTA`. That they can be met together is not shown; until it
    is, the theorem may be true and empty.
  * No wire is made at an annotation with shared rounds. If Test has shared rounds, the joining
    query (F4) repeats the whole list, answers included.
  * The theorem is for every coding m, and none is given here. One exists, by choice, where the
    instances, the bodies of leaves and every round's plain part are countable (`some_impl`,
    Johnson/Flat/EntryCoding.lean [not in this library; so here read: not proved in this library]);
    none is shown to be the programs'. m, the
    wires, the code of the answers and the arm are fixed before the function is drawn, `S.cfg` with
    them. Committer and prover put out typed values, not bytes.
  * The theorem is general in S. A coding that is to write the seed's second query and Test's own
    query of round 2 as two strings needs them to be two typed points: where `S.t` is Test's tag and
    round 2 of Test sends no root, `S.pl1` must be no plain part of round 2.
  * Where the committer has hashed nothing at a place under its root, the word has the fixed filling
    there.
  * n counts the two stages' calls on strings, one query for the announcement, and the arm's typed
    queries, three times. The arm's calls stand in neither log.
  * No yes is shown: the bound would hold of an arm that refuses everything.
  * This is one arm: nothing is said here of an entry or a proof file, and no joining is made.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.KeyAnsPr
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

/-! ## An arm's run -/

/-- An arm's run under oracle functions: its verdict and its log. -/
def runT (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutTA lam L aT) : Bool × Tc W :=
  (V z).withTrace.det G

/-- An arm that asks the one function through m gives the verdict of its run under the oracle
functions that m reads out of that function. -/
theorem armT_overOne {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ z, (V z).NoCoin) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (g : Fam (rom lam)) (z : OutTA lam L aT) :
    ((V z).overOne m).runEager g = PMF.pure (runT W V (readBlocks m g) z).1 := by
  rw [runEager_overOne, runEager_noCoin _ _ (hV z)]
  rfl

/-- The log of an arm's run holds the oracle functions' answers. -/
theorem ans_runT {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ z, (V z).NoCoin) (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutTA lam L aT) :
    ∀ e ∈ (runT W V F z).2, e.2.2 = F e.1 e.2.1 := by
  refine support_withTrace_ans F (V z) (runT W V F z) ?_
  rw [runEager_withTrace_det F _ (hV z), PMF.support_pure]
  rfl

/-- An arm that says yes runs in its own log. -/
theorem runsIn_runT {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} {n : ℕ}
    (hV : ∀ z, DetBound (V z) n) (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (z : OutTA lam L aT) (h : (runT W V F z).1 = true) : RunsIn (runT W V F z).2 (V z) true := by
  have h1 := runsIn_of_mem_support (hV z) F (runT W V F z) (by
    rw [runEager_withTrace_det F _ (noCoin_of_detBound (hV z)), PMF.support_pure]
    rfl)
  rwa [h] at h1

/-! ## The rare set on lengthened traces -/

/-- An algorithm with at most n queries: its trace, lengthened by the seed queries that the analysis
lays in, ends in `BadTA` with probability at most 3 n εs + 2 (3 n + 1)² / 2^lam. Premises: the
seed's law at εs, the bound on the rounds' errors (hbT), the laws of Test's wire (hT). -/
theorem badTA_len_rare {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εT : Err L.offline.shape} {εs : ℝ≥0∞} (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs) (hT : (wTC W).OKG) {β : Type}
    (B : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (n : ℕ) (hB : B.QueryBound n) :
    Rom.Pr B.withTrace (fun f => {o | BadTA W S cA εT (lenB (preST W S) f o.2)}) ≤
      ((n * (1 + 2) : ℕ) : ℝ≥0∞) * εs + 2 * ((n * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hn : ∀ o q, (preSeedsT W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preSeedsT W S o q)
  have e : Rom.Pr B.withTrace (fun f => {o | BadTA W S cA εT (lenB (preST W S) f o.2)}) =
      Rom.Pr (between (preST W S) B).withTrace (fun _ => {o | BadTA W S cA εT o.2}) := by
    unfold Rom.Pr
    refine MeasureTheory.lintegral_congr fun f => ?_
    unfold PrCoins
    rw [between_law (preST W S) hn f, pr_map]
    rfl
  rw [e, Pr_eq_law]
  exact badTA_rare hSd hbT hT _ _
    (between_bound (preST W S) 2 (fun o q => (detBound_preSeedsT W S o q).queryBound) _ _ hB)

/-! ## Two stages -/

/-- The analysis' algorithm over the typed oracles: the committer; the root is announced; the
prover; the arm. -/
def joinedT2 (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool) {St : Type}
    (Ct : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) ((Dig lam × L.Rec) × St))
    (Pt : St → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OneProtocolProof lam (batTC L aT))) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  Ct.bind fun a =>
    (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.ann a.1.1).bind fun _ =>
    (Pt a.2).bind fun b => (V (a.1.1, a.1.2, b)).bind fun _ => OComp.pure ()

/-- It asks at most tC + tP + 1 + n queries. -/
theorem joinedT2_queryBound {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} {n : ℕ}
    (hV : ∀ z, DetBound (V z) n) {St : Type}
    {Ct : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) ((Dig lam × L.Rec) × St)}
    {Pt : St → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OneProtocolProof lam (batTC L aT))} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (joinedT2 W V Ct Pt).QueryBound (tC + tP + 1 + n) := by
  have h : (joinedT2 W V Ct Pt).QueryBound (tC + (1 + (tP + (n + 0)))) := by
    unfold joinedT2
    exact hC.bind fun a =>
      (detBound_ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.ann a.1.1).queryBound.bind fun _ =>
        (hP a.2).bind fun b => (hV (a.1.1, a.1.2, b)).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- The experiment over one hash function in two stages: the committer publishes the root and its
record; the prover names Test's proof string; the arm; with the two logs of strings. The arm's calls
stand in neither log. -/
def expT (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {St : Type}
    (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pt : St → OComp (rom lam) (OneProtocolProof lam (batTC L aT))) :
    OComp (rom lam) ((((Dig lam × L.Rec) × St) × Trace (rom lam)) ×
      (OneProtocolProof lam (batTC L aT) × Trace (rom lam)) × Bool) :=
  Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b =>
    ((V (a.1.1.1, a.1.1.2, b.1)).overOne m).bind fun v => OComp.pure (a, b, v)

/-- The typed log of the analysis at one outcome. -/
def logT2 (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (cm : Dig lam) (rec : L.Rec)
    (trC : Trace (rom lam)) (b : OneProtocolProof lam (batTC L aT)) (trP : Trace (rom lam)) : Tc W :=
  (upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) ++ (upTr m F trP ++ (runT W V F (cm, rec, b)).2)

/-- On one outcome: the arm says yes, and the analysis' log, lengthened, lies outside `BadTA`: what
the arm promises holds of the word that the committer's typed log determines under the root. The
premises are those of `testA_key` (KeyAns.lean), and V is an arm (`IsArmT`). -/
theorem keyT_lift {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {εT : Err L.offline.shape}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : AnsOK cA)
    (hV : IsArmT W S cA V) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (cm : Dig lam) (rec : L.Rec)
    (trC : Trace (rom lam)) (b : OneProtocolProof lam (batTC L aT)) (trP : Trace (rom lam))
    (hacc : (runT W V F (cm, rec, b)).1 = true)
    (hnb : ¬ BadTA W S cA εT (lenB (preST W S) F (logT2 W V m F cm rec trC b trP))) :
    KeyHoldsAt L (extEnc W (upTr m F trC) cm) rec := by
  have hans : ∀ e ∈ logT2 W V m F cm rec trC b trP, e.2.2 = F e.1 e.2.1 := by
    intro e he
    rcases List.mem_append.1 he with h | h
    · rcases List.mem_append.1 h with h | h
      · exact ans_upTr m F trC e h
      · rw [List.mem_singleton.1 h]
        rfl
    · rcases List.mem_append.1 h with h | h
      · exact ans_upTr m F trP e h
      · exact ans_runT (fun z => noCoin_of_detBound (hV.det z)) F (cm, rec, b) e h
  have hrun : RunsIn (logT2 W V m F cm rec trC b trP) (V (cm, rec, b)) true :=
    (runsIn_runT hV.det F (cm, rec, b) hacc).mono fun e he =>
      List.mem_append_right _ (List.mem_append_right _ he)
  have hlh : KeyHolds W (logT2 W V m F cm rec trC b trP) cm rec :=
    armT_lift hsT hlT hcT hW hA hV F hans hrun hnb
  -- the word under the announced root stays
  have e0 : extEnc W (upTr m F trC) cm = extEnc W (logT2 W V m F cm rec trC b trP) cm := by
    have hsplit := lenB_append (preST W S) F (upTr m F trC ++ [annE W cm (F OracleName.ann cm)])
      (upTr m F trP ++ (runT W V F (cm, rec, b)).2)
    have hann : Announced W
        (lenB (preST W S) F (upTr m F trC ++ [annE W cm (F OracleName.ann cm)])) cm := by
      exact mem_lenB (preST W S) F _ _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
    have hM : ¬ EM (lenB (preST W S) F (upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) ++
        lenB (preST W S) F (upTr m F trP ++ (runT W V F (cm, rec, b)).2)) := by
      rw [← hsplit]
      exact fun h => hnb (Or.inl (Or.inl h))
    have h1 := extEnc_stable (W := W) hM (List.prefix_append _ _) (occursIn_of_announced hann)
    rw [← hsplit, extEnc_lenBT, extEnc_lenBT, extEnc_ann] at h1
    exact h1
  rw [e0]
  exact hlh

/-- An arm (`IsArmT`) is sound over one hash function, in two stages: the committer runs and
publishes a root with its record; the prover runs and names Test's proof string; the arm runs,
itself asking the one function. The arm accepts, and what it promises fails of the word that the
one-block entries of the committer's own log of strings determine under the root, with probability
at most n εs + 2 (n + 1)² / 2^lam, where n = 3 (tC + tP + 1 + tVT), tC bounds the committer's calls
(hC) and tP the prover's at every state (hP). The premises are those of `armT_pr` (KeyAnsPr.lean):
Test's soundness round by round (hsT), its locality (hlT), the annotation's coherence (hcT),
`OKTA W`, `AnsOK cA`, `S.Law εs`, the bound on the rounds' errors (hbT), `IsArmT`; and lam is not 0.
m is any coding. -/
theorem armT_pr_key {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εT : Err L.offline.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs) (hV : IsArmT W S cA V)
    (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {St : Type}
    (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pt : St → OComp (rom lam) (OneProtocolProof lam (batTC L aT)))
    (tC tP : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    Rom.Pr (expT W V m Ct Pt)
        (fun _ => {x | x.2.2 = true ∧
          ¬ KeyHoldsAt L (extEnc W (singleTr m x.1.2) x.1.1.1.1) x.1.1.1.2}) ≤
      (((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hnc : ∀ z, (V z).NoCoin := fun z => noCoin_of_detBound (hV.det z)
  refine le_trans ?_ (badTA_len_rare (cA := cA) (εT := εT) hSd hbT hW.T
    (joinedT2 W V (down m Ct) fun st => down m (Pt st)) _
    (joinedT2_queryBound hV.det (queryBound_down m Ct tC hC)
      fun st => queryBound_down m (Pt st) tP (hP st)))
  rw [Pr_down m]
  refine MeasureTheory.lintegral_mono fun F => ?_
  unfold PrCoins
  rw [runEager_down]
  simp only [expT, joinedT2, Rom.withTrace_bind, OComp.bind_assoc, OComp.ask, OComp.withTrace,
    OComp.bind, OComp.runEager_bind, OComp.runEager, withTrace_down, PMF.bind_map,
    Function.comp_def]
  refine pr_bind_le_bind _ _ _ _ _ fun a ha => pr_bind_le_bind _ _ _ _ _ fun b hb => ?_
  rw [armT_overOne hnc, readBlocks_glue, PMF.pure_bind, runEager_withTrace_det F _ (hnc _),
    PMF.pure_bind]
  refine pr_pure_le_pure ?_
  rintro ⟨hacc, hbad⟩
  by_contra hnb
  have hnb' : ¬ BadTA W S cA εT
      (lenB (preST W S) F (logT2 W V m F a.1.1.1 a.1.1.2 a.2 b.1 b.2)) := by
    simpa [logT2, annE, runT] using hnb
  have h := keyT_lift hsT hlT hcT hW hA hV m F a.1.1.1 a.1.1.2 a.2 b.1 b.2 hacc hnb'
  refine hbad ?_
  have hansC := support_withTrace_ans (glue m F) Ct a ha
  have u0 := extEnc_upTr (W := W) hlam m (glue m F) a.2 hansC a.1.1.1
  rw [readBlocks_glue] at u0
  show KeyHoldsAt L (extEnc W (singleTr m a.2) a.1.1.1) a.1.1.2
  rw [← u0]
  exact h

end TypedOracleCompiler.Compile.Batch.Cms

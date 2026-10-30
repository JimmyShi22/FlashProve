-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsTwoStage.lean: the entry's arm with the answers alone, against a maker
in two stages: the word under the first root is read off the log of the first stage alone.

In LinkAnsMaker.lean one maker makes roots, records and proof string in one run, and both words are
read off its whole log. Here a committer runs first and publishes the first root; then a prover,
handed the committer's state, makes the further root, the two records and the proof string; then the
arm runs. The word under the first root is read off the committer's log of strings: what was hashed
before the root was published determines it. The word under the further root is read off both logs.

How: in the analysis alone the root is announced behind the first stage (a query to the typed oracle
`OracleName.ann`, whose answer holds nothing). Outside the rare event the word under an announced root does
not change (`extEnc_stable`). The experiment itself holds no such query.

  `LinkHoldsAt`      what the arm promises, said of two words
  `isTree`, `extEnc_tree`   a word sees entries at the leaf and node oracles alone
  `joined2`          the typed algorithm of the analysis: committer, announcement, prover, arm
  `exp2`             the experiment over one hash function: committer, prover, arm, with the two
                     logs
  `arm_pr_two`       the bound: the arm accepts, and what it promises fails of (the word that the
                     committer's log of strings determines under the first root, the word that both
                     logs determine under the further root): with probability at most
                     n εs + 2 (n + 1)² / 2^lam, n = 5 (tC + tP + 1 + tVL)

Limits: soundness alone. This is said under the hypotheses that stand in the statement itself, which
this comment does not list; it is no claim that they hold.
  * The committer publishes the first root alone. The records, the first table's among them, are the
    prover's to name. So the first table, which the decoder reads off word and record, is not fixed
    by the first stage here; it is in LinkAnsKeyStage.lean.
  * "Publish" means: hand a typed root to the arm. There is no commitment ID, no key file and no
    byte in it. Not here, and needed for a whole verifier: the ID's step, the key's arm (that the
    first table decodes) and the proof file's arm in two stages, and their join.
  * The word under the further root is read off both logs, as they stand at the end of the prover's
    run. The arm's calls stand in neither log.
  * The theorem is for every coding m, and none is given here. One exists where the instances are
    countable, by choice (Johnson/Flat/EntryCoding.lean [not in this library; so here read: not
    proved in this library]); none is shown to be
    the programs'. m, the wires, the code of the answers and the arm are fixed before the function
    is drawn, `S.cfg` with them. Committer and prover put out typed values, not bytes.
  * Where the first table decodes to nothing, nothing is said of the further table.
  * n counts the two stages' calls on strings, one query for the announcement, and the arm's typed
    queries, five times.
  * The bullets under "Limits" in the heads of LinkAnsPr.lean and LinkAnsOne.lean hold of this file
    too, but for those that begin "In this file"; for t read tC + tP + 1.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsMaker

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

/-! ## What the arm promises, of two words -/

/-- What the entry's arm promises, said of two words and two records: the first record's seed is no
collision seed of the first word; the further record's seed is none of the further word; the first
word and record decode to nothing, or the further decode to what the first decode to. -/
def LinkHoldsAt (L : HolographicProtocol I X) (y y' : Fin L.wordLength → L.Symbol) (rec rec' : L.Rec) : Prop :=
  ¬ L.hasCollisionAt y rec.1 ∧ ¬ L.hasCollisionAt y' rec'.1 ∧ (L.decodeIndex y rec = none ∨ L.decodeIndex y' rec' = L.decodeIndex y rec)

/-- `LinkHolds` on a trace is `LinkHoldsAt` at the two words that the trace determines. -/
theorem linkHolds_iff (tr : Tc W) (cm cm' : Dig lam) (rec rec' : L.Rec) :
    LinkHolds W tr cm cm' rec rec' ↔
      LinkHoldsAt L (extEnc W tr cm) (extEnc W tr cm') rec rec' := Iff.rfl

/-! ## A word sees the tree's entries alone -/

/-- is the entry a query to the leaf or to the node oracle? -/
def isTree (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (e : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) : Bool :=
  match e.1 with
  | OracleName.leaf => true
  | OracleName.node => true
  | _ => false

/-- A word sees the entries at the leaf and node oracles alone. -/
theorem extEnc_tree (tr : Tc W) (cm : Dig lam) :
    extEnc W (tr.filter (isTree W)) cm = extEnc W tr cm := by
  have h : ∀ d c j, extLeaf (tr.filter (isTree W)) d c j = extLeaf tr d c j := by
    intro d c j
    unfold extLeaf
    refine Local.preimage_filter (pairM lam W.K (typedOracleCarrier L Bd aT aL)) _ ?_ ?_ tr _ c
    · rintro ⟨o, q, r⟩ ho
      cases o <;> first | rfl | (simp [isTree] at ho)
    · rintro ⟨o, q, r⟩ ho
      cases o <;> first | rfl | (simp [isTree] at ho)
  simp only [extEnc, h]

/-- Two traces with the same tree entries give one word. -/
theorem extEnc_congr_tree {tr tr' : Tc W} (h : tr.filter (isTree W) = tr'.filter (isTree W))
    (cm : Dig lam) : extEnc W tr cm = extEnc W tr' cm := by
  rw [← extEnc_tree tr, h, extEnc_tree]

/-- An entry at a Fiat-Shamir oracle is no tree entry. -/
theorem isTree_of_notFb {e : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (h : notFb W e = false) :
    isTree W e = false := by
  obtain ⟨o, q, r⟩ := e
  cases o <;> first | rfl | (simp [notFb] at h)

/-! ## The two algorithms -/

/-- what the prover puts out: the further root, the two records, Link's proof string -/
abbrev Out2 (lam : ℕ) (L : HolographicProtocol I X) (aL : RoundSplits L.link.shape) : Type :=
  Dig lam × L.Rec × L.Rec × OneProtocolProof lam (batLC L aL)

/-- The typed algorithm of the analysis: the committer, the announcement of the root, the prover,
the arm. -/
def joined2 (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool) {St : Type}
    (Ct : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Dig lam × St))
    (Pt : St → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Out2 lam L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  Ct.bind fun a =>
    (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.ann a.1).bind fun _ =>
    (Pt a.2).bind fun b => (V (a.1, b)).bind fun _ => OComp.pure ()

/-- The algorithm of the analysis asks at most tC + tP + 1 + n queries. -/
theorem joined2_queryBound {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} {n : ℕ}
    (hV : ∀ z, DetBound (V z) n) {St : Type}
    {Ct : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Dig lam × St)}
    {Pt : St → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Out2 lam L aL)} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (joined2 W V Ct Pt).QueryBound (tC + tP + 1 + n) := by
  have h : (joined2 W V Ct Pt).QueryBound (tC + (1 + (tP + (n + 0)))) := by
    unfold joined2
    exact hC.bind fun a =>
      (detBound_ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.ann a.1).queryBound.bind fun _ =>
        (hP a.2).bind fun b => (hV (a.1, b)).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- The experiment over one hash function: the committer, the prover, the arm, with the two logs of
strings. -/
def exp2 (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {St : Type}
    (Ct : OComp (rom lam) (Dig lam × St)) (Pt : St → OComp (rom lam) (Out2 lam L aL)) :
    OComp (rom lam)
      (((Dig lam × St) × Trace (rom lam)) × (Out2 lam L aL × Trace (rom lam)) × Bool) :=
  Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b =>
    ((V (a.1.1, b.1)).overOne m).bind fun v => OComp.pure (a, b, v)

/-- The typed log of the analysis at one outcome. -/
def log2 (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (cm : Dig lam) (trC : Trace (rom lam))
    (b : Out2 lam L aL) (trP : Trace (rom lam)) : Tc W :=
  (upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) ++ (upTr m F trP ++ (runA W V F (cm, b)).2)

/-! ## One outcome -/

/-- The log of an algorithm without coins, run at F, holds F's answers. -/
theorem ans_runA {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ z, (V z).NoCoin) (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutLA lam L aL) :
    ∀ e ∈ (runA W V F z).2, e.2.2 = F e.1 e.2.1 := by
  refine support_withTrace_ans F (V z) (runA W V F z) ?_
  rw [runEager_withTrace_det F _ (hV z), PMF.support_pure]
  rfl

/-- A yes of the run at F is a run in its log. -/
theorem runsIn_runA {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} {n : ℕ}
    (hV : ∀ z, DetBound (V z) n) (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (z : OutLA lam L aL) (h : (runA W V F z).1 = true) : RunsIn (runA W V F z).2 (V z) true := by
  have h1 := runsIn_of_mem_support (hV z) F (runA W V F z) (by
    rw [runEager_withTrace_det F _ (noCoin_of_detBound (hV z)), PMF.support_pure]
    rfl)
  rwa [h] at h1

/-- The entries of a log of strings, lifted to typed entries at F, hold F's answers. -/
theorem ans_upTr (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (tr : Trace (rom lam)) :
    ∀ e ∈ upTr m F tr, e.2.2 = F e.1 e.2.1 := by
  intro e he
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
  rfl

/-- One outcome: outside `BadLA` of the lengthened typed log, a yes of the arm holds what it
promises of the word that the committer's typed log determines under the first root and the word
that both typed logs determine under the further root. The premises are those of `arm_lift`
(LinkAnsPr.lean), and the arm begins with the seed queries (`HeadSeeds`). -/
theorem two_lift {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {εL : Err L.link.shape}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hV : IsArm W S cA V)
    (hH : HeadSeeds W S V) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (cm : Dig lam) (trC : Trace (rom lam))
    (b : Out2 lam L aL) (trP : Trace (rom lam)) (hacc : (runA W V F (cm, b)).1 = true)
    (hnb : ¬ BadLA W S cA εL (lenB (preS W S) F (log2 W V m F cm trC b trP))) :
    LinkHoldsAt L (extEnc W (upTr m F trC) cm) (extEnc W (upTr m F (trC ++ trP)) b.1) b.2.1
      b.2.2.1 := by
  have hans : ∀ e ∈ log2 W V m F cm trC b trP, e.2.2 = F e.1 e.2.1 := by
    intro e he
    rcases List.mem_append.1 he with h | h
    · rcases List.mem_append.1 h with h | h
      · exact ans_upTr m F trC e h
      · rw [List.mem_singleton.1 h]
        rfl
    · rcases List.mem_append.1 h with h | h
      · exact ans_upTr m F trP e h
      · exact ans_runA (fun z => noCoin_of_detBound (hV.det z)) F (cm, b) e h
  have hrun : RunsIn (log2 W V m F cm trC b trP) (V (cm, b)) true :=
    (runsIn_runA hV.det F (cm, b) hacc).mono fun e he =>
      List.mem_append_right _ (List.mem_append_right _ he)
  have hlh := arm_lift hsL hlL hcL hW hA hV F hans hrun hnb
  -- the first word: fixed since the announcement
  have e0 : extEnc W (upTr m F trC) cm = extEnc W (log2 W V m F cm trC b trP) cm := by
    have hsplit := lenB_append (preS W S) F (upTr m F trC ++ [annE W cm (F OracleName.ann cm)])
      (upTr m F trP ++ (runA W V F (cm, b)).2)
    have hann : Announced W
        (lenB (preS W S) F (upTr m F trC ++ [annE W cm (F OracleName.ann cm)])) cm := by
      exact mem_lenB (preS W S) F _ _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
    have hM : ¬ EM (lenB (preS W S) F (upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) ++
        lenB (preS W S) F (upTr m F trP ++ (runA W V F (cm, b)).2)) := by
      rw [← hsplit]
      exact fun h => hnb (Or.inl (Or.inl h))
    have h1 := extEnc_stable (W := W) hM (List.prefix_append _ _) (occursIn_of_announced hann)
    rw [← hsplit, extEnc_lenB, extEnc_lenB, extEnc_ann] at h1
    exact h1
  -- the further word: fixed since the arm's seed query
  obtain ⟨l0, l1, rest, a0, b0, e, -, h1, f0, f1⟩ := hH F (cm, b)
  have e1 : extEnc W (upTr m F (trC ++ trP)) b.1 = extEnc W (log2 W V m F cm trC b trP) b.1 := by
    have hsp : log2 W V m F cm trC b trP =
        ((upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) ++ (upTr m F trP ++ (l0 ++ l1))) ++ rest := by
      unfold log2
      rw [e]
      simp only [List.append_assoc]
    have h2 := linkA_fixes_len (S := S) (cA := cA) (εL := εL) F
      (tr := (upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) ++ (upTr m F trP ++ (l0 ++ l1)))
      (tr' := rest) (by rw [← hsp]; exact hnb) (cm := b.1) (a0 := b0)
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h1)))
    rw [← hsp] at h2
    rw [← h2]
    refine extEnc_congr_tree ?_ b.1
    have hf : (l0 ++ l1).filter (isTree W) = [] :=
      List.filter_eq_nil_iff.2 fun x hx => by
        rw [isTree_of_notFb ((List.mem_append.1 hx).elim (f0 x) (f1 x))]
        exact Bool.false_ne_true
    have hu : upTr m F (trC ++ trP) = upTr m F trC ++ upTr m F trP := List.map_append
    rw [hu]
    have ha : [annE W cm (F OracleName.ann cm)].filter (isTree W) = [] := rfl
    simp only [List.filter_append, hf, ha, List.append_nil]
  rw [e0, e1]
  exact hlh

/-! ## The bound -/

/-- An arm that begins with the seed queries is sound against every committer and prover over one
hash function, the word under the first root being the one that the committer's own log of strings
determines: the committer runs and publishes the first root; the prover runs; the arm runs; all ask
the one function. The arm accepts, and what it promises fails of that word and of the word that both
logs determine under the further root, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 5 (tC + tP + 1 + tVL), tC bounds the committer's queries (hC) and tP the prover's at every state
(hP). The premises are those of `arm_pr` (LinkAnsPr.lean): Link's soundness round by round (hsL),
its locality (hlL), the annotation's coherence (hcL), `OKLA W`, `AnsOK cA`, `S.Law εs`, the bound on
the rounds' errors (hbL), `IsArm`; and the arm begins with the seed queries (`HeadSeeds`), and lam
is not 0. m is any coding. -/
theorem arm_pr_two {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (hH : HeadSeeds W S V) (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    {St : Type} (Ct : OComp (rom lam) (Dig lam × St)) (Pt : St → OComp (rom lam) (Out2 lam L aL))
    (tC tP : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    Rom.Pr (exp2 W V m Ct Pt)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHoldsAt L (extEnc W (singleTr m x.1.2) x.1.1.1)
            (extEnc W (singleTr m (x.1.2 ++ x.2.1.2)) x.2.1.1.1) x.2.1.1.2.1 x.2.1.1.2.2.1}) ≤
      (((tC + tP + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hnc : ∀ z, (V z).NoCoin := fun z => noCoin_of_detBound (hV.det z)
  refine le_trans ?_ (badLA_len_rare (cA := cA) (εL := εL) hSd hbL hW.Lk
    (joined2 W V (down m Ct) fun st => down m (Pt st)) _
    (joined2_queryBound hV.det (queryBound_down m Ct tC hC)
      fun st => queryBound_down m (Pt st) tP (hP st)))
  rw [Pr_down m]
  refine MeasureTheory.lintegral_mono fun F => ?_
  unfold PrCoins
  rw [runEager_down]
  simp only [exp2, joined2, Rom.withTrace_bind, OComp.bind_assoc, OComp.ask, OComp.withTrace,
    OComp.bind, OComp.runEager_bind, OComp.runEager, withTrace_down, PMF.bind_map,
    Function.comp_def]
  refine pr_bind_le_bind _ _ _ _ _ fun a ha => pr_bind_le_bind _ _ _ _ _ fun b hb => ?_
  rw [arm_overOne hnc, readBlocks_glue, PMF.pure_bind, runEager_withTrace_det F _ (hnc _),
    PMF.pure_bind]
  refine pr_pure_le_pure ?_
  rintro ⟨hacc, hbad⟩
  by_contra hnb
  have hnb' : ¬ BadLA W S cA εL (lenB (preS W S) F (log2 W V m F a.1.1 a.2 b.1 b.2)) := by
    simpa [log2, annE, runA] using hnb
  have h := two_lift hsL hlL hcL hW hA hV hH m F a.1.1 a.2 b.1 b.2 hacc hnb'
  refine hbad ?_
  have hansC := support_withTrace_ans (glue m F) Ct a ha
  have hansP := support_withTrace_ans (glue m F) (Pt a.1.2) b hb
  have hansCP : ∀ e ∈ a.2 ++ b.2, e.2.2 = glue m F e.1 e.2.1 := fun e he =>
    (List.mem_append.1 he).elim (hansC e) (hansP e)
  have u0 := extEnc_upTr (W := W) hlam m (glue m F) a.2 hansC a.1.1
  have u1 := extEnc_upTr (W := W) hlam m (glue m F) (a.2 ++ b.2) hansCP b.1.1
  rw [readBlocks_glue] at u0 u1
  show LinkHoldsAt L (extEnc W (singleTr m a.2) a.1.1) (extEnc W (singleTr m (a.2 ++ b.2)) b.1.1)
    b.1.2.1 b.1.2.2.1
  rw [← u0, ← u1]
  exact h

end TypedOracleCompiler.Compile.Batch.Cms

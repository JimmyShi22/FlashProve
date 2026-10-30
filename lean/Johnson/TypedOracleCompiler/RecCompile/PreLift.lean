-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/PreLift.lean: a step of the verifier's side that asks the hash function
before the arm runs is counted to the maker.

By the byte format (docs/format/FORMAT.md: R4.5) a chain's run's value is the function's answer on
the parameters' digest and 32 bytes that the file holds or the chain's statement names. So a check
must ask the function before it can hand its arm an input. Such a pre-step `Pre` stands between the
maker and the arm. The experiment here is: the maker, with its log of strings; then `Pre` on what
the maker has put out, with its log; then the verdict on what `Pre` has made. In the analysis "the
maker, then `Pre`" is a maker with the calls of both, so a bound against every maker stands, at
t + c calls.

Two forms of the event, on a property Bad of a value and a log:
  * on the joint log, the maker's with `Pre`'s behind it: no premise on `Pre` but its number of
    calls. What only `Pre` asked then counts as known to the maker: the weaker statement: the word
    may then rest on hashes that the maker never asked;
  * on the maker's own log: if `Pre` asks strings with a property Q alone, and Bad does not see
    entries at such strings laid behind a log.

  `asksIn_log`      the log of an algorithm holds strings that it may ask
  `expPre`          the experiment
  `pre_lift_joint`, `pre_lift_own`   the two forms
  `extEnc_behind`   a word does not see entries laid behind a log of strings that code no leaf and
                    no node
  `arm_pr_run`, `arm_pr_run_joint`     the entry's arm (`arm_pr_maker`, LinkAnsMaker.lean)
  `armB_pr_run`, `armB_pr_run_joint`   the proof's arm (`armB_pr_maker`, ProofAnsStage.lean)
  `armT_pr_key_run`   the key's arm in two stages (`armT_pr_key`, KeyAnsStage.lean): the pre-step is
                    counted to the prover; the word is read off the committer's log, which it does
                    not touch

Limits: soundness alone; the limits in the heads of LinkAnsMaker.lean, ProofAnsStage.lean and
KeyAnsStage.lean hold.
  * `Pre` is a letter: any algorithm over the hash function with at most c calls. Nothing here ties
    it to a program. The number c of a program's reader is not said here.
  * In the forms on the maker's own log `Pre`'s calls stand in no log of the event. That its strings
    code no leaf and no node is asked of the coding and shown of none. A reader that walks trees
    does not meet it: the joint forms serve there.
  * The typed arms take a chain's salt and a leaf's salt as free strings. They do not test that a
    leaf's start is its chain's run's value.
  * `Pre`, like m, the wires, the code of the answers and the arm, is fixed before the function is
    drawn. By the byte format the run's value is a call on the parameters' digest, itself an answer
    of the function: a `Pre` that spells it holds that digest as a constant. No theorem here or in
    PublicLift.lean and the files on it has both a public algorithm and a pre-step; PublicPre.lean
    has, for the entry's arm with one author, and ThreeArmsChk.lean for the three arms.
  * Not here: the three arms in one experiment, and the entry's arm in two stages, behind a
    pre-step.
  * In the key's form the pre-step sees what the prover names alone. The committer's root and record
    go to the arm as typed values, with no pre-step. In the experiment the pre-step's calls stand in
    the prover's log.
  * No yes is shown: the bound would hold of an arm that refuses everything.
  * Said for every coding; none is built, and none is shown to be the programs'.
  * The premises are laws of letters; that they can be met together is not shown; until it is, the
    theorems may be true and empty.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.ProofAnsPublic
import Johnson.TypedOracleCompiler.RecCompile.KeyAnsStage

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

/-! ## The general lemma -/

section
variable {lam : ℕ}

/-- The log of an algorithm all of whose queries have a property holds entries with that property
alone. -/
theorem asksIn_log {Sp : OSpec} {α : Type} (P : (o : Sp.ι) → Sp.Dom o → Prop) (g : Fam Sp) :
    ∀ c : OComp Sp α, c.AsksIn P → ∀ x ∈ (c.withTrace.runEager g).support,
      ∀ e ∈ x.2, P e.1 e.2.1 := by
  intro c
  induction c with
  | pure a =>
    intro _ x hx e he
    have hx' : x = (a, []) := by simpa [OComp.withTrace, OComp.runEager] using hx
    rw [hx'] at he
    exact absurd he List.not_mem_nil
  | sample n k ih =>
    intro h x hx
    simp only [OComp.withTrace, OComp.runEager, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    exact ih r (h r) x hr
  | query o q k ih =>
    intro h x hx e he
    simp only [OComp.withTrace, OComp.runEager, OComp.runEager_bind,
      PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hx' : x = (y.1, ⟨o, q, g o q⟩ :: y.2) := by
      simpa [OComp.runEager] using hxy
    rw [hx'] at he
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact ih _ (h.2 _) y hy e he

/-- The experiment: the maker, with its log; the pre-step on what the maker has put out, with its
log; the verdict on what the pre-step has made. -/
def expPre {U Z : Type} (verd : Z → OComp (rom lam) Bool) (Pre : U → OComp (rom lam) Z)
    (Mk : OComp (rom lam) U) :
    OComp (rom lam) ((U × Trace (rom lam)) × (Z × Trace (rom lam)) × Bool) :=
  Mk.withTrace.bind fun o => (Pre o.1).withTrace.bind fun p =>
    (verd p.1).bind fun b => OComp.pure (o, p, b)

/-- The joint form: a bound against every maker with t + c calls stands for the maker with t calls
and the pre-step with c, the event being said of the maker's log with the pre-step's behind it. -/
theorem pre_lift_joint {U Z : Type} (verd : Z → OComp (rom lam) Bool)
    (Bad : Z → Trace (rom lam) → Prop) (B : ℝ≥0∞) (n : ℕ)
    (base : ∀ Mk' : OComp (rom lam) Z, Mk'.QueryBound n →
      Rom.Pr (Mk'.withTrace.bind fun o => (verd o.1).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧ Bad x.1.1 x.1.2}) ≤ B)
    (Pre : U → OComp (rom lam) Z) (Mk : OComp (rom lam) U) (t c : ℕ) (hn : t + c = n)
    (hq : Mk.QueryBound t) (hP : ∀ u, (Pre u).QueryBound c) :
    Rom.Pr (expPre verd Pre Mk)
        (fun _ => {x | x.2.2 = true ∧ Bad x.2.1.1 (x.1.2 ++ x.2.1.2)}) ≤ B := by
  have h := base (Mk.bind Pre) (hn ▸ hq.bind hP)
  have e : ((Mk.bind Pre).withTrace.bind fun o => (verd o.1).bind fun b =>
        (OComp.pure (o, b) : OComp (rom lam) ((Z × Trace (rom lam)) × Bool))) =
      (expPre verd Pre Mk).bind fun x => OComp.pure ((x.2.1.1, x.1.2 ++ x.2.1.2), x.2.2) := by
    simp only [expPre, Rom.withTrace_bind, OComp.bind_assoc, OComp.bind]
  rw [e, Rom.Pr_bind_pure] at h
  exact h

/-- The form on the maker's own log: if the pre-step asks strings with the property Q alone (hPa),
and Bad does not see entries at such strings laid behind a log (hinv), then the bound B stands for
the event said of the maker's own log. -/
theorem pre_lift_own {U Z : Type} (verd : Z → OComp (rom lam) Bool)
    (Bad : Z → Trace (rom lam) → Prop) (B : ℝ≥0∞) (n : ℕ)
    (base : ∀ Mk' : OComp (rom lam) Z, Mk'.QueryBound n →
      Rom.Pr (Mk'.withTrace.bind fun o => (verd o.1).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧ Bad x.1.1 x.1.2}) ≤ B)
    (Q : List Bool → Prop)
    (hinv : ∀ z tr l, (∀ e ∈ l, Q e.2.1) → Bad z tr → Bad z (tr ++ l))
    (Pre : U → OComp (rom lam) Z) (hPa : ∀ u, (Pre u).AsksIn fun _ s => Q s)
    (Mk : OComp (rom lam) U) (t c : ℕ) (hn : t + c = n)
    (hq : Mk.QueryBound t) (hP : ∀ u, (Pre u).QueryBound c) :
    Rom.Pr (expPre verd Pre Mk) (fun _ => {x | x.2.2 = true ∧ Bad x.2.1.1 x.1.2}) ≤ B := by
  refine le_trans (MeasureTheory.lintegral_mono fun g => ?_)
    (pre_lift_joint verd Bad B n base Pre Mk t c hn hq hP)
  unfold PrCoins expPre
  rw [OComp.runEager_bind]
  refine pr_bind_le_bind _ _ _ _ _ fun o _ => ?_
  rw [OComp.runEager_bind]
  refine pr_bind_le_bind _ _ _ _ _ fun p hp => ?_
  rw [OComp.runEager_bind]
  refine pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
  refine pr_pure_le_pure ?_
  rintro ⟨hb, hbad⟩
  exact ⟨hb, hinv _ _ _ (asksIn_log (fun _ s => Q s) g _ (hPa o.1) p hp) hbad⟩

end

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-! ## A word does not see what is laid behind -/

/-- the string codes no leaf and no node -/
def NoTree (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s : List Bool) : Prop :=
  (m.dec s).1 ≠ OracleName.leaf ∧ (m.dec s).1 ≠ OracleName.node

/-- The typed entries read off a log of strings that code no leaf and no node hold no tree entry. -/
theorem tree_noTree (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) :
    ∀ l : Trace (rom lam), (∀ e ∈ l, NoTree m e.2.1) → (singleTr m l).filter (isTree W) = []
  | [], _ => rfl
  | e :: l, h => by
    obtain ⟨u, s, r⟩ := e
    cases u
    have e1 : singleTr m ((⟨(), s, r⟩ : QA (rom lam)) :: l) =
        singleTr m [⟨(), s, r⟩] ++ singleTr m l := singleTr_append m [⟨(), s, r⟩] l
    have hs : (m.dec s).1 ≠ OracleName.leaf ∧ (m.dec s).1 ≠ OracleName.node := h _ List.mem_cons_self
    have e3 : (singleTr m [(⟨(), s, r⟩ : QA (rom lam))]).filter (isTree W) = [] := by
      rw [singleTr_one]
      by_cases hb : m.blocks (m.dec s).1 = 1
      · rw [if_pos hb]
        exact List.filter_eq_nil_iff.2 fun x hx => by
          rw [List.mem_singleton.1 hx, isTree_of_ne hs]
          exact Bool.false_ne_true
      · rw [if_neg hb]
        rfl
    rw [e1, List.filter_append, e3, List.nil_append,
      tree_noTree m l fun e he => h e (List.mem_cons_of_mem _ he)]

/-- A word does not see entries laid behind a log of strings that code no leaf and no node. -/
theorem extEnc_behind (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (tr l : Trace (rom lam)) (hl : ∀ e ∈ l, NoTree m e.2.1) (cm : Dig lam) :
    extEnc W (singleTr m (tr ++ l)) cm = extEnc W (singleTr m tr) cm := by
  refine extEnc_congr_tree ?_ cm
  rw [singleTr_append, List.filter_append, tree_noTree m l hl, List.append_nil]

/-! ## The entry's arm -/

/-- The entry's arm behind a pre-step: the maker runs; the pre-step runs on what it has put out; the
arm runs on what the pre-step has made; all ask the one function. The arm accepts, and what it
promises of the roots and records that the pre-step has made fails on the one-block entries of the
maker's log of strings with the pre-step's behind it, with probability at most
n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + c + tVL), t bounds the maker's calls (hq) and c the
pre-step's at every input (hP). Premises: those of `arm_pr_maker` (LinkAnsMaker.lean). -/
theorem arm_pr_run_joint {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (hH : HeadSeeds W S V) (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    {U : Type} (Pre : U → OComp (rom lam) (OutLA lam L aL)) (Mk : OComp (rom lam) U) (t c : ℕ)
    (hq : Mk.QueryBound t) (hP : ∀ u, (Pre u).QueryBound c) :
    Rom.Pr (expPre (fun z => (V z).overOne m) Pre Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds W (singleTr m (x.1.2 ++ x.2.1.2)) x.2.1.1.1 x.2.1.1.2.1 x.2.1.1.2.2.1
            x.2.1.1.2.2.2.1}) ≤
      (((t + c + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + c + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  pre_lift_joint (fun z => (V z).overOne m)
    (fun z tr => ¬ LinkHolds W (singleTr m tr) z.1 z.2.1 z.2.2.1 z.2.2.2.1) _ (t + c)
    (fun Mk' h => arm_pr_maker hsL hlL hcL hW hA hSd hbL hV hH hlam m Mk' (t + c) h)
    Pre Mk t c rfl hq hP

/-- The entry's arm behind a pre-step: the maker runs; the pre-step runs on what it has put out; the
arm runs on what the pre-step has made; all ask the one function. The arm accepts, and what it
promises of the roots and records that the pre-step has made fails on the one-block entries of the
maker's own log of strings, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 5 (t + c + tVL), t bounds the maker's calls (hq) and c the pre-step's at every input (hP).
Premises: those of `arm_pr_maker` (LinkAnsMaker.lean); every string that the pre-step asks codes no
leaf and no node under m (hPa). -/
theorem arm_pr_run {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (hH : HeadSeeds W S V) (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    {U : Type} (Pre : U → OComp (rom lam) (OutLA lam L aL))
    (hPa : ∀ u, (Pre u).AsksIn fun _ s => NoTree m s) (Mk : OComp (rom lam) U) (t c : ℕ)
    (hq : Mk.QueryBound t) (hP : ∀ u, (Pre u).QueryBound c) :
    Rom.Pr (expPre (fun z => (V z).overOne m) Pre Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds W (singleTr m x.1.2) x.2.1.1.1 x.2.1.1.2.1 x.2.1.1.2.2.1
            x.2.1.1.2.2.2.1}) ≤
      (((t + c + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + c + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  pre_lift_own (fun z => (V z).overOne m)
    (fun z tr => ¬ LinkHolds W (singleTr m tr) z.1 z.2.1 z.2.2.1 z.2.2.2.1) _ (t + c)
    (fun Mk' h => arm_pr_maker hsL hlL hcL hW hA hSd hbL hV hH hlam m Mk' (t + c) h)
    (NoTree m)
    (fun z tr l hl hb => by
      show ¬ LinkHolds W (singleTr m (tr ++ l)) z.1 z.2.1 z.2.2.1 z.2.2.2.1
      have hb' : ¬ LinkHolds W (singleTr m tr) z.1 z.2.1 z.2.2.1 z.2.2.2.1 := hb
      unfold LinkHolds at hb' ⊢
      rw [extEnc_behind m tr l hl, extEnc_behind m tr l hl]
      exact hb')
    Pre hPa Mk t c rfl hq hP

/-! ## The proof's arm -/

/-- The proof's arm behind a pre-step: the maker runs; the pre-step runs on what it has put out; the
arm runs on what the pre-step has made; all ask the one function. The arm accepts, and what it
promises of the root, instance and record that the pre-step has made fails on the one-block entries
of the maker's log of strings with the pre-step's behind it, with probability at most
n εs + 2 (n + 1)² / 2^lam, where n = 3 (t + c + tVB), t bounds the maker's calls (hq) and c the
pre-step's at every input (hP). Premises: those of `armB_pr_maker` (ProofAnsStage.lean). -/
theorem armB_pr_run_joint {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : AnsOK cA)
    (hSd : S.Law εs) (hbB : Err.Below εB εs)
    {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArmB W S cA r₀ V)
    (hH : HeadSeedB W S V) (hlam : 0 < lam)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {U : Type}
    (Pre : U → OComp (rom lam) (OutBA lam L)) (Mk : OComp (rom lam) U) (t c : ℕ)
    (hq : Mk.QueryBound t) (hP : ∀ u, (Pre u).QueryBound c) :
    Rom.Pr (expPre (fun z => (V z).overOne m) Pre Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w)
            (extEnc W (singleTr m (x.1.2 ++ x.2.1.2)) x.2.1.1.1) x.2.1.1.2.1 x.2.1.1.2.2.1}) ≤
      (((t + c + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + c + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  pre_lift_joint (fun z => (V z).overOne m)
    (fun z tr => ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w) (extEnc W (singleTr m tr) z.1)
      z.2.1 z.2.2.1) _ (t + c)
    (fun Mk' h => armB_pr_maker Rno wit hsB hlB hco hW hA hSd hbB hV hH hlam m Mk' (t + c) h)
    Pre Mk t c rfl hq hP

/-- The proof's arm behind a pre-step: the maker runs; the pre-step runs on what it has put out; the
arm runs on what the pre-step has made; all ask the one function. The arm accepts, and what it
promises of the root, instance and record that the pre-step has made fails on the one-block entries
of the maker's own log of strings, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 3 (t + c + tVB), t bounds the maker's calls (hq) and c the pre-step's at every input (hP).
Premises: those of `armB_pr_maker` (ProofAnsStage.lean); every string that the pre-step asks codes
no leaf and no node under m (hPa). -/
theorem armB_pr_run {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : AnsOK cA)
    (hSd : S.Law εs) (hbB : Err.Below εB εs)
    {V : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArmB W S cA r₀ V)
    (hH : HeadSeedB W S V) (hlam : 0 < lam)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {U : Type}
    (Pre : U → OComp (rom lam) (OutBA lam L))
    (hPa : ∀ u, (Pre u).AsksIn fun _ s => NoTree m s) (Mk : OComp (rom lam) U) (t c : ℕ)
    (hq : Mk.QueryBound t) (hP : ∀ u, (Pre u).QueryBound c) :
    Rom.Pr (expPre (fun z => (V z).overOne m) Pre Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w)
            (extEnc W (singleTr m x.1.2) x.2.1.1.1) x.2.1.1.2.1 x.2.1.1.2.2.1}) ≤
      (((t + c + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + c + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  pre_lift_own (fun z => (V z).overOne m)
    (fun z tr => ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w) (extEnc W (singleTr m tr) z.1)
      z.2.1 z.2.2.1) _ (t + c)
    (fun Mk' h => armB_pr_maker Rno wit hsB hlB hco hW hA hSd hbB hV hH hlam m Mk' (t + c) h)
    (NoTree m)
    (fun z tr l hl hb => by
      show ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w) (extEnc W (singleTr m (tr ++ l)) z.1)
        z.2.1 z.2.2.1
      rw [extEnc_behind m tr l hl]
      exact hb)
    Pre hPa Mk t c rfl hq hP

/-! ## The key's arm, in two stages -/

/-- The key's arm in two stages behind a pre-step on what the prover names: the pre-step is counted
to the prover. The word is read off the committer's own log, which the pre-step does not touch: so
nothing is asked of its strings. The bound is n εs + 2 (n + 1)² / 2^lam at
n = 3 (tC + (tP + c) + 1 + tVT): tC bounds the committer's calls (hC), tP the prover's at every
state (hP) and c the pre-step's at every input. The premises are those of `armT_pr_key`
(KeyAnsStage.lean). The pre-step sees what the prover names alone: the committer's root and record
go to the arm as typed values, with no pre-step. -/
theorem armT_pr_key_run {V : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εT : Err L.offline.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs) (hV : IsArmT W S cA V)
    (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {St U : Type}
    (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St)) (Pv : St → OComp (rom lam) U)
    (Pre : U → OComp (rom lam) (OneProtocolProof lam (batTC L aT)))
    (tC tP c : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ st, (Pv st).QueryBound tP)
    (hPq : ∀ u, (Pre u).QueryBound c) :
    Rom.Pr (expT W V m Ct fun st => (Pv st).bind Pre)
        (fun _ => {x | x.2.2 = true ∧
          ¬ KeyHoldsAt L (extEnc W (singleTr m x.1.2) x.1.1.1.1) x.1.1.1.2}) ≤
      (((tC + (tP + c) + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + (tP + c) + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  armT_pr_key hsT hlT hcT hW hA hSd hbT hV hlam m Ct (fun st => (Pv st).bind Pre) tC (tP + c) hC
    fun st => (hP st).bind hPq

end TypedOracleCompiler.Compile.Batch.Cms

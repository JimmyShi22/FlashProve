-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/ThreeArmsChk.lean: the three arms in one experiment (ThreeArms.lean) in the
shape of a check on what a prover has put out: the public digests, then a reading, then the three
arms.

The committer runs and publishes the first root with its record. The prover, handed all that the
committer has put out, runs and puts out any value u. Then the check: a public algorithm without
coins `Pub` asks the function for the digests d; the reading at d, `Pre d k u`, which sees the
committer's root and record k, asks the function on its way and makes the three proof strings, the
further root with its record and an instance, or refuses; the three arms at d run on that, each
through its own coding at d; no on a refusal. The record's wire, the code of the answers, the arms,
the codings and the reading are families over d.

The bound is that of `three_arms` with the reading's calls counted to the prover: tP + c in the
place of tP. How: `pub_lift_res` (PublicPre.lean) over both stages; at each fixed d, `three_arms` at
the prover "the prover, then the reading at d". The event names the committer's log alone, which the
reading does not touch. So of the reading's strings nothing is asked but that none is a public
string: a reader that walks trees is covered. Inside `three_arms` what only the reading has hashed
then counts as the prover's.

  `arms3`, `arms3Opt`   the three arms' verdicts, joined; no on a refusal
  `Bad3`              the committer's word does not decode to an index for which the instance has a
                    witness
  `three_arms_opt`    `three_arms` for provers that may refuse
  `chk3`              the check
  `chk3Res`, `exp3Chk`   the reading and the arms, what the reading has made being kept; the
                    experiment
  `three_arms_chk`    the bound

The soundness of each of the three protocols is a hypothesis (hsT, hsL, hsB). Pt is the set of
public strings here (in ThreeArms.lean and KeyAnsStage.lean the letter names the prover).

Limits: soundness alone.
  * No yes is shown: the bound would hold of arms, or of a reading, that refuse everything.
  * 36 premises: the 34 of `three_arms_pub` (ThreeArmsPublic.lean) and two on the reading. All are
    laws of letters here; those that name S, cA, an arm, a coding or the reading are asked at every
    d of the type D, reached by `Pub` or not. That they can be met together is not shown; until it
    is, the theorem may be true and empty.
  * Said for every three families of codings that meet the premises. None is built, and that such
    families exist is not shown.
  * Fixed before the function is drawn: `Pub`, and so the public strings; L, aT, aL, W and r₀, which
    do not hang on d; and the way in which wire, code, arms, codings and reading are made of d. So
    neither stage picks the public strings: a committer that writes the public files after asking
    the function is not covered.
  * `Pre` is a letter: nothing here ties it to a program. Two laws are asked of it, at every d, k
    and u: it asks no string of Pt (hnoP); it asks at most c times (hPq), one c for all that a
    prover can put out, and c is not said for a program's reader.
  * The instance of the event is the one that the reading has made. That it is the one in what the
    prover has put out, or the one of a request, is no law here. `chk3` hands on yes or no alone:
    the instance stands in `exp3Chk`, not in the check's answer. A check that is given an instance
    and says no at another: `chk3X`, `three_arms_chkX` (ThreeArmsChkX.lean [not in this library]).
  * The theorem is on `exp3Chk`, which runs `chk3Res`: the steps of `chk3` with what the reading has
    made kept. That the committer's root and record, what the prover has put out and the yes have
    the law of the committer, the prover, then `chk3`, under every function: `exp3Chk_chk3`
    (PublicPreChk.lean).
  * The first root and its record are typed values of the committer: no reading makes them of a
    file. By thought such a reading can be counted to the committer; its calls would then stand in
    the committer's log, and the word could rest on hashes that the committer never asked. A bound
    with such a reading: `three_arms_keyRead_joint` (ThreeArmsKeyRead.lean [not in this library]).
  * Pt holds every string that `Pub` can ask, at every answer of the function. The premises on Pt
    are paid for no arm and no reading here.
  * Not here: `three_arms_holds`, `two_arms`, and the key's arm and the proof's arm on their own,
    behind a public algorithm and a reading.
  * This is a bound on an experiment. Whether a theorem that carries a bound to a scheme and takes
    one coding can take a coding that hangs on d is not settled here.
  * These are the three arms, not the whole compiled verifier.
  * The bound is an average over the public digests of bounds against committers and provers that
    may hang on them.
  * The other limits in the head of ThreeArms.lean hold, but for the number 27 and the sentence on
    who names the instance, which the bullets here replace.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.ThreeArmsPublic
import Johnson.TypedOracleCompiler.RecCompile.PublicPre

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

/-- The three arms, each through its own coding, on the committer's root and record and on what a
prover names: yes if all three say yes. -/
def arms3 (VT : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VL : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VB : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (mT mL mB : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (k : Dig lam × L.Rec)
    (p : OutP3 lam L aT aL) : OComp (rom lam) Bool :=
  ((VT (k.1, k.2, p.1)).overOne mT).bind fun vT =>
  ((VL (k.1, p.2.1.1, k.2, p.2.1.2.1, p.2.1.2.2)).overOne mL).bind fun vL =>
  ((VB (p.2.1.1, p.2.2.1, p.2.1.2.1, p.2.2.2)).overOne mB).bind fun vB =>
    OComp.pure (vT && vL && vB)

/-- The same, no on a refusal. -/
def arms3Opt (VT : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VL : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VB : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (mT mL mB : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (k : Dig lam × L.Rec) :
    Option (OutP3 lam L aT aL) → OComp (rom lam) Bool
  | none => OComp.pure false
  | some p => arms3 VT VL VB mT mL mB k p

/-- The word that a log of strings determines under the root does not decode, with the record, to an
index for which the instance that was named, if one was, has a witness. -/
def Bad3 {Wn : Type} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (Rno : I → X → Wn → Prop)
    (mT : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (k : Dig lam × L.Rec)
    (tr : Trace (rom lam)) (op : Option (OutP3 lam L aT aL)) : Prop :=
  ∀ p, op = some p →
    ¬ ∃ i, L.decodeIndex (extEnc W (singleTr mT tr) k.1) k.2 = some i ∧ ∃ w, Rno i p.2.2.1 w

/-- `three_arms` (ThreeArms.lean) for provers that may refuse and that are handed all that the
committer has put out, its root and record with its state: the committer; the prover; then the three
arms on what the prover names, or no on a refusal. Yes, and the committer's word does not decode to
an index for which the instance that the prover names has a witness: with probability at most the
bound of `three_arms`, to the letter, under its premises; tC bounds the committer's calls (hC) and
tP the prover's at every input (hP). -/
theorem three_arms_opt {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {VT : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {VL : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {VB : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εT : Err L.offline.shape} {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hWT : OKTA W)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hVT : IsArmT W S cA VT)
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hWL : OKLA W)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hVL : IsArm W S cA VL) (hHL : HeadSeeds W S VL)
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hWB : OKBA W) (hbB : Err.Below εB εs)
    (hVB : IsArmB W S cA r₀ VB) (hHB : HeadSeedB W S VB)
    (hA : AnsOK cA) (hSd : S.Law εs) (hlam : 0 < lam)
    (mT mL mB : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (hmL : SameTrees W mT mL)
    (hmB : SameTrees W mT mB) {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pv : (Dig lam × L.Rec) × St → OComp (rom lam) (Option (OutP3 lam L aT aL)))
    (tC tP : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ a, (Pv a).QueryBound tP) :
    Rom.Pr ((run2 id (Ct, Pv)).bind fun y =>
        (arms3Opt VT VL VB mT mL mB y.1.1.1 y.2.1).bind fun b => OComp.pure (y, b))
        (fun _ => {x | x.2 = true ∧ Bad3 W Rno mT x.1.1.1.1 x.1.1.2 x.1.2.1}) ≤
      ((((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      (((((tC + tP + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      ((((tC + tP + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam)) := by
  by_cases hne : Nonempty (OutP3 lam L aT aL)
  · obtain ⟨p0⟩ := hne
    have hP' : ∀ st, ((Pv st).bind fun op => (OComp.pure (op.getD p0) :
        OComp (rom lam) (OutP3 lam L aT aL))).QueryBound tP := fun st => by
      have h : ((Pv st).bind fun op => (OComp.pure (op.getD p0) :
          OComp (rom lam) (OutP3 lam L aT aL))).QueryBound (tP + 0) := (hP st).bind fun _ => trivial
      exact h
    have hC' : (Ct.bind fun a => (OComp.pure (a.1, a) :
        OComp (rom lam) ((Dig lam × L.Rec) × ((Dig lam × L.Rec) × St)))).QueryBound tC := by
      have h : (Ct.bind fun a => (OComp.pure (a.1, a) :
          OComp (rom lam) ((Dig lam × L.Rec) × ((Dig lam × L.Rec) × St)))).QueryBound (tC + 0) :=
        hC.bind fun _ => trivial
      exact h
    refine le_trans (MeasureTheory.lintegral_mono fun g => ?_)
      (three_arms Rno wit hsT hlT hcT hWT hbT hVT hsL hlL hcL hWL hbL hVL hHL hsB hlB hco hWB hbB
        hVB hHB hA hSd hlam mT mL mB hmL hmB (Ct.bind fun a => OComp.pure (a.1, a))
        (fun st => (Pv st).bind fun op => OComp.pure (op.getD p0)) tC tP hC' hP')
    unfold PrCoins run2 exp3A
    simp only [withTrace_map, OComp.bind_assoc, OComp.runEager_bind, OComp.bind, OComp.runEager,
      id]
    refine pr_bind_le_bind _ _ _ _ _ fun a _ => ?_
    refine pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
    obtain ⟨op, tr⟩ := b
    cases op with
    | none =>
      simp only [arms3Opt, OComp.runEager, PMF.pure_bind]
      rw [pr_pure, if_neg fun h => Bool.false_ne_true h.1]
      exact zero_le _
    | some p =>
      simp only [arms3Opt, arms3, OComp.runEager_bind, OComp.runEager, PMF.pure_bind,
        PMF.bind_bind, Option.getD_some]
      refine pr_bind_le_bind _ _ _ _ _ fun vT _ => ?_
      refine pr_bind_le_bind _ _ _ _ _ fun vL _ => ?_
      refine pr_bind_le_bind _ _ _ _ _ fun vB _ => ?_
      refine pr_pure_le_pure ?_
      rintro ⟨hb, hbad⟩
      have hb' : (vT && vL && vB) = true := hb
      simp only [Bool.and_eq_true] at hb'
      exact ⟨hb'.1.1, hb'.1.2, hb'.2, hbad p rfl⟩
  · refine le_trans ?_ (zero_le _)
    unfold Rom.Pr
    refine le_trans (MeasureTheory.lintegral_mono fun g => ?_)
      (le_of_eq (MeasureTheory.lintegral_zero (μ := U (rom lam))))
    show PrCoins g _ _ ≤ 0
    unfold PrCoins
    rw [OComp.runEager_bind, pr_bind]
    refine le_trans (expect_mono _ fun y => ?_) (le_of_eq (expect_const _ 0))
    obtain ⟨a, op, tr⟩ := y
    cases op with
    | none =>
      simp only [arms3Opt, OComp.bind, OComp.runEager]
      rw [pr_pure, if_neg fun h => Bool.false_ne_true h.1]
    | some p => exact absurd ⟨p⟩ hne

/-! ## The check -/

/-- The reading at d of what the prover has put out; then the three arms at d on what the reading
has made. -/
def chk3Res {D U St : Type} (VT : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VL : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VB : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (mT mL mB : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pre : D → Dig lam × L.Rec → U → OComp (rom lam) (Option (OutP3 lam L aT aL))) (d : D)
    (y : (((Dig lam × L.Rec) × St) × Trace (rom lam)) × (U × Trace (rom lam))) :
    OComp (rom lam) (Option (OutP3 lam L aT aL) × Bool) :=
  (Pre d y.1.1.1 y.2.1).bind fun op =>
    (arms3Opt (VT d) (VL d) (VB d) (mT d) (mL d) (mB d) y.1.1.1 op).bind fun b =>
      OComp.pure (op, b)

/-- The check as one term, on the committer's root and record and on what the prover has put out:
the public digests; the reading; the three arms. -/
def chk3 {D U : Type} (VT : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VL : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VB : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (mT mL mB : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pre : D → Dig lam × L.Rec → U → OComp (rom lam) (Option (OutP3 lam L aT aL))) (Pub : OComp (rom
        lam) D)
    (k : Dig lam × L.Rec) (u : U) : OComp (rom lam) Bool :=
  Pub.bind fun d => (Pre d k u).bind fun op =>
    arms3Opt (VT d) (VL d) (VB d) (mT d) (mL d) (mB d) k op

/-- The experiment: the committer and the prover, with their logs; then the check. -/
def exp3Chk {D U St : Type} (VT : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VL : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VB : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (mT mL mB : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pre : D → Dig lam × L.Rec → U → OComp (rom lam) (Option (OutP3 lam L aT aL))) (Pub : OComp (rom
        lam) D)
    (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pv : (Dig lam × L.Rec) × St → OComp (rom lam) U) :
    OComp (rom lam) (((((Dig lam × L.Rec) × St) × Trace (rom lam)) × (U × Trace (rom lam))) × D ×
      Option (OutP3 lam L aT aL) × Bool) :=
  expPR (chk3Res VT VL VB mT mL mB Pre) Pub (run2 id (Ct, Pv))

/-- The check on what a prover has put out, behind a committer, over one hash function. The
experiment (`exp3Chk`): the committer runs and publishes the first root with its record k; the
prover, handed all that the committer has put out, runs and puts out u; the public algorithm; the
reading at its output d, on k and u; the three arms at d on k and on what the reading has made, each
through its own coding at d, or no on a refusal. The check says yes, and the committer's word does
not decode to an index for which the instance that the reading has made has a witness: with
probability at most the sum of three bounds, each of the form n εs + 2 (n + 1)² / 2^lam: at
n = 3 (tC + (tP + c) + 1 + tVT), at n = 5 (tC + (tP + c) + 1 + tVL) and at
n = 3 (tC + (tP + c) + tVB); tC bounds the committer's calls (hC), tP the prover's at every input
(hP) and c the reading's at every d, k and u (hPq). The word is the one that the one-block entries,
under the key's arm's coding at d, of the committer's own log of strings determine under the first
root; the record is the committer's. A yes holds a value, since a refusal is a no. Premises: those
of `three_arms_pub` (ThreeArmsPublic.lean), written out there; and at every d of the type D, reached
by the public algorithm or not, the reading asks no string of Pt (hnoP). The reading may have
coins. -/
theorem three_arms_chk {Wn D U : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {VT : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {VL : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {VB : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εT : Err L.offline.shape} {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hWT : OKTA W)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hVT : ∀ d, IsArmT W (S d) (cA d) (VT d))
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hWL : OKLA W)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hVL : ∀ d, IsArm W (S d) (cA d) (VL d)) (hHL : ∀ d, HeadSeeds W (S d) (VL d))
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hWB : OKBA W) (hbB : Err.Below εB εs)
    (hVB : ∀ d, IsArmB W (S d) (cA d) r₀ (VB d)) (hHB : ∀ d, HeadSeedB W (S d) (VB d))
    (hA : ∀ d, AnsOK (cA d)) (hSd : ∀ d, (S d).Law εs) (hlam : 0 < lam)
    (mT mL mB : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (hmL : ∀ d, SameTrees W (mT d) (mL d)) (hmB : ∀ d, SameTrees W (mT d) (mB d))
    (Pt : List Bool → Prop)
    (hT : ∀ d s, Pt s → ((mT d).dec s).1 ≠ OracleName.leaf ∧ ((mT d).dec s).1 ≠ OracleName.node)
    (hnoT : ∀ d z, ((VT d z).overOne (mT d)).AsksIn fun _ s => ¬ Pt s)
    (hnoL : ∀ d z, ((VL d z).overOne (mL d)).AsksIn fun _ s => ¬ Pt s)
    (hnoB : ∀ d z, ((VB d z).overOne (mB d)).AsksIn fun _ s => ¬ Pt s)
    (Pre : D → Dig lam × L.Rec → U → OComp (rom lam) (Option (OutP3 lam L aT aL)))
    (hnoP : ∀ d k u, (Pre d k u).AsksIn fun _ s => ¬ Pt s) (c : ℕ)
    (hPq : ∀ d k u, (Pre d k u).QueryBound c)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pv : (Dig lam × L.Rec) × St → OComp (rom lam) U) (tC tP : ℕ) (hC : Ct.QueryBound tC)
    (hP : ∀ a, (Pv a).QueryBound tP) :
    Rom.Pr (exp3Chk VT VL VB mT mL mB Pre Pub Ct Pv)
        (fun _ => {x | x.2.2.2 = true ∧
          Bad3 W Rno (mT x.2.1) x.1.1.1.1 x.1.1.2 x.2.2.1}) ≤
      ((((tC + (tP + c) + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + (tP + c) + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      (((((tC + (tP + c) + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + (tP + c) + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      ((((tC + (tP + c) + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + (tP + c) + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam)) := by
  refine pub_lift_res
    (M := OComp (rom lam) ((Dig lam × L.Rec) × St) ×
      ((Dig lam × L.Rec) × St → OComp (rom lam) U))
    (run2 id) wire2 strike2 (fun s r M g => run2_wire id s r M g)
    (fun M => M.1.QueryBound tC ∧ ∀ st, (M.2 st).QueryBound tP)
    (fun s r M h => ⟨queryBound_wire s r M.1 tC h.1, fun st => queryBound_wire s r _ tP (h.2 st)⟩)
    (chk3Res VT VL VB mT mL mB Pre) (fun _ _ _ => rfl) Pt ?_
    (fun d y r => r.2 = true ∧ Bad3 W Rno (mT d) y.1.1.1 y.1.2 r.1)
    (fun d s y r hs hb => ⟨hb.1, fun p hp => by
      have h := hb.2 p hp
      show ¬ ∃ i, L.decodeIndex (extEnc W (singleTr (mT d) (strike s y.1.2)) y.1.1.1.1) y.1.1.1.2 =
        some i ∧ ∃ w, Rno i p.2.2.1 w
      rw [extEnc_strike (mT d) s (hT d s hs)]
      exact h⟩) _ ?_ Pub hPc hPa hPr (Ct, Pv) ⟨hC, hP⟩
  · intro d y
    unfold chk3Res
    refine OComp.AsksIn.bind ?_ (hnoP d _ _)
    intro op
    refine OComp.AsksIn.bind ?_ ?_
    · intro _
      trivial
    · cases op with
      | none => trivial
      | some p =>
        show (arms3 (VT d) (VL d) (VB d) (mT d) (mL d) (mB d) y.1.1.1 p).AsksIn _
        unfold arms3
        refine OComp.AsksIn.bind ?_ (hnoT d _)
        intro _
        refine OComp.AsksIn.bind ?_ (hnoL d _)
        intro _
        refine OComp.AsksIn.bind ?_ (hnoB d _)
        intro _
        trivial
  · rintro d ⟨Ct, Pv⟩ ⟨hC, hP⟩
    have h := three_arms_opt Rno wit hsT hlT hcT hWT hbT (hVT d) hsL hlL hcL hWL hbL (hVL d)
      (hHL d) hsB hlB hco hWB hbB (hVB d) (hHB d) (hA d) (hSd d) hlam (mT d) (mL d) (mB d) (hmL d)
      (hmB d) Ct (fun a => (Pv a).bind (Pre d a.1)) tC (tP + c) hC
      fun a => (hP a).bind (hPq d a.1)
    refine le_trans (MeasureTheory.lintegral_mono fun g => ?_) h
    unfold PrCoins expDR run2 chk3Res
    simp only [Rom.withTrace_bind, OComp.bind_assoc, OComp.runEager_bind, OComp.bind,
      OComp.runEager, id]
    refine pr_bind_le_bind _ _ _ _ _ fun a _ => ?_
    refine pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
    rw [← runEager_withTrace_fst g (Pre d a.1.1 b.1), PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun q _ => ?_
    simp only [Function.comp]
    refine pr_bind_le_bind _ _ _ _ _ fun v _ => ?_
    exact pr_pure_le_pure fun hx => hx

end TypedOracleCompiler.Compile.Batch.Cms

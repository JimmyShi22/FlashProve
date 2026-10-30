-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/PublicPre.lean: the entry's arm in the shape of a check on what an author has
put out: the public digests, then a reading, then the arm.

By the byte format (docs/format/FORMAT.md: R4.4, R4.5, R4.9, R4.10) a check on files needs digests
of the public files, which are answers of the hash function, and a chain's run's value, which is the
function's answer on a string that holds such a digest. So a check asks for the public digests, then
reads the files, asking on the way, and only then can hand its arm an input. Here:

    `chkPub`: d from the public algorithm `Pub`; then `Pre d u`, the reading at d of what the author
      has put out, into a value for the arm or a refusal; then the arm at d, through the coding at
      d, or no on a refusal.

The record's wire, the code of the answers, the arm, the coding and the reading are families over d.
The maker of the bound is the author. The induction of `pub_lift` (PublicLift.lean: the public
digests cost nothing) is said again with a result in the place of yes and no. At each fixed d
`pre_lift_joint` or `pre_lift_own` (PreLift.lean: the reading is counted to the maker) is used.
The bound is n εs + 2 (n + 1)² / 2^lam at n = 5 (t + c + tVL), where t bounds the author's calls and
c the reading's. It is an average over the public digests of bounds against authors that may hang on
them.

  `expDR`, `verdPR`, `expPR`, `pub_lift_res`   `pub_lift` and its experiments (PublicLift.lean)
                    with any type of results in the place of yes and no
  `asksIn_withTrace`   an algorithm with its log asks what the algorithm asks
  `armOpt`, `BadOpt`, `arm_pr_maker_opt`   the arm, and the event, on a value or a refusal;
                    `arm_pr_maker` for makers that may refuse
  `chkPub`          the check
  `chkRes`, `expChk`   the reading and the arm with the reading's log kept; the experiment: the
                    author, with its log; the public algorithm; then these
  `extEnc_strike_append`   a word does not see an entry struck from the first of two joined logs
  `arm_pr_chk_joint`   the bound, the words read off the author's log with the reading's behind it
  `arm_pr_chk`         the bound, the words read off the author's own log: if the reading's strings
                    code no leaf and no node

Limits: soundness alone.
  * No yes is shown: the bounds would hold of an arm, or of a reading, that refuses everything.
  * The premises are laws of letters, asked at every d of the type D, reached by `Pub` or not. That
    they can be met together is not shown; until it is, the theorems may be true and empty.
  * Said for every family of codings that meets the premises. None is built, and that one exists is
    not shown.
  * Fixed before the function is drawn: `Pub`, and so the public strings; L, aT, aL and W, which do
    not hang on d; and the way in which wire, code, arm, coding and reading are made of d. So the
    author does not pick the public strings: an author that writes the public files after asking
    the function is not covered.
  * `Pre` is a letter: nothing here ties it to a program. Three laws are asked of it, at every d and
    every u: it asks no string of Pt (hnoP); it asks at most c times (hPq), one c for all that an
    author can put out, and c is not said for a program's reader; in `arm_pr_chk`, its strings code
    no leaf and no node (hPt). A reader that walks trees does not meet the last: the joint form
    serves there.
  * What the arm promises is said of the roots and records that the reading has made. That these are
    the ones in what the author has put out is no law here. `chkPub` hands on yes or no alone: the
    value that the reading has made stands in `expChk`, not in the check's answer.
  * The theorems are on `expChk`, which runs `chkRes`: the steps of `chkPub` with the reading's log
    kept. That what the author has put out and the yes have the law of the author, then `chkPub`,
    under every function: `expChk_chkPub` (PublicPreChk.lean).
  * Pt holds every string that `Pub` can ask, at every answer of the function (as `Pt2`,
    LinkAnsPublic.lean: the second string at every first digest). Asked: the reading at d and the
    arm at d ask no string of Pt; a string of Pt codes no leaf and no node under the coding at d.
    These are paid for no arm and no reading here. Pt cannot be "codes a point of the spare oracle"
    where the reading's own strings are coded there too: these lie outside Pt.
  * In the joint form what only the reading asked counts as known to the author: the weaker
    statement: the word may then rest on hashes that the author never asked.
  * The entry's arm with one author alone. The three arms in one experiment, behind a public
    algorithm and a reading: `three_arms_chk` (ThreeArmsChk.lean). Not here, nor there: the key's
    arm and the proof's arm on their own, and the entry's arm in two stages, behind both.
  * The other limits in the heads of LinkAnsPublic.lean and PreLift.lean hold, but for the bullet of
    PreLift.lean on what is fixed before the function is drawn, which the fourth bullet here
    replaces.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.PublicLift
import Johnson.TypedOracleCompiler.RecCompile.PreLift
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsKeyStage

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

/-! ## The public digests, with any type of results -/

section
variable {lam : ℕ}

/-- The experiment at a fixed d, with results of any type. -/
def expDR {D Y R : Type} (verd : D → Y → OComp (rom lam) R) (d : D) (c : OComp (rom lam) Y) :
    OComp (rom lam) (Y × D × R) :=
  c.bind fun y => (verd d y).bind fun b => OComp.pure (y, d, b)

/-- The result with the public algorithm in front. -/
def verdPR {D Y R : Type} (verd : D → Y → OComp (rom lam) R) (Pub : OComp (rom lam) D) (y : Y) :
    OComp (rom lam) (D × R) :=
  Pub.bind fun d => (verd d y).bind fun b => OComp.pure (d, b)

/-- The experiment with the public algorithm, with results of any type. -/
def expPR {D Y R : Type} (verd : D → Y → OComp (rom lam) R) (Pub : OComp (rom lam) D)
    (c : OComp (rom lam) Y) : OComp (rom lam) (Y × D × R) :=
  c.bind fun y => (verdPR verd Pub y).bind fun v => OComp.pure (y, v)

/-- Public digests cost nothing: `pub_lift` (PublicLift.lean) with a result of any type R in the
place of yes and no. If at every fixed d the event Ev d, of the makers' outcome and the result, has
probability at most B against every maker with ok (base), then it has probability at most B where d
is the output of a public algorithm run behind the makers' part. Premises: the law of the wired
maker (hrun); ok is kept by wiring (hok); the step that makes the result is the same program on a
struck outcome (hvs) and at no d asks a string of Pt (hno); Ev d is kept, at every result, when the
entries at a string of Pt are struck from the outcome (hbs); the public algorithm has no coins, asks
strings of Pt alone and none twice. -/
theorem pub_lift_res {D Y R M : Type} (run : M → OComp (rom lam) Y)
    (wireM : List Bool → (Fin lam → Bool) → M → M) (strikeY : List Bool → Y → Y)
    (hrun : ∀ s r Mk g, (run (wireM s r Mk)).runEager g =
      ((run Mk).runEager (g.set () s r)).map (strikeY s))
    (ok : M → Prop) (hok : ∀ s r Mk, ok Mk → ok (wireM s r Mk))
    (verd : D → Y → OComp (rom lam) R) (hvs : ∀ d s y, verd d (strikeY s y) = verd d y)
    (Pt : List Bool → Prop) (hno : ∀ d y, (verd d y).AsksIn fun _ s => ¬ Pt s)
    (Ev : D → Y → R → Prop) (hbs : ∀ d s y r, Pt s → Ev d y r → Ev d (strikeY s y) r)
    (B : ℝ≥0∞)
    (base : ∀ d Mk, ok Mk →
      Rom.Pr (expDR verd d (run Mk)) (fun _ => {x | Ev x.2.1 x.1 x.2.2}) ≤ B) :
    ∀ (Pub : OComp (rom lam) D), Pub.NoCoin → (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
      ∀ Mk, ok Mk →
        Rom.Pr (expPR verd Pub (run Mk)) (fun _ => {x | Ev x.2.1 x.1 x.2.2}) ≤ B := by
  intro Pub
  induction Pub with
  | pure d =>
    intro _ _ _ Mk hq
    have e : expPR verd (OComp.pure d) (run Mk) = expDR verd d (run Mk) := by
      simp only [expPR, expDR, verdPR, OComp.bind_assoc, OComp.bind]
    rw [e]
    exact base d Mk hq
  | sample n k _ =>
    intro hc
    exact hc.elim
  | query o s k ih =>
    intro hc hp hr Mk hq
    cases o
    unfold Rom.Pr
    rw [lintegral_U_resample () s (measurable_PrCoins _ _)]
    refine (expect_mono _ fun r => ?_).trans (le_of_eq (expect_const _ _))
    refine le_trans (MeasureTheory.lintegral_mono fun g => ?_)
      (ih r (hc r) (hp.2 r) (hr r).2 (wireM s r Mk) (hok s r Mk hq))
    have hv : ∀ y, (verdPR verd (OComp.query () s k) y).runEager (g.set () s r) =
        (verdPR verd (k r) y).runEager g := by
      intro y
      have h1 : (verdPR verd (OComp.query () s k) y).runEager (g.set () s r) =
          (verdPR verd (k r) y).runEager (g.set () s r) := by
        simp only [verdPR, OComp.bind, OComp.runEager, Fam.set_self]
      rw [h1]
      refine runEager_set s r g _ ?_
      have ha : ∀ d, ((verd d y).bind fun b =>
          (OComp.pure (d, b) : OComp (rom lam) (D × R))).AsksIn fun _ s' => s' ≠ s := by
        intro d
        refine OComp.AsksIn.bind ?_
          (OComp.AsksIn.mono (P := fun _ s' => ¬ Pt s') (Q := fun _ s' => s' ≠ s)
            (fun _ s' h e => h (by rw [e]; exact hp.1)) (hno d y))
        intro _
        trivial
      exact OComp.AsksIn.bind ha (hr r).1
    have hvs' : ∀ y, verdPR verd (k r) (strikeY s y) = verdPR verd (k r) y := by
      intro y
      simp only [verdPR, hvs]
    unfold PrCoins expPR
    rw [OComp.runEager_bind, OComp.runEager_bind, hrun, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun y _ => ?_
    simp only [Function.comp, OComp.runEager_bind, hv, hvs']
    refine pr_bind_le_bind _ _ _ _ _ fun v _ => ?_
    refine pr_pure_le_pure ?_
    intro hbad
    exact hbs v.1 s y v.2 hp.1 hbad

/-- All queries of an algorithm with its log are the algorithm's. -/
theorem asksIn_withTrace {Sp : OSpec} {α : Type} (P : (o : Sp.ι) → Sp.Dom o → Prop) :
    ∀ c : OComp Sp α, c.AsksIn P → c.withTrace.AsksIn P := by
  intro c
  induction c with
  | pure a => intro _; trivial
  | sample n k ih => intro h x; exact ih x (h x)
  | query o q k ih =>
    intro h
    refine ⟨h.1, fun r => ?_⟩
    refine OComp.AsksIn.bind ?_ (ih r (h.2 r))
    intro _
    trivial

end

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-! ## The arm on a value or a refusal -/

/-- The arm over the hash function on a value, no on a refusal. -/
def armOpt (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) :
    Option (OutLA lam L aL) → OComp (rom lam) Bool
  | none => OComp.pure false
  | some z => (V z).overOne m

/-- what the arm promises fails of the value, if there is one, on a log of strings -/
def BadOpt (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (oz : Option (OutLA lam L aL))
    (tr : Trace (rom lam)) : Prop :=
  ∀ z, oz = some z → ¬ LinkHolds W (singleTr m tr) z.1 z.2.1 z.2.2.1 z.2.2.2.1

/-- `arm_pr_maker` (LinkAnsMaker.lean) for makers that may refuse: the maker runs; then the arm on
its value, or no on a refusal. Yes, and what the arm promises fails of the value on the one-block
entries of the maker's log of strings, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 5 (t + tVL) and t bounds the maker's calls (hq). The premises are those of `arm_pr_maker`. -/
theorem arm_pr_maker_opt {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (hH : HeadSeeds W S V) (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Mk : OComp (rom lam) (Option (OutLA lam L aL))) (t : ℕ) (hq : Mk.QueryBound t) :
    Rom.Pr (Mk.withTrace.bind fun o => (armOpt V m o.1).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧ BadOpt W m x.1.1 x.1.2}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  by_cases hne : Nonempty (OutLA lam L aL)
  · obtain ⟨z0⟩ := hne
    have hq' : (Mk.bind fun oz => OComp.pure (oz.getD z0)).QueryBound t := by
      have h : (Mk.bind fun oz => (OComp.pure (oz.getD z0) :
          OComp (rom lam) (OutLA lam L aL))).QueryBound (t + 0) := hq.bind fun _ => trivial
      exact h
    refine le_trans (MeasureTheory.lintegral_mono fun g => ?_)
      (arm_pr_maker hsL hlL hcL hW hA hSd hbL hV hH hlam m
        (Mk.bind fun oz => OComp.pure (oz.getD z0)) t hq')
    unfold PrCoins
    rw [withTrace_map, OComp.bind_assoc, OComp.runEager_bind, OComp.runEager_bind]
    refine pr_bind_le_bind _ _ _ _ _ fun o _ => ?_
    obtain ⟨oz, tr⟩ := o
    cases oz with
    | none =>
      simp only [armOpt, OComp.bind, OComp.runEager]
      rw [pr_pure, if_neg fun h => Bool.false_ne_true h.1]
      exact zero_le _
    | some z =>
      simp only [armOpt, OComp.bind, OComp.runEager_bind, Option.getD_some]
      refine pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
      refine pr_pure_le_pure ?_
      rintro ⟨hb, hbad⟩
      exact ⟨hb, hbad z rfl⟩
  · refine le_trans ?_ (zero_le _)
    unfold Rom.Pr
    refine le_trans (MeasureTheory.lintegral_mono fun g => ?_)
      (le_of_eq (MeasureTheory.lintegral_zero (μ := U (rom lam))))
    show PrCoins g _ _ ≤ 0
    unfold PrCoins
    rw [OComp.runEager_bind, pr_bind]
    refine le_trans (expect_mono _ fun o => ?_) (le_of_eq (expect_const _ 0))
    obtain ⟨oz, tr⟩ := o
    cases oz with
    | none =>
      simp only [armOpt, OComp.bind, OComp.runEager]
      rw [pr_pure, if_neg fun h => Bool.false_ne_true h.1]
    | some z => exact absurd ⟨z⟩ hne

/-! ## The check on what an author has put out -/

/-- The reading at d of what the author has put out, with its log; then the arm at d on what the
reading has made. -/
def chkRes {D U : Type} (V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pre : D → U → OComp (rom lam) (Option (OutLA lam L aL))) (d : D)
    (y : U × Trace (rom lam)) :
    OComp (rom lam) ((Option (OutLA lam L aL) × Trace (rom lam)) × Bool) :=
  (Pre d y.1).withTrace.bind fun p => (armOpt (V d) (m d) p.1).bind fun b => OComp.pure (p, b)

/-- The check as one term: the public digests; the reading; the arm. -/
def chkPub {D U : Type} (V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pre : D → U → OComp (rom lam) (Option (OutLA lam L aL))) (Pub : OComp (rom lam) D) (u : U) :
    OComp (rom lam) Bool :=
  Pub.bind fun d => (Pre d u).bind fun oz => armOpt (V d) (m d) oz

/-- The experiment: the author, with its log; then the check, with the reading's log. -/
def expChk {D U : Type} (V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pre : D → U → OComp (rom lam) (Option (OutLA lam L aL))) (Pub : OComp (rom lam) D)
    (Mk : OComp (rom lam) U) :
    OComp (rom lam) ((U × Trace (rom lam)) × D ×
      (Option (OutLA lam L aL) × Trace (rom lam)) × Bool) :=
  expPR (chkRes V m Pre) Pub Mk.withTrace

/-- The reading and the arm ask no public string. -/
theorem asksIn_chkRes {D U : Type}
    {V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam}
    {Pre : D → U → OComp (rom lam) (Option (OutLA lam L aL))} {Pt : List Bool → Prop}
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt s)
    (hnoP : ∀ d u, (Pre d u).AsksIn fun _ s => ¬ Pt s) (d : D) (y : U × Trace (rom lam)) :
    (chkRes V m Pre d y).AsksIn fun _ s => ¬ Pt s := by
  unfold chkRes
  refine OComp.AsksIn.bind ?_ (asksIn_withTrace _ _ (hnoP d y.1))
  intro p
  refine OComp.AsksIn.bind ?_ ?_
  · intro _
    trivial
  · cases p.1 with
    | none => trivial
    | some z => exact hno d z

/-- The tree entries of a log with another behind it are not moved when entries at a string that
codes no leaf and no node are struck from the first. -/
theorem extEnc_strike_append (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s : List Bool)
    (h0 : (m.dec s).1 ≠ OracleName.leaf ∧ (m.dec s).1 ≠ OracleName.node) (tr l : Trace (rom lam))
    (cm : Dig lam) :
    extEnc W (singleTr m (strike s tr ++ l)) cm = extEnc W (singleTr m (tr ++ l)) cm := by
  refine extEnc_congr_tree ?_ cm
  rw [singleTr_append, singleTr_append, List.filter_append, List.filter_append,
    tree_strike m s h0 tr]

/-- The check on what an author has put out, against every author over one hash function, the words
being read off the author's log of strings with the reading's behind it. The experiment (`expChk`):
the author runs; the public algorithm; the reading at its output d, on what the author has put out;
the arm at d on the value that the reading has made, through the coding at d, or no on a refusal;
all ask the one function. The check says yes, and what the arm promises of the roots and records
that the reading has made fails on the one-block entries of that joint log under the coding at d,
with probability at most n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + c + tVL), t bounds the author's
calls (hq) and c the reading's at every d and every input (hPq). A yes holds a value, since a
refusal is a no. Premises, at every d of the type D, reached by the public algorithm or not: those
of `arm_pr_maker` (LinkAnsMaker.lean); the reading (hnoP) and the arm over the hash function (hno)
ask no string of Pt; a string of Pt codes no leaf and no node (hT). The public algorithm has no
coins (hPc), asks strings of Pt alone (hPa) and none twice (hPr). The reading may have coins. -/
theorem arm_pr_chk_joint {D U : Type} {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : D → L.OutOfDomainAnswer → List (Dig lam)}
    {V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hV : ∀ d, IsArm W (S d) (cA d) (V d)) (hH : ∀ d, HeadSeeds W (S d) (V d)) (hlam : 0 < lam)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hT : ∀ d s, Pt s → ((m d).dec s).1 ≠ OracleName.leaf ∧ ((m d).dec s).1 ≠ OracleName.node)
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt s)
    (Pre : D → U → OComp (rom lam) (Option (OutLA lam L aL)))
    (hnoP : ∀ d u, (Pre d u).AsksIn fun _ s => ¬ Pt s) (c : ℕ)
    (hPq : ∀ d u, (Pre d u).QueryBound c)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) (Mk : OComp (rom lam) U) (t : ℕ) (hq : Mk.QueryBound t) :
    Rom.Pr (expChk V m Pre Pub Mk)
        (fun _ => {x | x.2.2.2 = true ∧
          BadOpt W (m x.2.1) x.2.2.1.1 (x.1.2 ++ x.2.2.1.2)}) ≤
      (((t + c + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + c + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine pub_lift_res (M := OComp (rom lam) U) (fun Mk => Mk.withTrace) wire
    (fun s y => (y.1, strike s y.2)) (fun s r Mk g => withTrace_wire s r g Mk)
    (fun Mk => Mk.QueryBound t) (fun s r Mk h => queryBound_wire s r Mk t h)
    (chkRes V m Pre) (fun _ _ _ => rfl) Pt (asksIn_chkRes hno hnoP)
    (fun d y r => r.2 = true ∧ BadOpt W (m d) r.1.1 (y.2 ++ r.1.2))
    (fun d s y r hs hb => ⟨hb.1, fun z hz => by
      have h := hb.2 z hz
      unfold LinkHolds at h ⊢
      show ¬ (¬ L.hasCollisionAt (extEnc W (singleTr (m d) (strike s y.2 ++ r.1.2)) z.1) _ ∧ _)
      rw [extEnc_strike_append (m d) s (hT d s hs), extEnc_strike_append (m d) s (hT d s hs)]
      exact h⟩) _ ?_ Pub hPc hPa hPr Mk hq
  intro d Mk hq
  have e : expDR (chkRes V m Pre) d Mk.withTrace =
      (expPre (armOpt (V d) (m d)) (Pre d) Mk).bind fun x =>
        OComp.pure (x.1, d, (x.2.1, x.2.2)) := by
    simp only [expDR, expPre, chkRes, OComp.bind_assoc, OComp.bind]
  rw [e, Rom.Pr_bind_pure]
  exact pre_lift_joint (armOpt (V d) (m d)) (BadOpt W (m d)) _ (t + c)
    (fun Mk' h => arm_pr_maker_opt hsL hlL hcL hW (hA d) (hSd d) hbL (hV d) (hH d) hlam (m d) Mk'
      (t + c) h) (Pre d) Mk t c rfl hq (hPq d)

/-- The check on what an author has put out, against every author over one hash function, the words
being read off the author's own log of strings. The experiment is `expChk`, as in
`arm_pr_chk_joint`. The check says yes, and what the arm promises of the roots and records that the
reading has made fails on the one-block entries of the author's own log under the coding at d, with
probability at most n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + c + tVL), t bounds the author's
calls (hq) and c the reading's at every d and every input (hPq). Premises: those of
`arm_pr_chk_joint`; and at every d of the type D every string that the reading asks codes no leaf
and no node under the coding at d (hPt). -/
theorem arm_pr_chk {D U : Type} {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : D → L.OutOfDomainAnswer → List (Dig lam)}
    {V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hV : ∀ d, IsArm W (S d) (cA d) (V d)) (hH : ∀ d, HeadSeeds W (S d) (V d)) (hlam : 0 < lam)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hT : ∀ d s, Pt s → ((m d).dec s).1 ≠ OracleName.leaf ∧ ((m d).dec s).1 ≠ OracleName.node)
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt s)
    (Pre : D → U → OComp (rom lam) (Option (OutLA lam L aL)))
    (hnoP : ∀ d u, (Pre d u).AsksIn fun _ s => ¬ Pt s)
    (hPt : ∀ d u, (Pre d u).AsksIn fun _ s => NoTree (m d) s) (c : ℕ)
    (hPq : ∀ d u, (Pre d u).QueryBound c)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) (Mk : OComp (rom lam) U) (t : ℕ) (hq : Mk.QueryBound t) :
    Rom.Pr (expChk V m Pre Pub Mk)
        (fun _ => {x | x.2.2.2 = true ∧ BadOpt W (m x.2.1) x.2.2.1.1 x.1.2}) ≤
      (((t + c + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + c + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine pub_lift_res (M := OComp (rom lam) U) (fun Mk => Mk.withTrace) wire
    (fun s y => (y.1, strike s y.2)) (fun s r Mk g => withTrace_wire s r g Mk)
    (fun Mk => Mk.QueryBound t) (fun s r Mk h => queryBound_wire s r Mk t h)
    (chkRes V m Pre) (fun _ _ _ => rfl) Pt (asksIn_chkRes hno hnoP)
    (fun d y r => r.2 = true ∧ BadOpt W (m d) r.1.1 y.2)
    (fun d s y r hs hb => ⟨hb.1, fun z hz h =>
      hb.2 z hz ((linkHolds_strike (m d) s (hT d s hs) y.2 _ _ _ _).1 h)⟩) _ ?_ Pub hPc hPa hPr Mk
    hq
  intro d Mk hq
  have e : expDR (chkRes V m Pre) d Mk.withTrace =
      (expPre (armOpt (V d) (m d)) (Pre d) Mk).bind fun x =>
        OComp.pure (x.1, d, (x.2.1, x.2.2)) := by
    simp only [expDR, expPre, chkRes, OComp.bind_assoc, OComp.bind]
  rw [e, Rom.Pr_bind_pure]
  exact pre_lift_own (armOpt (V d) (m d)) (BadOpt W (m d)) _ (t + c)
    (fun Mk' h => arm_pr_maker_opt hsL hlL hcL hW (hA d) (hSd d) hbL (hV d) (hH d) hlam (m d) Mk'
      (t + c) h) (NoTree (m d))
    (fun oz tr l hl hb z hz => by
      have h := hb z hz
      unfold LinkHolds at h ⊢
      rw [extEnc_behind (m d) tr l hl, extEnc_behind (m d) tr l hl]
      exact h)
    (Pre d) (hPt d) Mk t c rfl hq (hPq d)

end TypedOracleCompiler.Compile.Batch.Cms

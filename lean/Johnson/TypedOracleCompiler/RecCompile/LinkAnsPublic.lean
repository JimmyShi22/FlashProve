-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublic.lean: the entry's arm with the answers alone, where the
record's wire, the code of the answers, the arm and the coding hang on public digests that are
themselves answers of the one hash function.

In the files before this one the record's wire S and the coding m are letters fixed before the
function is drawn, `S.cfg` with them. By the byte format (docs/format/FORMAT.md: R4.4, R4.9, R4.10,
R7.4) the configuration's digest is an answer of the same hash function on the public files. It
stands in a table's name and so in the first seed query; and it starts the calls for a stored
table's leaves and for the vertices, which no typed query holds, so that the coding of typed queries
as strings hangs on it. The parameters' digest, which stands in Link's first call, is an answer on a
string that holds the configuration's digest. Here a public
algorithm without coins `Pub` asks the function for such digests, and wire, code, arm and coding are
families over its output d. In the experiment the arm runs `Pub` itself. The maker may ask the same
strings among its calls.

The bound is that of `arm_pr_maker`, to the letter: the public queries cost nothing.

How: one public point at a time. The average over the function is the average over the value r at
that point of the average over the function with r laid in there (`lintegral_U_resample`,
Rom/Measure.lean). At a fixed r the value is wired into the maker: every query of the maker at the
point is answered by r without asking (`wire`). What follows the point in `Pub`, and the arm, never
ask it, so their runs do not hang on the value there. A word does not see an entry at the point. So
at each fixed output d of `Pub` wire, code, arm and coding are fixed before the function is drawn,
the wired maker is a maker with no more queries, and `arm_pr_maker` applies. The bound is thus an
average over the public digests of bounds against makers that may hang on them.

  `wire`            an algorithm with the queries at one string answered by a fixed value, unasked
                    (another sense of the word than in "the record's wire")
  `runEager_wire`, `withTrace_wire`, `queryBound_wire`   its run, its log, its number of queries
  `runEager_set`    an algorithm that never asks a string has a run that does not hang on the value
                    there
  `NoRepeat`        an algorithm asks no string twice
  `expPub`          the experiment: the maker; then the public algorithm and the arm at its output
  `arm_pr_pub`      the bound
  `pub2`, `arm_pr_pub2`   two digests, the second on a string made of the first

Limits: soundness alone.
  * The public strings are letters fixed before the function is drawn, as are W and the way in which
    wire, code, arm and coding are made of the digests.
  * Asked of a set Pt of strings: `Pub` asks strings of Pt alone, none twice; the arm, over the hash
    function, asks none of Pt; a string of Pt codes no leaf and no node. LinkAnsPublicArm.lean pays
    the second and the third for the two arms where Pt is "codes a point of the spare oracle
    `OracleName.other`". That the programs' digests are spelled so under a coding is, like all of m, shown
    nowhere.
  * Said for every family of codings that meets the premises. None is built, and that one exists is
    not shown.
  * No yes is shown: the bound would hold of an arm that refuses everything.
  * One maker. Of the theorems in two stages `arm_pr_key` (LinkAnsKeyStage.lean) is lifted in
    LinkAnsKeyPublic.lean. `arm_pr_two` (LinkAnsTwoStage.lean) and the entries of both at a written
    object still fix the digests before the function is drawn.
  * The other limits in the head of LinkAnsMaker.lean hold, but for the sentence on what is fixed
    before the function is drawn, which the first bullet here replaces.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsTwoStage
import Rom.AsksIn

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

/-! ## A value wired in at one string -/

section
variable {lam : ℕ} {α : Type}

/-- The algorithm with every query at the string s0 answered by r, without asking. -/
def wire (s0 : List Bool) (r : Fin lam → Bool) : OComp (rom lam) α → OComp (rom lam) α
  | .pure a => .pure a
  | .sample n k => .sample n fun x => wire s0 r (k x)
  | .query o s k => if s = s0 then wire s0 r (k r) else .query o s fun x => wire s0 r (k x)

/-- strike the entries at the string s0 from a log -/
def strike (s0 : List Bool) (tr : Trace (rom lam)) : Trace (rom lam) :=
  tr.filter fun e => decide (e.2.1 ≠ s0)

/-- The wired algorithm runs under g as the algorithm under g with r laid in at s0. -/
theorem runEager_wire (s0 : List Bool) (r : Fin lam → Bool) (g : Fam (rom lam))
    (c : OComp (rom lam) α) : (wire s0 r c).runEager g = c.runEager (g.set () s0 r) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [wire, OComp.runEager, ih]
  | query o s k ih =>
    cases o
    by_cases h : s = s0
    · subst h
      simp only [wire, if_true, OComp.runEager, ih, Fam.set_self]
    · simp only [wire, if_neg h, OComp.runEager, ih, Fam.set_of_ne_point g () h r]

/-- Its log is the algorithm's log with the entries at s0 struck. -/
theorem withTrace_wire (s0 : List Bool) (r : Fin lam → Bool) (g : Fam (rom lam))
    (c : OComp (rom lam) α) :
    (wire s0 r c).withTrace.runEager g =
      (c.withTrace.runEager (g.set () s0 r)).map fun o => (o.1, strike s0 o.2) := by
  induction c with
  | pure a =>
    simp only [wire, OComp.withTrace, OComp.runEager, PMF.pure_map]
    rfl
  | sample n k ih =>
    simp only [wire, OComp.withTrace, OComp.runEager, ih, PMF.map_bind]
  | query o s k ih =>
    cases o
    by_cases h : s = s0
    · subst h
      simp only [wire, if_true, OComp.withTrace, OComp.runEager, OComp.runEager_bind, ih,
        Fam.set_self, PMF.map_bind, PMF.pure_map]
      rw [← PMF.bind_pure_comp]
      refine congrArg _ (funext fun out => ?_)
      simp [strike]
    · simp only [wire, if_neg h, OComp.withTrace, OComp.runEager, OComp.runEager_bind, ih,
        Fam.set_of_ne_point g () h r, PMF.map_bind, PMF.pure_map, PMF.bind_map]
      refine congrArg _ (funext fun out => ?_)
      simp [strike, h]

/-- It asks no more. -/
theorem queryBound_wire (s0 : List Bool) (r : Fin lam → Bool) :
    ∀ (c : OComp (rom lam) α) (t : ℕ), c.QueryBound t → (wire s0 r c).QueryBound t := by
  intro c
  induction c with
  | pure a => intro t _; trivial
  | sample n k ih => intro t h x; exact ih x t (h x)
  | query o s k ih =>
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t =>
      by_cases hs : s = s0
      · simp only [wire, if_pos hs]
        exact (ih r t (h r)).mono (Nat.le_succ t)
      · simp only [wire, if_neg hs]
        exact fun x => ih x t (h x)

/-- An algorithm that never asks s0 has a run that does not hang on the value at s0. -/
theorem runEager_set (s0 : List Bool) (r : Fin lam → Bool) (g : Fam (rom lam)) :
    ∀ c : OComp (rom lam) α, (c.AsksIn fun _ s => s ≠ s0) →
      c.runEager (g.set () s0 r) = c.runEager g := by
  intro c
  induction c with
  | pure a => intro _; rfl
  | sample n k ih =>
    intro h
    simp only [OComp.runEager]
    refine congrArg _ (funext fun x => ih x (h x))
  | query o s k ih =>
    intro h
    cases o
    simp only [OComp.runEager, Fam.set_of_ne_point g () h.1 r]
    exact ih _ (h.2 _)

/-- The algorithm asks no string twice. -/
def NoRepeat : OComp (rom lam) α → Prop
  | .pure _ => True
  | .sample _ k => ∀ x, NoRepeat (k x)
  | .query _ s k => ∀ x, ((k x).AsksIn fun _ s' => s' ≠ s) ∧ NoRepeat (k x)

end

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-! ## A word does not see a struck entry -/

/-- An entry at an oracle that is neither the leaf's nor the node's is no tree entry. -/
theorem isTree_of_ne {e : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (h : e.1 ≠ OracleName.leaf ∧ e.1 ≠ OracleName.node) : isTree W e = false := by
  obtain ⟨o, q, r⟩ := e
  cases o <;> first | rfl | exact absurd rfl h.1 | exact absurd rfl h.2

/-- The tree entries read off a log of strings are not moved when the entries at a string that codes
no leaf and no node are struck. -/
theorem tree_strike (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s0 : List Bool)
    (h0 : (m.dec s0).1 ≠ OracleName.leaf ∧ (m.dec s0).1 ≠ OracleName.node) :
    ∀ tr : Trace (rom lam),
      (singleTr m (strike s0 tr)).filter (isTree W) = (singleTr m tr).filter (isTree W)
  | [] => rfl
  | e :: tr => by
    have ih := tree_strike m s0 h0 tr
    obtain ⟨u, s, r⟩ := e
    cases u
    have e1 : singleTr m ((⟨(), s, r⟩ : QA (rom lam)) :: tr) =
        singleTr m [⟨(), s, r⟩] ++ singleTr m tr := singleTr_append m [⟨(), s, r⟩] tr
    by_cases hs : s = s0
    · subst hs
      have e2 : strike s ((⟨(), s, r⟩ : QA (rom lam)) :: tr) = strike s tr := by simp [strike]
      have e3 : (singleTr m [(⟨(), s, r⟩ : QA (rom lam))]).filter (isTree W) = [] := by
        rw [singleTr_one]
        by_cases hb : m.blocks (m.dec s).1 = 1
        · rw [if_pos hb]
          exact List.filter_eq_nil_iff.2 fun x hx => by
            rw [List.mem_singleton.1 hx, isTree_of_ne h0]
            exact Bool.false_ne_true
        · rw [if_neg hb]
          rfl
      rw [e2, e1, List.filter_append, e3, List.nil_append, ih]
    · have e2 : strike s0 ((⟨(), s, r⟩ : QA (rom lam)) :: tr) =
          (⟨(), s, r⟩ : QA (rom lam)) :: strike s0 tr := by simp [strike, hs]
      have e4 : singleTr m ((⟨(), s, r⟩ : QA (rom lam)) :: strike s0 tr) =
          singleTr m [⟨(), s, r⟩] ++ singleTr m (strike s0 tr) :=
        singleTr_append m [⟨(), s, r⟩] (strike s0 tr)
      rw [e2, e4, e1, List.filter_append, List.filter_append, ih]

/-- So what the arm promises is the same of the two logs. -/
theorem linkHolds_strike (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s0 : List Bool)
    (h0 : (m.dec s0).1 ≠ OracleName.leaf ∧ (m.dec s0).1 ≠ OracleName.node) (tr : Trace (rom lam))
    (cm cm' : Dig lam) (rec rec' : L.Rec) :
    LinkHolds W (singleTr m (strike s0 tr)) cm cm' rec rec' ↔
      LinkHolds W (singleTr m tr) cm cm' rec rec' := by
  unfold LinkHolds
  rw [extEnc_congr_tree (tree_strike m s0 h0 tr) cm, extEnc_congr_tree (tree_strike m s0 h0 tr) cm']

/-! ## The experiment and the bound -/

/-- The verdict: the public algorithm, then the arm at its output d, over the hash function through
the coding at d; with d. -/
def verdPub {D : Type} (V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D)
    (z : OutLA lam L aL) : OComp (rom lam) (D × Bool) :=
  Pub.bind fun d => ((V d z).overOne (m d)).bind fun b => OComp.pure (d, b)

/-- The experiment: the maker runs; then the public algorithm and the arm at its output. -/
def expPub {D : Type} (V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D)
    (Mk : OComp (rom lam) (OutLA lam L aL)) :
    OComp (rom lam) ((OutLA lam L aL × Trace (rom lam)) × D × Bool) :=
  Mk.withTrace.bind fun o => (verdPub V m Pub o.1).bind fun v => OComp.pure (o, v)

/-- An arm that begins with the seed queries, made of public digests that are answers of the hash
function, is sound against every maker over that function: the maker runs; the public algorithm
runs; the arm at its output d runs, through the coding at d; all ask the one function. The arm
accepts, and what it promises fails on the one-block entries, under the coding at d, of the maker's
log of strings, with probability at most n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + tVL) and t
bounds the maker's queries. Premises: those of `arm_pr_maker` at every d of the type D; the public
algorithm has no coins, asks strings of Pt alone and none twice; at every d the arm over the hash
function asks none of Pt, and a string of Pt codes no leaf and no node. m is any family of
codings. -/
theorem arm_pr_pub {D : Type} {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
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
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt s) (t : ℕ) :
    ∀ (Pub : OComp (rom lam) D), Pub.NoCoin → (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
      ∀ (Mk : OComp (rom lam) (OutLA lam L aL)), Mk.QueryBound t →
    Rom.Pr (expPub V m Pub Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds W (singleTr (m x.2.1) x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  intro Pub
  induction Pub with
  | pure d =>
    intro _ _ _ Mk hq
    have e : expPub V m (OComp.pure d) Mk =
        (Mk.withTrace.bind fun o => ((V d o.1).overOne (m d)).bind fun b =>
          OComp.pure (o, b)).bind fun x => OComp.pure (x.1, (d, x.2)) := by
      simp only [expPub, verdPub, OComp.bind_assoc, OComp.bind]
    rw [e, Rom.Pr_bind_pure]
    exact arm_pr_maker hsL hlL hcL hW (hA d) (hSd d) hbL (hV d) (hH d) hlam (m d) Mk t hq
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
      (ih r (hc r) (hp.2 r) (hr r).2 (wire s r Mk) (queryBound_wire s r Mk t hq))
    have hv : ∀ z, (verdPub V m (OComp.query () s k) z).runEager (g.set () s r) =
        (verdPub V m (k r) z).runEager g := by
      intro z
      have h1 : (verdPub V m (OComp.query () s k) z).runEager (g.set () s r) =
          (verdPub V m (k r) z).runEager (g.set () s r) := by
        simp only [verdPub, OComp.bind, OComp.runEager, Fam.set_self]
      rw [h1]
      refine runEager_set s r g _ ?_
      have ha : ∀ d, (((V d z).overOne (m d)).bind fun b =>
          (OComp.pure (d, b) : OComp (rom lam) (D × Bool))).AsksIn fun _ s' => s' ≠ s := by
        intro d
        refine OComp.AsksIn.bind ?_
          (OComp.AsksIn.mono (P := fun _ s' => ¬ Pt s') (Q := fun _ s' => s' ≠ s)
            (fun _ s' h e => h (by rw [e]; exact hp.1)) (hno d z))
        intro _
        trivial
      exact OComp.AsksIn.bind ha (hr r).1
    unfold PrCoins expPub
    rw [OComp.runEager_bind, OComp.runEager_bind, withTrace_wire, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun o _ => ?_
    simp only [Function.comp, OComp.runEager_bind, hv]
    refine pr_bind_le_bind _ _ _ _ _ fun v _ => ?_
    refine pr_pure_le_pure ?_
    rintro ⟨hb, hbad⟩
    exact ⟨hb, fun h => hbad ((linkHolds_strike (m v.1) s (hT v.1 s hp.1) o.2 _ _ _ _).1 h)⟩

/-! ## Two digests, the second on a string made of the first -/

/-- The public algorithm of two digests: c at the string s0, then p at the string s1 c. -/
def pub2 (s0 : List Bool) (s1 : Dig lam → List Bool) : OComp (rom lam) (Dig lam × Dig lam) :=
  (OComp.ask (S := rom lam) () s0).bind fun c =>
    (OComp.ask (S := rom lam) () (s1 c)).bind fun p => OComp.pure (c, p)

/-- the two public strings, at every first digest -/
def Pt2 (s0 : List Bool) (s1 : Dig lam → List Bool) (s : List Bool) : Prop :=
  s = s0 ∨ ∃ c, s = s1 c

/-- `arm_pr_pub` at two digests, the second on a string made of the first. Asked of the two strings:
s1 c is never s0; at every pair d of digests the arm over the hash function asks neither s0 nor any
s1 c, and these code no leaf and no node under the coding at d. The other premises and the bound are
those of `arm_pr_pub`; t bounds the maker's queries. -/
theorem arm_pr_pub2 {S : Dig lam × Dig lam → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : Dig lam × Dig lam → L.OutOfDomainAnswer → List (Dig lam)}
    {V : Dig lam × Dig lam → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hV : ∀ d, IsArm W (S d) (cA d) (V d)) (hH : ∀ d, HeadSeeds W (S d) (V d)) (hlam : 0 < lam)
    (m : Dig lam × Dig lam → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (s0 : List Bool) (s1 : Dig lam → List Bool)
    (hT : ∀ d s, Pt2 s0 s1 s → ((m d).dec s).1 ≠ OracleName.leaf ∧ ((m d).dec s).1 ≠ OracleName.node)
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt2 s0 s1 s)
    (hne : ∀ c, s1 c ≠ s0)
    (Mk : OComp (rom lam) (OutLA lam L aL)) (t : ℕ) (hq : Mk.QueryBound t) :
    Rom.Pr (expPub V m (pub2 s0 s1) Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds W (singleTr (m x.2.1) x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  arm_pr_pub hsL hlL hcL hW hA hSd hbL hV hH hlam m (Pt2 s0 s1) hT hno t (pub2 s0 s1)
    (fun _ _ => trivial) ⟨Or.inl rfl, fun c => ⟨Or.inr ⟨c, rfl⟩, fun _ => trivial⟩⟩
    (fun c => ⟨⟨hne c, fun _ => trivial⟩, fun _ => ⟨trivial, trivial⟩⟩) Mk hq

end TypedOracleCompiler.Compile.Batch.Cms

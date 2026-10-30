-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsKeyPublic.lean: the entry's arm in two stages where the record's wire,
the code of the answers, the arm and the coding hang on public digests that are themselves answers
of the one hash function.

`pub_lift` (PublicLift.lean) at `arm_pr_key` (LinkAnsKeyStage.lean), as KeyAnsPublic.lean has it for
the key's arm. The committer runs and publishes the first root with its record; the prover runs and
names the further root, its record and Link's proof string; then a public algorithm without coins
`Pub` asks the function for the digests, and the arm at its output d runs, through the coding at d.
Both stages may ask the same strings among their calls: a value is wired into both. THE WORD UNDER
THE FIRST ROOT IS READ OFF THE COMMITTER's LOG ALONE; the word under the further root off both logs.
The bound is that of `arm_pr_key`, to the letter.

  `OutKey`, `verdKey`, `expKeyPub`   what the stages put out; the verdict at d; the experiment
  `failsKeyPub`, `badKeyPub`         what the arm promises at d fails; the event
  `strike_append`                    striking from two logs, then joining them
  `arm_pr_key_pub`                   the bound
  `arm_pr_key_pub2`                  at two digests, the second on a string made of the first

What the step beyond `arm_pr_pub` costs. That step is the passage, under the first root, from the
word that both logs determine to the word that the committer's log determines: a prover may hash
under a published root. It adds no term of its own to the bound. The rare event outside which the
word under an announced root stays (`EM`; `extEnc_stable`, OnBytes/TypedOracleCompiler/Compile/Batch/Hash.lean) is a
part of `BadLA` (LinkAns.lean). The bound is a bound on one event: `BadLA` of the lengthened typed
log of the analysis' algorithm `joined2` (`badLA_len_rare`, LinkAnsMore.lean), and `two_lift`
(LinkAnsTwoStage.lean) draws both words' stay from "not `BadLA`". The price is one query more, for
the announcement, in the count that n takes five times. All of that stands in LinkAnsTwoStage.lean
and the files before it; nothing of it is proved anew here.

Link's soundness is a hypothesis (hsL). The premises are those of `arm_pr_pub` and `arm_pr_pub2`
(LinkAnsPublic.lean) but for the makers: there one maker with at most t queries, and both words are
read off its whole log; here a committer and a prover with at most tC and tP.

Limits: those in the heads of LinkAnsKeyStage.lean and LinkAnsPublic.lean, but for the sentence on
what is fixed before the function is drawn, which the first bullet here replaces. Of
LinkAnsPublic.lean's limits the bullet "One maker" does not hold here.
  * The public strings, the object L with its annotations aT and aL, W and the way in which wire,
    code, arm and coding are made of the digests are fixed before the function is drawn: L, aT, aL
    and W do not hang on the digests. So neither stage picks the public strings: a committer that
    writes the public files after asking the function is not covered.
  * Soundness alone. No yes is shown: the bound would hold of an arm that refuses everything.
  * Said for every family of codings that meets the premises. None is built here, and that such a
    family exists is not shown here. All premises are laws of letters here, and that they can be met
    together is not shown here. Elsewhere, for one maker, the arm with the lax Link and lam = 256:
    `closedFull_public` and `closedSmall_public` (Johnson/Top/Pub/ArmPublicFull.lean
    [not in this library], ArmPublicSmall.lean [not in this library]) come from `arm_pr_pub2`,
    through Johnson/Flat/ArmSibPublic.lean and
    Johnson/Top/Pub/ArmPublicAt.lean. `arm_pr_pub2` shares its premises, but
    for the maker's, with `arm_pr_key_pub2`. The two closed theorems ask the theorem on codes and
    the bound on the maker's queries, and no other proposition; the type X and the letters A, R, G,
    P, hL, sX, pol, lay, KL stay.
  * Where the first table decodes to nothing, nothing is said of the further table.
  * The arm's calls and the public algorithm's stand in neither log.
  * n counts the two stages' calls on strings, one query for the announcement of the first root in
    the analysis (the experiment holds no such query), and the arm's typed queries, five times.
  * By the byte format the run's value, a call on the parameters' digest and 32 bytes of the proof
    string, also stands in the arms' calls. It hangs on what a stage puts out, so it is no public
    digest, and this file does not reach it.
  * The bound is an average over the public digests of bounds against committers and provers that
    may hang on them.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.PublicLift
import Johnson.TypedOracleCompiler.RecCompile.ProofAnsPublic
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsKeyStage

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

/-- What the two stages have put out, with their logs of strings: the committer's root, record and
state; the prover's further root, its record and Link's proof string. -/
abbrev OutKey (lam : ℕ) (L : HolographicProtocol I X) (aL : RoundSplits L.link.shape) (St : Type) : Type :=
  (((Dig lam × L.Rec) × St) × Trace (rom lam)) × (Out3 lam L aL × Trace (rom lam))

/-- The entry's arm at d, through the coding at d, on what committer and prover have put out. -/
def verdKey {D St : Type} (V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (d : D) (y : OutKey lam L aL St) :
    OComp (rom lam) Bool :=
  (V d (y.1.1.1.1, y.2.1.1, y.1.1.1.2, y.2.1.2.1, y.2.1.2.2)).overOne (m d)

/-- The experiment over one hash function: the committer, with its log; the prover, handed the
committer's state, with its log; the public algorithm; the arm at its output d. The outcome keeps
what both stages have put out, both logs, d and the arm's bit. -/
def expKeyPub {D St : Type} (V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D)
    (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St)) (Pv : St → OComp (rom lam) (Out3 lam L aL)) :
    OComp (rom lam) (OutKey lam L aL St × D × Bool) :=
  expP (verdKey V m) Pub (run2 Prod.snd (Ct, Pv))

/-- What the arm promises at d fails: of the word that the one-block entries, under the coding at d,
of the committer's own log determine under the first root, and of the word that those of both logs
determine under the further root. -/
def failsKeyPub {D St : Type} (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (d : D)
    (y : OutKey lam L aL St) : Prop :=
  ¬ LinkHoldsAt L (extEnc W (singleTr (m d) y.1.2) y.1.1.1.1)
    (extEnc W (singleTr (m d) (y.1.2 ++ y.2.2)) y.2.1.1) y.1.1.1.2 y.2.1.2.1

/-- The event: the arm accepts, and what it promises at d fails. -/
def badKeyPub {D St : Type} (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) :
    Set (OutKey lam L aL St × D × Bool) :=
  {x | x.2.2 = true ∧ failsKeyPub (W := W) m x.2.1 x.1}

/-- Striking the entries at one string from two logs and joining them is striking them from the
joined log. -/
theorem strike_append (s : List Bool) (tr tr' : Trace (rom lam)) :
    strike s tr ++ strike s tr' = strike s (tr ++ tr') := by
  unfold strike
  rw [List.filter_append]

/-- An arm (`IsArm`, `HeadSeeds`) made of public digests that are answers of the hash function is
sound over that function, in two stages: the committer runs and publishes the first root with its
record; the prover runs and names the further root, its record and Link's proof string; the public
algorithm runs; the arm at its output d runs, through the coding at d; all ask the one function. The
arm accepts, and what it promises fails of the word that the one-block entries, under the coding at
d, of the committer's own log of strings determine under the first root and of the word that those
of both logs determine under the further root, with probability at most n εs + 2 (n + 1)² / 2^lam,
where n = 5 (tC + tP + 1 + tVL); tC bounds the committer's calls (hC) and tP the prover's at every
state (hP). Premises: those of `arm_pr_key` at every d of the type D, reached by the public
algorithm or not; the public algorithm has no coins, asks strings of Pt alone and none twice; at
every d the arm over the hash function asks none of Pt, and a string of Pt codes no leaf and no
node. m is any family of codings that meets these. -/
theorem arm_pr_key_pub {D : Type} {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
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
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pv : St → OComp (rom lam) (Out3 lam L aL)) (tC tP : ℕ) (hC : Ct.QueryBound tC)
    (hP : ∀ st, (Pv st).QueryBound tP) :
    Rom.Pr (expKeyPub V m Pub Ct Pv) (fun _ => badKeyPub (W := W) m) ≤
      (((tC + tP + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine pub_lift
    (M := OComp (rom lam) ((Dig lam × L.Rec) × St) × (St → OComp (rom lam) (Out3 lam L aL)))
    (run2 Prod.snd) wire2 strike2 (fun s r M g => run2_wire Prod.snd s r M g)
    (fun M => M.1.QueryBound tC ∧ ∀ st, (M.2 st).QueryBound tP)
    (fun s r M h => ⟨queryBound_wire s r M.1 tC h.1, fun st => queryBound_wire s r _ tP (h.2 st)⟩)
    (verdKey V m) (fun _ _ _ => rfl) Pt (fun d y => hno d _) (failsKeyPub (W := W) m)
    (fun d s y hs hb => by
      show ¬ LinkHoldsAt L (extEnc W (singleTr (m d) (strike s y.1.2)) y.1.1.1.1)
        (extEnc W (singleTr (m d) (strike s y.1.2 ++ strike s y.2.2)) y.2.1.1) y.1.1.1.2 y.2.1.2.1
      rw [strike_append, extEnc_strike (m d) s (hT d s hs), extEnc_strike (m d) s (hT d s hs)]
      exact hb) _ ?_ Pub hPc hPa hPr (Ct, Pv) ⟨hC, hP⟩
  rintro d ⟨Ct, Pv⟩ ⟨hC, hP⟩
  have e : expD (verdKey V m) d (run2 Prod.snd (Ct, Pv)) =
      (exp3 W (V d) (m d) Ct Pv).bind fun x => OComp.pure ((x.1, x.2.1), (d, x.2.2)) := by
    simp only [expD, exp3, verdKey, run2, OComp.bind_assoc, OComp.bind]
  rw [e, Rom.Pr_bind_pure]
  exact arm_pr_key hsL hlL hcL hW (hA d) (hSd d) hbL (hV d) (hH d) hlam (m d) Ct Pv tC tP hC hP

/-- `arm_pr_key_pub` at two digests, the second on a string made of the first. Asked of the two
strings: s1 c is never s0; at every pair d of digests the arm over the hash function asks neither s0
nor any s1 c, and these code no leaf and no node under the coding at d. The other premises and the
bound are those of `arm_pr_key_pub`. -/
theorem arm_pr_key_pub2 {S : Dig lam × Dig lam → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
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
    (hne : ∀ c, s1 c ≠ s0) {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pv : St → OComp (rom lam) (Out3 lam L aL)) (tC tP : ℕ) (hC : Ct.QueryBound tC)
    (hP : ∀ st, (Pv st).QueryBound tP) :
    Rom.Pr (expKeyPub V m (pub2 s0 s1) Ct Pv) (fun _ => badKeyPub (W := W) m) ≤
      (((tC + tP + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  arm_pr_key_pub hsL hlL hcL hW hA hSd hbL hV hH hlam m (Pt2 s0 s1) hT hno (pub2 s0 s1)
    (fun _ _ => trivial) ⟨Or.inl rfl, fun c => ⟨Or.inr ⟨c, rfl⟩, fun _ => trivial⟩⟩
    (fun c => ⟨⟨hne c, fun _ => trivial⟩, fun _ => ⟨trivial, trivial⟩⟩) Ct Pv tC tP hC hP

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.arm_pr_key_pub
#print axioms TypedOracleCompiler.Compile.Batch.Cms.arm_pr_key_pub2

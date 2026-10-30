-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/ThreeArmsPublic.lean: the three arms in one experiment (ThreeArms.lean) where
the record's wire, the code of the answers, the three arms and their three codings hang on public
digests that are themselves answers of the one hash function.

`pub_lift` (PublicLift.lean) at `three_arms`. The committer runs and publishes the first root with
its record; the prover runs and names the three proof strings, the further root with its record, and
an instance; then a public algorithm without coins `Pub` asks the function for the digests, and the
three arms at its output d run, each through its own coding at d. Both stages may ask the same
strings among their calls. The bound is that of `three_arms`, to the letter.

  `verd3`             the three arms' verdicts, joined
  `three_arms_pub`    the bound

The soundness of each of the three protocols is a hypothesis (hsT, hsL, hsB). Pt is the set of
public strings here (in ThreeArms.lean and KeyAnsStage.lean the letter names the prover).

Limits: those in the heads of ThreeArms.lean and LinkAnsPublic.lean, but for the sentence on what is
fixed before the function is drawn, which the first bullet here replaces. Of LinkAnsPublic.lean's
limits the bullet "One maker" does not hold here.
  * The public strings, the object L with its annotations aT and aL, W, r₀ and the way in which
    wire, code, arms and codings are made of the digests are fixed before the function is drawn: L,
    aT, aL and W do not hang on the digests. So neither stage picks the public strings: a committer
    that writes the public files after asking the function is not covered.
  * Soundness alone. No yes is shown: the bound would hold of arms that refuse everything.
  * 34 premises: the 27 of `three_arms`, nine of them now at every d, and seven on the public
    strings. All are laws of letters here. That they can be met together is not shown; until it is,
    the theorem may be true and empty.
  * Said for every three families of codings that meet the premises. None is built, and that such
    families exist is not shown.
  * The premises on Pt are paid for no arm here. `hno_armTL` and its like pay them for one coding at
    "codes a point of the spare oracle"; that the public strings do so under all three codings at
    every d stays a premise.
  * These are the three arms, not the whole compiled verifier.
  * Not lifted: `three_arms_holds`, `two_arms` and `arm_pr_two` on their own, and the theorems in
    two stages at a written object: they still fix the digests before the function is drawn.
    `arm_pr_key` on its own is lifted in LinkAnsKeyPublic.lean (`arm_pr_key_pub`).
  * By the byte format the run's value, a call on the parameters' digest and 32 bytes of the proof
    string, also stands in the arms' calls. It hangs on what a stage puts out, so it is no public
    digest, and this file does not reach it.
  * The bound is an average over the public digests of bounds against committers and provers that
    may hang on them.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.ThreeArms
import Johnson.TypedOracleCompiler.RecCompile.KeyAnsPublic

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

/-- The three arms at d, each through its own coding at d, on what committer and prover have put
out: yes if all three say yes. -/
def verd3 {D St : Type} (VT : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VL : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VB : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (mT mL mB : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (d : D)
    (y : (((Dig lam × L.Rec) × St) × Trace (rom lam)) × (OutP3 lam L aT aL × Trace (rom lam))) :
        OComp (rom lam) Bool :=
  ((VT d (y.1.1.1.1, y.1.1.1.2, y.2.1.1)).overOne (mT d)).bind fun vT =>
  ((VL d (y.1.1.1.1, y.2.1.2.1.1, y.1.1.1.2, y.2.1.2.1.2.1, y.2.1.2.1.2.2)).overOne
    (mL d)).bind fun vL =>
  ((VB d (y.2.1.2.1.1, y.2.1.2.2.1, y.2.1.2.1.2.1, y.2.1.2.2.2)).overOne (mB d)).bind fun vB =>
    OComp.pure (vT && vL && vB)

/-- All three arms, made of public digests that are answers of the hash function, accept, and the
committer's word does not decode to an index for which the instance that the prover names has a
witness: with probability at most the sum of three bounds, each of the form
n εs + 2 (n + 1)² / 2^lam: at n = 3 (tC + tP + 1 + tVT), at n = 5 (tC + tP + 1 + tVL) and at
n = 3 (tC + tP + tVB); tC bounds the committer's calls (hC) and tP the prover's at every state (hP).
The word is the one that the one-block entries, under the key's arm's coding at d, of the
committer's own log of strings determine under the first root; the record is the committer's. The
premises are those of `armT_pr_key` (hsT, hlT, hcT, `OKTA W`, hbT, `IsArmT`), of `arm_pr_key` (hsL,
hlL, hcL, `OKLA W`, hbL, `IsArm`, `HeadSeeds`) and of `armB_pr_maker` (hsB, hlB, hco, `OKBA W`, hbB,
`IsArmB`, `HeadSeedB`), at one `AnsOK`, one `S.Law εs` and lam not 0, and that mL and mB agree with
mT on the leaf and node oracles (`SameTrees`): those that name S, cA, an arm or a coding at every d
of the type D, reached by the public algorithm or not. The public algorithm has no coins, asks
strings of Pt alone and none twice; at every d none of the three arms over the hash function asks a
string of Pt, and a string of Pt codes no leaf and no node under the key's arm's coding. -/
theorem three_arms_pub {Wn D : Type} (Rno : I → X → Wn → Prop)
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
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pv : St → OComp (rom lam) (OutP3 lam L aT aL))
    (tC tP : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ st, (Pv st).QueryBound tP) :
    Rom.Pr (expP (verd3 VT VL VB mT mL mB) Pub (run2 Prod.snd (Ct, Pv)))
        (fun _ => {x | x.2.2 = true ∧
          ¬ ∃ i, L.decodeIndex (extEnc W (singleTr (mT x.2.1) x.1.1.2) x.1.1.1.1.1) x.1.1.1.1.2 = some i ∧
            ∃ w, Rno i x.1.2.1.2.2.1 w}) ≤
      ((((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      (((((tC + tP + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      ((((tC + tP + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam)) := by
  refine pub_lift
    (M := OComp (rom lam) ((Dig lam × L.Rec) × St) × (St → OComp (rom lam) (OutP3 lam L aT aL)))
    (run2 Prod.snd) wire2 strike2 (fun s r M g => run2_wire Prod.snd s r M g)
    (fun M => M.1.QueryBound tC ∧ ∀ st, (M.2 st).QueryBound tP)
    (fun s r M h => ⟨queryBound_wire s r M.1 tC h.1, fun st => queryBound_wire s r _ tP (h.2 st)⟩)
    (verd3 VT VL VB mT mL mB) (fun _ _ _ => rfl) Pt ?_
    (fun d y => ¬ ∃ i, L.decodeIndex (extEnc W (singleTr (mT d) y.1.2) y.1.1.1.1) y.1.1.1.2 = some i ∧
      ∃ w, Rno i y.2.1.2.2.1 w)
    (fun d s y hs hb => by
      show ¬ ∃ i, L.decodeIndex (extEnc W (singleTr (mT d) (strike s y.1.2)) y.1.1.1.1) y.1.1.1.2 =
        some i ∧ ∃ w, Rno i y.2.1.2.2.1 w
      rw [extEnc_strike (mT d) s (hT d s hs)]
      exact hb) _ ?_ Pub hPc hPa hPr (Ct, Pv) ⟨hC, hP⟩
  · intro d y
    unfold verd3
    refine OComp.AsksIn.bind ?_ (hnoT d _)
    intro _
    refine OComp.AsksIn.bind ?_ (hnoL d _)
    intro _
    refine OComp.AsksIn.bind ?_ (hnoB d _)
    intro _
    trivial
  · rintro d ⟨Ct, Pv⟩ ⟨hC, hP⟩
    have e : expD (verd3 VT VL VB mT mL mB) d (run2 Prod.snd (Ct, Pv)) =
        (exp3A W (VT d) (VL d) (VB d) (mT d) (mL d) (mB d) Ct Pv).bind fun x =>
          OComp.pure ((x.1, x.2.1), (d, x.2.2.1 && x.2.2.2.1 && x.2.2.2.2)) := by
      simp only [expD, exp3A, verd3, run2, OComp.bind_assoc, OComp.bind]
    rw [e, Rom.Pr_bind_pure]
    refine le_trans (Pr_mono _ fun _ x hx => ?_)
      (three_arms Rno wit hsT hlT hcT hWT hbT (hVT d) hsL hlL hcL hWL hbL (hVL d) (hHL d) hsB hlB
        hco hWB hbB (hVB d) (hHB d) (hA d) (hSd d) hlam (mT d) (mL d) (mB d) (hmL d) (hmB d) Ct Pv
        tC tP hC hP)
    obtain ⟨h1, h2⟩ := hx
    have h1' : (x.2.2.1 && x.2.2.2.1 && x.2.2.2.2) = true := h1
    simp only [Bool.and_eq_true] at h1'
    exact ⟨h1'.1.1, h1'.1.2, h1'.2, h2⟩

end TypedOracleCompiler.Compile.Batch.Cms

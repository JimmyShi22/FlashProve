-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/KeyAnsPublic.lean: the key's arm in two stages where the record's wire, the
code of the answers, the arm and the coding hang on public digests that are themselves answers of
the one hash function.

`pub_lift` (PublicLift.lean) at `armT_pr_key` (KeyAnsStage.lean). The committer runs and publishes a
root with its record; the prover runs and names Test's proof string; then a public algorithm without
coins `Pub` asks the function for the digests, and the arm at its output d runs, through the coding
at d. Both stages may ask the same strings among their calls: a value is wired into both. The bound
is that of `armT_pr_key`, to the letter.

  `asksIn_armTL`, `asksIn_armTS`, `hno_armTL`, `hno_armTS`   the two arms ask no point of the spare
                    oracle
  `armT_pr_key_pub`   the bound

Test's soundness is a hypothesis (hsT).

Limits: those in the heads of KeyAnsStage.lean and LinkAnsPublic.lean, but for the sentence on what
is fixed before the function is drawn, which the first bullet here replaces. Of LinkAnsPublic.lean's
limits the bullet "One maker" does not hold here.
  * The public strings, the object L with its annotations aT and aL, W and the way in which wire,
    code, arm and coding are made of the digests are fixed before the function is drawn: L, aT, aL
    and W do not hang on the digests. So neither stage picks the public strings: a committer that
    writes the public files after asking the function is not covered.
  * Soundness alone. No yes is shown: the bound would hold of an arm that refuses everything.
  * Said for every family of codings that meets the premises. None is built, and that such a family
    exists is not shown.
  * By the byte format the run's value, a call on the parameters' digest and 32 bytes of the proof
    string, also stands in the arms' calls. It hangs on what a stage puts out, so it is no public
    digest, and this file does not reach it.
  * The bound is an average over the public digests of bounds against committers and provers that
    may hang on them.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.PublicLift
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublicArm
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

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-- The arm with the lax Test asks no point of the spare oracle. -/
theorem asksIn_armTL (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam))
    (z : OutTA lam L aT) : (armTL W S cA z).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  show (VTA' W S cA z.1 z.2.1 z.2.2).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL))
  unfold VTA'
  refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
  intro _
  refine OComp.AsksIn.bind ?_
    (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyB _ _ _ _ _ _ _ _ _ _ _))
  intro _
  trivial

/-- The arm with the strict Test asks no point of the spare oracle. -/
theorem asksIn_armTS (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params)
    (z : OutTA lam L aT) : (armTS W S cA p z).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  show (VTA W S cA p z.1 z.2.1 z.2.2).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL))
  unfold VTA
  refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
  intro _
  refine OComp.AsksIn.bind ?_
    (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
  intro _
  trivial

/-- Over the hash function the arm with the lax Test asks no string that codes a point of the spare
oracle. -/
theorem hno_armTL (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (z : OutTA lam L aT) :
    ((armTL W S cA z).overOne m).AsksIn fun _ s => ¬ IsOther m s :=
  asksIn_overOne m (NotOther lam (typedOracleCarrier L Bd aT aL)) _ (asksIn_armTL S cA z)

/-- The same of the arm with the strict Test. -/
theorem hno_armTS (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params)
    (z : OutTA lam L aT) : ((armTS W S cA p z).overOne m).AsksIn fun _ s => ¬ IsOther m s :=
  asksIn_overOne m (NotOther lam (typedOracleCarrier L Bd aT aL)) _ (asksIn_armTS S cA p z)

/-- An arm (`IsArmT`) made of public digests that are answers of the hash function is sound over
that function, in two stages: the committer runs and publishes a root with its record; the prover
runs and names Test's proof string; the public algorithm runs; the arm at its output d runs, through
the coding at d; all ask the one function. The arm accepts, and what it promises fails of the word
that the one-block entries, under the coding at d, of the committer's own log of strings determine
under the root, with probability at most n εs + 2 (n + 1)² / 2^lam, where n = 3 (tC + tP + 1 + tVT);
tC bounds the committer's calls (hC) and tP the prover's at every state (hP). Premises: those of
`armT_pr_key` at every d of the type D, reached by the public algorithm or not; the public algorithm
has no coins, asks strings of Pt alone and none twice; at every d the arm over the hash function
asks none of Pt, and a string of Pt codes no leaf and no node. m is any family of codings. -/
theorem armT_pr_key_pub {D : Type} {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : D → L.OutOfDomainAnswer → List (Dig lam)}
    {V : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {εT : Err L.offline.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hV : ∀ d, IsArmT W (S d) (cA d) (V d)) (hlam : 0 < lam)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hT : ∀ d s, Pt s → ((m d).dec s).1 ≠ OracleName.leaf ∧ ((m d).dec s).1 ≠ OracleName.node)
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt s)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pv : St → OComp (rom lam) (OneProtocolProof lam (batTC L aT))) (tC tP : ℕ) (hC : Ct.QueryBound tC)
    (hP : ∀ st, (Pv st).QueryBound tP) :
    Rom.Pr (expP (fun d (y : (((Dig lam × L.Rec) × St) × Trace (rom lam)) ×
          (OneProtocolProof lam (batTC L aT) × Trace (rom lam))) =>
          (V d (y.1.1.1.1, y.1.1.1.2, y.2.1)).overOne (m d)) Pub (run2 Prod.snd (Ct, Pv)))
        (fun _ => {x | x.2.2 = true ∧
          ¬ KeyHoldsAt L (extEnc W (singleTr (m x.2.1) x.1.1.2) x.1.1.1.1.1) x.1.1.1.1.2}) ≤
      (((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine pub_lift
    (M := OComp (rom lam) ((Dig lam × L.Rec) × St) ×
      (St → OComp (rom lam) (OneProtocolProof lam (batTC L aT))))
    (run2 Prod.snd) wire2 strike2 (fun s r M g => run2_wire Prod.snd s r M g)
    (fun M => M.1.QueryBound tC ∧ ∀ st, (M.2 st).QueryBound tP)
    (fun s r M h => ⟨queryBound_wire s r M.1 tC h.1, fun st => queryBound_wire s r _ tP (h.2 st)⟩)
    (fun d y => (V d (y.1.1.1.1, y.1.1.1.2, y.2.1)).overOne (m d)) (fun _ _ _ => rfl) Pt
    (fun d y => hno d _)
    (fun d y => ¬ KeyHoldsAt L (extEnc W (singleTr (m d) y.1.2) y.1.1.1.1) y.1.1.1.2)
    (fun d s y hs hb => by
      show ¬ KeyHoldsAt L (extEnc W (singleTr (m d) (strike s y.1.2)) y.1.1.1.1) y.1.1.1.2
      rw [extEnc_strike (m d) s (hT d s hs)]
      exact hb) _ ?_ Pub hPc hPa hPr (Ct, Pv) ⟨hC, hP⟩
  rintro d ⟨Ct, Pv⟩ ⟨hC, hP⟩
  have e : expD (fun d (y : (((Dig lam × L.Rec) × St) × Trace (rom lam)) ×
        (OneProtocolProof lam (batTC L aT) × Trace (rom lam))) =>
        (V d (y.1.1.1.1, y.1.1.1.2, y.2.1)).overOne (m d)) d (run2 Prod.snd (Ct, Pv)) =
      (expT W (V d) (m d) Ct Pv).bind fun x => OComp.pure ((x.1, x.2.1), (d, x.2.2)) := by
    simp only [expD, expT, run2, OComp.bind_assoc, OComp.bind]
  rw [e, Rom.Pr_bind_pure]
  exact armT_pr_key hsT hlT hcT hW (hA d) (hSd d) hbT (hV d) hlam (m d) Ct Pv tC tP hC hP

end TypedOracleCompiler.Compile.Batch.Cms

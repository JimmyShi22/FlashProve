-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/ProofAnsPublic.lean: the proof's arm where the record's wire, the code of the
answers, the arm and the coding hang on public digests that are themselves answers of the one hash
function.

`pub_lift` (PublicLift.lean) at `armB_pr_maker` (ProofAnsStage.lean): as `arm_pr_pub`
(LinkAnsPublic.lean) for the entry's arm. A public algorithm without coins `Pub` asks the function
for the digests; wire, code, arm and coding are families over its output d; in the experiment the
arm runs `Pub` itself, behind the maker. The maker may ask the same strings among its calls. The
bound is that of `armB_pr_maker`, to the letter.

  `asksIn_armBL`, `asksIn_armBS`, `hno_armBL`, `hno_armBS`   the two arms ask no point of the spare
                    oracle
  `extEnc_strike`   the word under a root does not see a struck entry
  `armB_pr_pub`     the bound

The session's soundness is a hypothesis (hsB).

Limits: those in the heads of ProofAnsStage.lean and LinkAnsPublic.lean, but for the sentence on
what is fixed before the function is drawn, which the first bullet here replaces.
  * The public strings, the object L with its annotations aT and aL, W, r₀ and the way in which
    wire, code, arm and coding are made of the digests are fixed before the function is drawn: L,
    aT, aL and W do not hang on the digests. So the maker does not pick the public strings: a maker
    that writes the public files after asking the function is not covered.
  * Soundness alone. No yes is shown: the bound would hold of an arm that refuses everything.
  * Said for every family of codings that meets the premises. None is built, and that such a family
    exists is not shown.
  * By the byte format the run's value, a call on the parameters' digest and 32 bytes of the proof
    string, also stands in the arm's calls. It hangs on what the maker puts out, so it is no public
    digest, and this file does not reach it.
  * The bound is an average over the public digests of bounds against makers that may hang on them.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.PublicLift
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublicArm
import Johnson.TypedOracleCompiler.RecCompile.ProofAnsStage

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

/-- The arm with the lax session asks no point of the spare oracle. -/
theorem asksIn_armBL (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
    (z : OutBA lam L) : (armBL W S cA r₀ z).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  show (VBA' W S cA r₀ z.1 z.2.1 z.2.2.1 z.2.2.2).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL))
  unfold VBA'
  refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
  intro _
  refine OComp.AsksIn.bind ?_
    (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyB _ _ _ _ _ _ _ _ _ _ _))
  intro _
  trivial

/-- The arm with the strict session asks no point of the spare oracle. -/
theorem asksIn_armBS (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
    (p : Params) (z : OutBA lam L) :
    (armBS W S cA r₀ p z).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  show (VBA W S cA r₀ p z.1 z.2.1 z.2.2.1 z.2.2.2).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL))
  unfold VBA
  refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
  intro _
  refine OComp.AsksIn.bind ?_
    (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
  intro _
  trivial

/-- Over the hash function the arm with the lax session asks no string that codes a point of the
spare oracle. -/
theorem hno_armBL (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
    (z : OutBA lam L) : ((armBL W S cA r₀ z).overOne m).AsksIn fun _ s => ¬ IsOther m s :=
  asksIn_overOne m (NotOther lam (typedOracleCarrier L Bd aT aL)) _ (asksIn_armBL S cA r₀ z)

/-- The same of the arm with the strict session. -/
theorem hno_armBS (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params)
    (z : OutBA lam L) : ((armBS W S cA r₀ p z).overOne m).AsksIn fun _ s => ¬ IsOther m s :=
  asksIn_overOne m (NotOther lam (typedOracleCarrier L Bd aT aL)) _ (asksIn_armBS S cA r₀ p z)

/-- The word under a root is not moved when the entries at a string that codes no leaf and no node
are struck from the log of strings. -/
theorem extEnc_strike (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s0 : List Bool)
    (h0 : (m.dec s0).1 ≠ OracleName.leaf ∧ (m.dec s0).1 ≠ OracleName.node) (tr : Trace (rom lam))
    (cm : Dig lam) :
    extEnc W (singleTr m (strike s0 tr)) cm = extEnc W (singleTr m tr) cm :=
  extEnc_congr_tree (tree_strike m s0 h0 tr) cm

/-- An arm (`IsArmB`, `HeadSeedB`) made of public digests that are answers of the hash function is
sound against every maker over that function: the maker runs; the public algorithm runs; the arm at
its output d runs, through the coding at d; all ask the one function. The arm accepts, and what it
promises fails of the word that the one-block entries, under the coding at d, of the maker's log of
strings determine under the root, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 3 (t + tVB) and t bounds the maker's calls (hq). Premises: those of `armB_pr_maker` at every d
of the type D, reached by the public algorithm or not; the public algorithm has no coins, asks
strings of Pt alone and none twice; at every d the arm over the hash function asks none of Pt, and a
string of Pt codes no leaf and no node. m is any family of codings. -/
theorem armB_pr_pub {Wn D : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs) (hbB : Err.Below εB εs)
    {V : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d)) (hH : ∀ d, HeadSeedB W (S d) (V d))
    (hlam : 0 < lam) (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pt : List Bool → Prop)
    (hT : ∀ d s, Pt s → ((m d).dec s).1 ≠ OracleName.leaf ∧ ((m d).dec s).1 ≠ OracleName.node)
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt s)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) (Mk : OComp (rom lam) (OutBA lam L)) (t : ℕ) (hq : Mk.QueryBound t) :
    Rom.Pr (expP (fun d (y : OutBA lam L × Trace (rom lam)) => (V d y.1).overOne (m d)) Pub
        Mk.withTrace)
        (fun _ => {x | x.2.2 = true ∧
          ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w)
            (extEnc W (singleTr (m x.2.1) x.1.2) x.1.1.1) x.1.1.2.1 x.1.1.2.2.1}) ≤
      (((t + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine pub_lift (M := OComp (rom lam) (OutBA lam L)) (fun Mk => Mk.withTrace) wire
    (fun s y => (y.1, strike s y.2)) (fun s r Mk g => withTrace_wire s r g Mk)
    (fun Mk => Mk.QueryBound t) (fun s r Mk h => queryBound_wire s r Mk t h)
    (fun d y => (V d y.1).overOne (m d)) (fun _ _ _ => rfl) Pt (fun d y => hno d y.1)
    (fun d y => ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w)
      (extEnc W (singleTr (m d) y.2) y.1.1) y.1.2.1 y.1.2.2.1)
    (fun d s y hs hb => by
      show ¬ ProofHoldsAt L _ (extEnc W (singleTr (m d) (strike s y.2)) y.1.1) y.1.2.1 y.1.2.2.1
      rw [extEnc_strike (m d) s (hT d s hs)]
      exact hb) _ ?_ Pub hPc hPa hPr Mk hq
  intro d Mk hq
  have e : expD (fun d (y : OutBA lam L × Trace (rom lam)) => (V d y.1).overOne (m d)) d
      Mk.withTrace = (expB W (V d) (m d) Mk).bind fun x => OComp.pure (x.1, (d, x.2)) := by
    simp only [expD, expB, OComp.bind_assoc, OComp.bind]
  rw [e, Rom.Pr_bind_pure]
  exact armB_pr_maker Rno wit hsB hlB hco hW (hA d) (hSd d) hbB (hV d) (hH d) hlam (m d) Mk t hq

end TypedOracleCompiler.Compile.Batch.Cms

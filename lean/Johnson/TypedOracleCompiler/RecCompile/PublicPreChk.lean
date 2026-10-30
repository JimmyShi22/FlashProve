-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/PublicPreChk.lean: the experiments of PublicPre.lean and ThreeArmsChk.lean
run the checks `chkPub` and `chk3`.

The bounds `arm_pr_chk_joint`, `arm_pr_chk` (PublicPre.lean) and `three_arms_chk`
(ThreeArmsChk.lean) are said of experiments that keep logs and what the reading has made, so that
their events can be said. Here: with the logs and these values dropped, under every hash function,
such an experiment is the makers' part and then the check as one term on what that part has put out.

  `bind_withTrace_fst`   what does not read an algorithm's log can be run behind the algorithm
                    itself
  `expChk_chkPub`        `expChk`, its logs dropped, is the author and then `chkPub`
  `exp3Chk_chk3`         `exp3Chk`, its logs dropped, is the committer, the prover and then `chk3`

Limits: two equations between laws of outcomes, at every fixed function, over the coins.
  * No probability is bounded here, and no form with `Rom.Pr` is stated.
  * Kept on the left: what the makers have put out for the check, and the verdict. The events of the
    three bounds read logs and what the reading has made, which are dropped here: they cannot be
    said of the checks' answers alone.
  * The limits in the heads of PublicPre.lean and ThreeArmsChk.lean hold.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.ThreeArmsChk

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

/-- What does not read an algorithm's log can be run behind the algorithm itself. -/
theorem bind_withTrace_fst {Sp : OSpec} {α β : Type} (g : Fam Sp) (c : OComp Sp α)
    (F : α → PMF β) :
    (c.withTrace.runEager g).bind (fun o => F o.1) = (c.runEager g).bind F := by
  rw [← runEager_withTrace_fst g c, PMF.bind_map]
  rfl

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-- Under every hash function: the experiment `expChk`, of whose outcome what the author has put out
and the verdict are kept, is the author and then the check `chkPub` on what the author has put
out. -/
theorem expChk_chkPub {D U : Type}
    (V : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pre : D → U → OComp (rom lam) (Option (OutLA lam L aL))) (Pub : OComp (rom lam) D)
    (Mk : OComp (rom lam) U) (g : Fam (rom lam)) :
    ((expChk V m Pre Pub Mk).runEager g).map (fun x => (x.1.1, x.2.2.2)) =
      (Mk.bind fun u => (chkPub V m Pre Pub u).bind fun b => OComp.pure (u, b)).runEager g := by
  unfold expChk expPR verdPR chkRes chkPub
  simp only [OComp.runEager_bind, OComp.runEager, PMF.map_bind, PMF.pure_map, PMF.bind_bind,
    PMF.pure_bind]
  rw [← bind_withTrace_fst g Mk]
  refine congrArg _ (funext fun o => ?_)
  refine congrArg _ (funext fun d => ?_)
  rw [← bind_withTrace_fst g (Pre d o.1)]

/-- Under every hash function: the experiment `exp3Chk`, of whose outcome the committer's root and
record, what the prover has put out and the verdict are kept, is the committer, the prover and then
the check `chk3`. -/
theorem exp3Chk_chk3 {D U St : Type}
    (VT : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VL : D → OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VB : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (mT mL mB : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pre : D → Dig lam × L.Rec → U → OComp (rom lam) (Option (OutP3 lam L aT aL)))
    (Pub : OComp (rom lam) D) (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pv : (Dig lam × L.Rec) × St → OComp (rom lam) U) (g : Fam (rom lam)) :
    ((exp3Chk VT VL VB mT mL mB Pre Pub Ct Pv).runEager g).map
        (fun x => (x.1.1.1.1, x.1.2.1, x.2.2.2)) =
      (Ct.bind fun a => (Pv a).bind fun u =>
        (chk3 VT VL VB mT mL mB Pre Pub a.1 u).bind fun b => OComp.pure (a.1, u, b)).runEager g :=
            by
  unfold exp3Chk expPR verdPR chk3Res chk3 run2
  simp only [OComp.runEager_bind, OComp.runEager, PMF.map_bind, PMF.pure_map, PMF.bind_bind,
    PMF.pure_bind, id]
  rw [← bind_withTrace_fst g Ct]
  refine congrArg _ (funext fun a => ?_)
  rw [← bind_withTrace_fst g (Pv a.1)]

end TypedOracleCompiler.Compile.Batch.Cms

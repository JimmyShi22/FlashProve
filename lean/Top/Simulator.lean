-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/Simulator.lean: the simulator of one protocol after its challenges are derived through
  samplers (in the scheme: from hash blocks). (Terms: lean/GLOSSARY.md.)

  For a protocol `Q` and samplers `σ`, `Q.pull σ` (Iop/Pull.lean) is `Q` with each challenge
  replaced by a preimage under its sampler.
    `simPull`       For a simulator `Sim` of `Q` (`Lifetime.SimOf`, Compile/Life.lean),
                    `simPull σ Sim` runs `Sim` at the verifier randomness `Rho.push σ ρ` and
                    translates its output (`DView.pull σ`; `none` stays `none`).
    `simPull_good`  For an honest prover `H` and samplers with `Samplers.Good κ K`: if, at w and x,
                    the honest output differs from `Sim`'s (given the honest external answers) on a
                    set of ρ of probability at most z, then after the pull it differs from
                    `simPull σ Sim`'s on a set of probability at most K · z.
  Top/ProgDraw.lean uses them in `simsD` and `simsD_good`, for the protocols Test and Link; the
  counterpart for Batch is in Iop/BatchPullNamed.lean.

  Notation: `Samplers.Good κ K`: every fibre has at most w elements (w: `Sampler.w`); for each round
  w · card Chal ≤ κ · card Src; the product of these ratios over all rounds is at most K
  (Iop/Pull.lean); external answers: the symbols of the external strings where the verifier reads
  them (`InteractiveOracleProof.extAns`, Iop/InteractiveOracleProof.lean).

  Limits: No simulator of a scheme is here, and no instance. `simPull` is a term with a theorem
  about it, not a program: nothing is said on whether it can be run.
-/
import Rom.ExitPriv
import Iop.WireOf
import Iop.PullProofs
import Code.FieldEnum
import ZKCP.Defs
import Mathlib.Data.Matrix.Mul
import Code.RS
import Code.Field
import Iop.Univ
import Blocks.Opens
import Blocks.Numbering
import Blocks.LowerKit
import Blocks.SerS
import Iop.WireOK
import Blocks.Small
import Blocks.Leaves
import Blocks.ErrSup
import Blocks.LevelAcc
import Blocks.LevelLocal
import Blocks.LevelSound
import Blocks.LinkHVZK_rs
import Blocks.LinkSound
import Blocks.Reads
import Compile.CompleteStrict
import Compile.CompleteUnif
import Compile.GlueBinding
import Compile.GluePrivacy
import Compile.HashEvents
import Compile.LifeStar
import Compile.Local
import Iop.RbrLast
import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Fin.Basic
import ZKCP.Special
import Compile.DisciplineWorld
import Compile.Step1_defc_Prob
import Compile.Step1_life2_Erase
import Prob.Tail
import Rom.Forget
import Rom.HopCost
import Rom.UpToBad

noncomputable section

namespace Top.R0
open Iop Rom Compile Prob Code
open scoped ENNReal

section Pull
variable {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} {Wt : Type}

/-- The simulator of `Q.pull σ`: run `Sim` at `Rho.push σ ρ` and translate its output by
`DView.pull σ`. -/
def simPull (σ : Samplers Q.shape) (Sim : Lifetime.SimOf Q) : Lifetime.SimOf (Q.pull σ) :=
  fun x ρ a => (Sim x (Rho.push σ ρ) a).map (Option.map (DView.pull σ))

theorem simPull_good {H : Honest Q Wt} {σ : Samplers Q.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K)
    (Sim : Lifetime.SimOf Q) (w : Wt) (x : X) {z : ℝ≥0∞}
    (h : prRho {ρ | H.output w x ρ ≠ Sim x ρ (Q.extAns x ρ (H.ext w))} ≤ z) :
    prRho {ρ | (H.pull σ).output w x ρ ≠
          simPull σ Sim x ρ ((Q.pull σ).extAns x ρ ((H.pull σ).ext w))} ≤ K * z := by
  refine le_trans (pr_mono _ ?_) ((prRho_preimage_le hσ _).trans (by gcongr))
  intro ρ hρ heq
  apply hρ
  rw [Honest.output_pull, heq]
  rfl

end Pull

end Top.R0

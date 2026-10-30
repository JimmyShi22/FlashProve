-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/ProgDraw.lean: the simulators of single sessions of Test, Link and Batch after challenges are
derived from hash blocks, for any record of protocols `L` and challenge samplers `dr : L.Draws lam`,
one sampler for each round. (Terms: lean/GLOSSARY.md.)
  `simsD`, `simsD_good`:
      the simulators for `LBd lam L dr` (Top/BatchDraw.lean), from those of `L`; so an instance
      supplies only the simulators of its interactive protocols.
Limits: This file defines no scheme and states no theorem on a scheme.
-/
import Top.BatchDraw
import Top.Prog
import Blocks.Batch.Fmt
import Blocks.Batch.Numbering
import Iop.BatchPullNamed
import Top.Simulator

noncomputable section

namespace Top.ProgDraw
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.Prog
open Compile.BatchLife (Sims)
open Compile.Seed (blocksStd)
open scoped ENNReal

variable {I X : Type} (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
  (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
  (dr : L.Draws lam) (ax : L.Aux pT pL pB) (p : Params) (D : SerLHB L)




variable {Ryes Rno : I → X → Prop} {M : LH.Nums} {κ₀ : ℝ≥0∞} {n : ℕ}

/-- The simulators of single sessions for `LBd lam L dr`, from those of `L`. -/
def simsD (Sm : Sims L) : Sims (LBd lam L dr) :=
  ⟨Top.R0.simPull _ Sm.T, Top.R0.simPull _ Sm.Lk, simPullB _ Sm.B⟩

/-- They are good, with the numbers `numsDraw`, under the hypotheses below. -/
theorem simsD_good (h1 : 1 ≤ κ₀) (hg : dr.Good κ₀) (hr : dr.TotLe n) (hN0 : 0 < L.maxBatchSize)
    {Sm : Sims L} (hS : Sm.Good Ryes M.zT M.zL M.zO) :
    (simsD lam L dr Sm).Good Ryes (numsDraw lam L dr M κ₀ n).zT
      (numsDraw lam L dr M κ₀ n).zL (numsDraw lam L dr M κ₀ n).zO := by
  have gT := drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K n (le_max_left _ _) hr.1
  have gL :=
    drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K n (le_trans (le_max_left _ _) (le_max_right _ _)) hr.2.1
  have gB :=
    drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K n (le_trans (le_max_right _ _) (le_max_right _ _)) hr.2.2
  exact ⟨fun w x => Top.R0.simPull_good gT _ w x (hS.goodT w x),
    fun w x => Top.R0.simPull_good gL _ w x (hS.goodL w x),
    fun w x hv J xs hxs => simPullB_good hN0 gB _ w x J xs (hS.goodB w x hv J xs hxs)⟩

variable {Sim : Gen.Simulator
    (Compile.Batch.spec lam (WBd lam L pT pL pB z no dr ax).K (LBd lam L dr)) Unit
    (IVKK lam (LBd lam L dr)) X (PrfK lam (LBd lam L dr))}
  {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞}


end Top.ProgDraw

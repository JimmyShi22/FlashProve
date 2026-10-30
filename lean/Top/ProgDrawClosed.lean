-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/ProgDrawClosed.lean: one definition, `bSCg`: the right-hand side of `bStd_le`
(Compile/Batch/StepS.lean). `bStd_le` bounds the seed's term `bStd` if all salts have lam bits.
  `bSCg lam p`   3 (`p.leaves` + 1) / (4 · 2^lam); `p.leaves` = p.M + 1 is the number of copies.
                 In `carryS` the error term of the seed is b, and it stands beside
                 t / (number of seeds). The head of Compile/Batch/StepS.lean says when `bStd` can be
                 taken for b.
Limits: A definition only. This file defines no scheme and states no theorem. No statement here is a
security level.
-/
import Top.BatchBoundsGenDr
import Top.BatchVQueriesDraw
import Top.ProgDraw
import Top.ProgN

noncomputable section

namespace Top.ProgDraw
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.Prog
open Compile.BatchLife (Sims)
open scoped ENNReal

/-- The right-hand side of `bStd_le` (Compile/Batch/StepS.lean). -/
def bSCg (lam : ℕ) (p : Params) : ℝ≥0∞ :=
  ((3 * (p.M + 2) : ℕ) : ℝ≥0∞) * (((4 * 2 ^ lam : ℕ) : ℝ≥0∞))⁻¹

variable {I X : Type} (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
  (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
  (dr : L.Draws lam) (ax : L.Aux pT pL pB) (p : Params) (D : SerLHB L)


variable {Ryes Rno : I → X → Prop} {M : LH.Nums} {κ₀ : ℝ≥0∞} {n : ℕ} {c : CountNumsB} {kt kr : ℝ≥0∞}


end Top.ProgDraw

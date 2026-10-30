-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageOnCore.lean: a stage whose protocol is also given by a second, equal term. (Words of
this library: lean/GLOSSARY.md.)

A stage (Blocks/Stage.lean) is a protocol (`Core`) with numbers, sets of pads and a simulator. The
definition of a scheme may mention protocols only. So a long protocol is given there as a term K
that is composed of the protocols of its rows (a row: one stage of a `Chain`, Blocks/Stage.lean),
while its properties come from a stage T that is composed of the stages of the rows, with T.toCore =
K. For long chains it is slow to let Lean compare the two terms again and again. Here the equation
is an argument, used once.
 * `Stage.epsOn`, `Stage.simOn`: the errors and the simulator of T, for the list of rounds of K.
 * `Stage.below_epsOn`: bounds for the errors carry over.
-/
import Blocks.StageSide
import Blocks.StageNums
import Blocks.LevelAcc
import Blocks.LevelLocal
import Blocks.LevelSound
import Blocks.LinkHVZK_rs
import Iop.RbrLast
import Mathlib.Data.FinEnum
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob
open scoped ENNReal

section Gen

variable {P E : Type} {a b : Sorts}

/-- The errors of the stage, for the rounds of K (hc). -/
def Stage.epsOn (T : Stage P E a b) {K : Core P E a b} (hc : T.toCore = K) : Err K.B.shape :=
  hc ▸ T.ε

/-- The simulator of the stage, for the rounds of K (hc). -/
def Stage.simOn (T : Stage P E a b) {K : Core P E a b} (hc : T.toCore = K) :
    Rho K.B.shape → PMF (Plains K.B.shape) := hc ▸ T.Sim

theorem Stage.below_epsOn {T : Stage P E a b} {K : Core P E a b} (hc : T.toCore = K)
    {κ : ℝ≥0∞} (h : T.Below κ) : Err.Below (T.epsOn hc) κ := by
  subst hc
  exact h

end Gen

end Blocks

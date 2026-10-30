-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/SolveSteps.lean: how one turn's answer carries the two iterations that solve a group
(`solveGroupFrom`, `solveStageFrom`, OnBytes/Params/Group.lean) one step on.

Four laws, by unfolding. With them a closed statement "the iteration gives this group" can be proved
from one closed statement for each turn, so that Lean's kernel evaluates one turn at a time.
OnBytes/Params/EntryStagesRecord.lean and EntryStagesRecordSmall.lean do so.
Main names: `solveStageFrom_more`, `solveStageFrom_settled`, `solveGroupFrom_more`,
`solveGroupFrom_settled`; an instance: equality of turns' answers (`Turn`) is decidable.
What is not claimed: anything on what a turn answers. Nothing on soundness.

-/
import OnBytes.Params.SizedForward

set_option autoImplicit false

namespace OnBytes.Params

deriving instance DecidableEq for Turn

/-- A turn that asks for more positions hands a later stage on to the next turn. -/
theorem solveStageFrom_more (s : Setting) (scope : Scope) (beforeR : Nat)
    (shape : GroupSize) (fuel t : Nat) (g : GroupSize) (t2 : Nat)
    (h : turn s scope ⟨stageCubeBits shape, 1, 4 + 3 * max beforeR 1024⟩ shape (tailFor t)
      (tailFor t) t = .more g t2) :
    solveStageFrom s scope beforeR shape (fuel + 1) t =
      solveStageFrom s scope beforeR shape fuel t2 := by
  rw [solveStageFrom]
  simp only [h]

/-- A turn at which the numbers have settled ends a later stage. -/
theorem solveStageFrom_settled (s : Setting) (scope : Scope) (beforeR : Nat)
    (shape : GroupSize) (fuel t : Nat) (g : GroupSize) (t2 : Nat)
    (h : turn s scope ⟨stageCubeBits shape, 1, 4 + 3 * max beforeR 1024⟩ shape (tailFor t)
      (tailFor t) t = .settled g t2) :
    solveStageFrom s scope beforeR shape (fuel + 1) t = some ⟨g, t⟩ := by
  rw [solveStageFrom]
  simp only [h]

/-- A turn that asks for more positions hands the first group on to the next turn. -/
theorem solveGroupFrom_more (s : Setting) (scope : Scope) (load : GroupLoad)
    (draws : Nat → Nat) (shape : GroupSize) (fuel t : Nat) (g : GroupSize) (t2 : Nat)
    (h : turn s scope load shape (tailFor (draws t)) (tailFor t) t = .more g t2) :
    solveGroupFrom s scope load draws shape (fuel + 1) t =
      solveGroupFrom s scope load draws shape fuel t2 := by
  rw [solveGroupFrom]
  simp only [h]

/-- A turn at which the numbers have settled, at a number of positions other than 0, ends the first
group. -/
theorem solveGroupFrom_settled (s : Setting) (scope : Scope) (load : GroupLoad)
    (draws : Nat → Nat) (shape : GroupSize) (fuel t : Nat) (g : GroupSize) (t2 : Nat)
    (h : turn s scope load shape (tailFor (draws t)) (tailFor t) t = .settled g t2)
    (h0 : (t2 == 0) = false) :
    solveGroupFrom s scope load draws shape (fuel + 1) t = some ⟨g, t⟩ := by
  rw [solveGroupFrom]
  simp only [h, h0]
  rfl

end OnBytes.Params

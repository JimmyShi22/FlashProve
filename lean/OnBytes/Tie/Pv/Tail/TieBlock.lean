-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/TieBlock.lean: the typed round of the smallness test (Cb/Pv/Tail/Block.lean) has
the list of rounds and the list of errors that the planner lays for the draw of the matrix.

OnBytes/Tie/Pv/Tail/Tie.lean and TieAll.lean say it of the library's reduction that draws a value
from any set of the right size. Here that set is Dr s, the reduction is the block's R, and the
error is the block's eps. Definitions, statements and proofs.

Main names:
  `smallOf s d`: what the planner reads of the sizes s: the columns of all matrices together and
    tau; d: the sizes of the lookup on the digits, which the draw of the matrix does not read.
  `block_shape`, `block_err`: the block's list of rounds is the one round that draws from Dr s, and
    its list of errors is "of all values, one part in 2 ^ tau".
  `block_rounds`: whatever plan the planner's finish makes of planSmall (smallOf s d) 0: the
    block's rounds have the shape of that plan's entries (ShapeIsAll, OnBytes/G4/RoundIsAll.lean).
  `block_errors`: with one instance and a column or more: the block's errors, each divided by the
    number of values of its challenge, are that plan's bounds: one equation of two lists.
  `block_errors_le`: without the premise on the columns they are at most these.
  `block_at`: the same from an idle state of a plan in writing, as a chain's routine meets it.

Limits: nothing here says that the block is sound at these errors: that is in Cb/Pv/Tail/. Which
value of Dr s belongs to which drawn bits is not said here. The shape is the one before proof of
work is added.
-/
import OnBytes.Tie.Pv.Tail.TieAll
import Cb.Pv.Tail.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop OnBytes.Params OnBytes.G4 Cb.Pv.Tail

/-- What the planner reads of the sizes. -/
def smallOf (s : Size) (d : ForestSize) : SmallSize :=
  { columns := s.columns, tau := s.tau, digits := d }

variable {K : Type} {s : Size} (Λ : Letters K s)

/-- The block's list of rounds. -/
theorem block_shape : (R Λ).shape = [IOR.drawRound (Dr s)] := rfl

/-- The block's list of errors. -/
theorem block_err (d : ForestSize) : eps Λ = drawErr (Dr s) (smallOf s d) := rfl

/-- The list of rounds. -/
theorem block_rounds (d : ForestSize) (st : Setting) (P : Planned)
    (h : finish st .request (planSmall (smallOf s d) 0) = .ok P) :
    ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape (P.rounds.map (·.entry)) :=
  rounds_areAll (Dr s) (smallOf s d) (flat s) st P h

/-- The list of errors. -/
theorem block_errors (d : ForestSize) (st : Setting) (P : Planned)
    (h : finish st .request (planSmall (smallOf s d) 0) = .ok P) (hi : st.instances ≤ 1)
    (hc : 1 ≤ s.columns) :
    List.zipWith (fun e c : ℕ => (e : ℚ) / (c : ℚ)) (eps Λ).toList (R Λ).shape.chalList =
      P.rounds.map fun r => planVal r.error :=
  errors_are (Dr s) (smallOf s d) (flat s) st P h hi hc

/-- The list of errors, without the premise on the columns. -/
theorem block_errors_le (d : ForestSize) (st : Setting) (P : Planned)
    (h : finish st .request (planSmall (smallOf s d) 0) = .ok P) (hi : st.instances ≤ 1) :
    List.Forall₂ (· ≤ ·)
      (List.zipWith (fun e c : ℕ => (e : ℚ) / (c : ℚ)) (eps Λ).toList (R Λ).shape.chalList)
      (P.rounds.map fun r => planVal r.error) :=
  errors_le (Dr s) (smallOf s d) (flat s) st P h hi

/-- From an idle state of a plan in writing: the state is idle again, one round is added, the
block's round is the round of its entry, and with one instance the block's error, divided by the
number of values, is at most its bound. -/
theorem block_at (d : ForestSize) (st : Setting) (p q : PlanState) (hp : Idle st p)
    (h : planSmall (smallOf s d) 0 p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st (smallOf s d)) ∧
      ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [(rngRound st (smallOf s d)).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e c : ℕ => (e : ℚ) / (c : ℚ)) (eps Λ).toList
            (R Λ).shape.chalList)
          [planVal (rngRound st (smallOf s d)).error]) := by
  obtain ⟨a, r, i, le, _⟩ := round_at (Dr s) (smallOf s d) (flat s) st p q hp h
  exact ⟨a, r, List.Forall₂.cons (rngIs_toAll Cb.Gl.E Cb.Gl.F i) List.Forall₂.nil,
    fun hi => List.Forall₂.cons (le hi) List.Forall₂.nil⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.block_rounds
#print axioms OnBytes.Tie.Pv.Tail.block_errors
#print axioms OnBytes.Tie.Pv.Tail.block_errors_le
#print axioms OnBytes.Tie.Pv.Tail.block_at

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/IndexOfAtFull.lean: the stored table's index at the shared chain's seat is the key file's
written one wherever AtFull holds of what the planner configured
(Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean: in the goals' scope, whatever the second hash
function and the digest, and at the written description's own plain planner by atFull_of_made): the
heir of AnswersAtScope.lean's index_at_scope, which speaks of the program's planner alone.
  index_written: indexShapeOf recordSet recordTable is the key file's written index: Lean's kernel
  index_of_atFull: so AtFull M gives M.sized.proof.batch.shape.fold.index = the written one
  index_at_seat: at p14Of c bp, for every bp, from AtFull c.made
  three_at_seat: there v = 11, answers = 1, cubeBits = 29
  ahead_at_seat: and the masks go ahead (AtFull's own clause, at the seat's letters)

What is not claimed. AtFull itself: other files' laws. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Goal.Numbers.IndexThree
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open H2K.Sizes (AtFull)
open Lk6.AtPlan (keyFull)

theorem index_written : indexShapeOf recordSet recordTable = keyFull.once.shape.fold.index := by
  decide +kernel

theorem index_of_atFull {M : Configured} (h : AtFull M) :
    M.sized.proof.batch.shape.fold.index = keyFull.once.shape.fold.index :=
  h.index.trans index_written

theorem index_at_seat {c : Model.Verify.Chains} (h : AtFull c.made) (bp : List (Nat × Nat)) :
    (p14Of c bp).S.fold.index = keyFull.once.shape.fold.index := index_of_atFull h

theorem three_at_seat {c : Model.Verify.Chains} (h : AtFull c.made) (bp : List (Nat × Nat)) :
    (p14Of c bp).S.fold.index.v = 11 ∧ (p14Of c bp).S.fold.index.answers = 1 ∧
      (p14Of c bp).S.fold.index.cubeBits = 29 := by
  rw [index_at_seat h bp]
  exact index_numbers

theorem ahead_at_seat {c : Model.Verify.Chains} (h : AtFull c.made) (bp : List (Nat × Nat)) :
    (p14Of c bp).S.masksAhead = true := h.ahead

end Desc.K14.Law

#print axioms Desc.K14.Law.index_written
#print axioms Desc.K14.Law.index_of_atFull
#print axioms Desc.K14.Law.index_at_seat
#print axioms Desc.K14.Law.three_at_seat
#print axioms Desc.K14.Law.ahead_at_seat

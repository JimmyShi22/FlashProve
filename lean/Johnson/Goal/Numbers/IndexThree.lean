-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/IndexThree.lean: three numbers of the stored table's index at the shared chain's seat, in the
scope of the goals: v = 11, answers = 1, cubeBits = 29: what the law that the instance's key
fits the index by make (Johnson/Desc/Laid/ProofInstFits.lean: instOf_key_fits) takes as premises.
  index_numbers: at the key file's written index: Lean's kernel
  index_three_at_scope: at p14Of p.chains bp, for every bp, at every three files in scope with a planner
      that returns (Johnson/Goal/Numbers/AnswersAtScope.lean: index_at_scope)

What is not claimed. It speaks of the program's planner (Model.Verify.planned). That the other law's
frS.P.v is 11. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.AnswersAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

theorem index_numbers : keyFull.once.shape.fold.index.v = 11 ∧
    keyFull.once.shape.fold.index.answers = 1 ∧ keyFull.once.shape.fold.index.cubeBits = 29 := by
  decide +kernel

theorem index_three_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    (bp : List (Nat × Nat)) : (p14Of p.chains bp).S.fold.index.v = 11 ∧
      (p14Of p.chains bp).S.fold.index.answers = 1 ∧
      (p14Of p.chains bp).S.fold.index.cubeBits = 29 := by
  have e : (p14Of p.chains bp).S.fold.index = keyFull.once.shape.fold.index := index_at_scope hZ hp
  rw [e]
  exact index_numbers

end Desc.K14.Law

#print axioms Desc.K14.Law.index_numbers
#print axioms Desc.K14.Law.index_three_at_scope

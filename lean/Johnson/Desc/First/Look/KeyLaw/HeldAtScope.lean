-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/HeldAtScope.lean: THE PLANNER'S OWN ROUNDS FOR EACH LOOKUP HOLD
(LookHeld, BelowAt.lean), FROM THE PROGRAM'S OWN MAKING OF THE CHAINS; AND, AT THE PUBLIC FILES IN
SCOPE, THE TWO SIZES OF THE MATRIX ARE ONE.

The plan prices the lookups at the matrix's size as the lines have it (RangesSized.matrix,
OnBytes/Plan/Ranges.lean); the blocks of a chain take the size from the shape of the test on the
table (Wf.matrixOf). By that file's own words nothing compares the two. At the public files in scope
the key's sizes are a written value (key_eq_at_scope, Johnson/Goal/PlanValues/KeyFullAtScope.lean),
at which the two are compared by evaluation.

Main names:
  lookHeld_of_chains: where chainsOf returns c: c.made.key is three plans, and where the first of
    them passes sideB, LookHeld holds at the face of every lookup of the sized key, at the matrix's
    size as the lines have it.
  matrix_full: at the written sizes of a key of full size the two sizes of the matrix are one.
  matrix_at_scope: so they are one at every three public files in scope.

Limits. sideB of the first plan is a premise. That the shape which a key file's description reads is
the sized key's shape is not shown here. One size.

-/
import Johnson.Goal.PlanValues.KeyFullAtScope
import OnBytes.Model.VerifyDerives
import OnBytes.Plan.PlanListsConfigure
import Johnson.Desc.First.Look.KeyLaw.HeldAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Params OnBytes.Plan
open OnBytes.Flat.Held (sideB)
open Lk6 (pubOf)

/-- **From the program's own making of the chains.** -/
theorem lookHeld_of_chains {X : Model.Verify.Public} {lay : Option ByteArray} {cfg : ByteArray}
    {c : Model.Verify.Chains} (h : Model.Verify.chainsOf X lay cfg = .ok c) :
    ∃ P1 P2 P3, c.made.key = [P1, P2, P3] ∧ (sideB P1 = true →
      ∀ l ∈ c.made.sized.key.ranges.x.lookups,
        (pubOf (Wf.lookupOf c.made.sized.key.ranges.x.messageId c.made.sized.key.ranges.matrix
          l)).Adm Cb.Gl.p → l.d ≤ 64 →
        (faceOfLkp (Wf.lookupOf c.made.sized.key.ranges.x.messageId c.made.sized.key.ranges.matrix
          l)).ok = true →
        LookHeld c.made.sized.key.set (faceOfLkp
          (Wf.lookupOf c.made.sized.key.ranges.x.messageId c.made.sized.key.ranges.matrix l))) := by
  obtain ⟨shapes, hm⟩ := Model.Verify.chainsOf_made h
  obtain ⟨-, -, P1, P2, P3, hk, h1, -⟩ := configure_plans hm
  exact ⟨P1, P2, P3, hk, fun hs l hl hadm hd hok =>
    lookHeld_of_oneTime c.made.sized.key P1 h1 hs l hl hadm hd hok⟩

/-- At the written sizes of a key of full size the two sizes of the matrix are one. -/
theorem matrix_full :
    Wf.matrixOf Lk6.AtPlan.keyFull.once.shape = Lk6.AtPlan.keyFull.ranges.matrix := by
  decide +kernel

/-- **At every three public files in scope the two sizes of the matrix are one.** -/
theorem matrix_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    Wf.matrixOf p.chains.made.sized.key.once.shape = p.chains.made.sized.key.ranges.matrix := by
  rw [Lk6.AtPlan.key_eq_at_scope hZ hp]
  exact matrix_full

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.lookHeld_of_chains
#print axioms VerifiableInference.Desc.K3.KeyLaw.matrix_full
#print axioms VerifiableInference.Desc.K3.KeyLaw.matrix_at_scope

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K14PlanY.lean: what K12's read-back law of a member's sample row asks of a message's shape
and the codes (PlanY, Johnson/Desc/K14/Law/LedgerSmpOwed.lean: one answer; rows of one
kind alone, and some; the case; lengths that are powers of two), at the three sampled messages of
the shared chain, S.fold.u, S.omega and S.sharedSplit, at the typed shape and codes of a proof file
and of a key file: Lean's kernel.
  PlanYs cs sh: PlanY's six clauses, written out sign for sign, so that this file stands on no file
      that states what is owed
  planY_real, planY_key: they hold at the three shapes
  one_kind_real, one_kind_key: which kind: o_u and o_omega have main rows alone, the split's mask
      message a mask row alone

What is not claimed. That a seated description's shape and codes are the typed ones. The law that
spends it. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14CondAt
import Johnson.Desc.K12.Law.MeetsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)

/-- PlanY's six clauses. -/
def PlanYs (cs : Codes) (sh : OracleShape) : Prop :=
  sh.answers = 1 ∧ ¬ (0 < sh.mainRows ∧ 0 < sh.maskRows) ∧ (0 < sh.mainRows ∨ 0 < sh.maskRows) ∧
    ((0 < sh.maskRows ∨ sh.mainDeg = 3) ∨ (sh.maskRows = 0 ∧ sh.mainDeg = 1)) ∧
    (sh.mainRows = 0 ∨ 2 ^ ceilLog2 (H2K.Pin.mainB cs sh).ell = (H2K.Pin.mainB cs sh).ell) ∧
    (sh.maskRows = 0 ∨ 2 ^ ceilLog2 (H2K.Pin.maskB cs sh).ell = (H2K.Pin.maskB cs sh).ell)

instance (cs : Codes) (sh : OracleShape) : Decidable (PlanYs cs sh) := by
  unfold PlanYs
  infer_instance

/-- The three at a shape. -/
def PlanY3 (cs : Codes) (S : LinShape) : Prop :=
  PlanYs cs S.fold.u ∧ PlanYs cs S.omega ∧ PlanYs cs S.sharedSplit

instance (cs : Codes) (S : LinShape) : Decidable (PlanY3 cs S) := by
  unfold PlanY3
  infer_instance

theorem planY_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    PlanY3 codesFull2 x.shape := by
  obtain ⟨x, a1, -, -⟩ := k14_real
  have h : (realSized.any fun p => decide (PlanY3 p.2 p.1.shape)) = true := by decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, of_decide_eq_true h⟩

theorem planY_key : PlanY3 keyFull.codes keyFull.once.shape := by decide +kernel

/-- Which kind of rows each has. -/
def OneKind (S : LinShape) : Prop :=
  (0 < S.fold.u.mainRows ∧ S.fold.u.maskRows = 0) ∧ (0 < S.omega.mainRows ∧ S.omega.maskRows = 0) ∧
    (S.sharedSplit.mainRows = 0 ∧ 0 < S.sharedSplit.maskRows)

instance (S : LinShape) : Decidable (OneKind S) := by
  unfold OneKind
  infer_instance

theorem one_kind_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ OneKind x.shape := by
  obtain ⟨x, a1, -, -⟩ := k14_real
  have h : (realSized.any fun p => decide (OneKind p.1.shape)) = true := by decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, of_decide_eq_true h⟩

theorem one_kind_key : OneKind keyFull.once.shape := by decide +kernel

end Desc.K14.Law

#print axioms Desc.K14.Law.planY_real
#print axioms Desc.K14.Law.planY_key
#print axioms Desc.K14.Law.one_kind_real
#print axioms Desc.K14.Law.one_kind_key

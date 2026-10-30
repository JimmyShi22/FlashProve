-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadNumsScope.lean: three closed facts on the output head's public numbers, in
the goals' scope. One theorem.

What is proved.
  calls_size_in_scope   the head's layout has six lookup calls.
  **nums_in_scope**     under VerifierAndGoals.InScope Z = true, VerifierAndGoals.readFiles Z = .ok pp and publicOf
          Z.pol Z.KL lay = .ok X: X.HLy.calls.size ≤ 6; X.hS.ls + X.hS.lt ≤ keyFloor X.hS (6 + 10 ≤
          27); X.hS.ls ≤ lNI + lPd at sizesOf X.hS (6 ≤ lNI + 13). These are, field by field, the
          three fields six, floor, hls of the structure Nums X in
          Johnson/Desc/Reads/RunIsAtBorder.lean, which this file does not import.

No existential quantifier.
Not proved here. The full size only (the scope's numbers). At publicOf's X. That publicOf returns is
a premise. Nothing on soundness.

-/
import Johnson.Goal.Meaning.HeadColsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Verify (publicOf Public)
open OnBytes.Model.Head (keyFloor)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- The head's layout has six lookup calls. -/
theorem calls_size_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.HLy.calls.size = 6 := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have A := OnBytes.Road.Hd.admittedH_of_layout B.head
  obtain ⟨cs, hc, -, hL⟩ := A.calls
  rw [hL, calls_six hc (lines_in_scope hZ hR h)]
  rfl

/-- Lean's kernel evaluates it. -/
theorem six_le_clog : 6 ≤ clog2 5120 := by
  decide +kernel

/-- **Three closed facts on the head's public numbers.** -/
theorem nums_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    X.HLy.calls.size ≤ 6 ∧ X.hS.ls + X.hS.lt ≤ keyFloor X.hS ∧
      X.hS.ls ≤ (letI := sizesOf X.hS; Norm.lNI + Norm.lPd) := by
  have N := numbers_in_scope hZ hR h
  have e : X.hS.ls = 6 := by
    show X.hS.la - X.hS.lt = 6
    rw [N.la, N.lt]
  refine ⟨Nat.le_of_eq (calls_size_in_scope hZ hR h), ?_, ?_⟩
  · rw [e, N.lt, Meaning.HeadS.keyFloor_in_scope hZ hR h]
    decide
  · refine Nat.le_trans ?_ (Nat.le_add_left _ _)
    show X.hS.ls ≤ clog2 X.hS.d
    rw [e, N.d]
    exact six_le_clog

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.calls_size_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.six_le_clog
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.nums_in_scope

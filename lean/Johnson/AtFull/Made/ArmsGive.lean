-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ArmsGive.lean: what a yes of the test on the 26 links' arms (`armsB`,
Johnson/LPFE1R/RowsAtArms.lean) says of two numbers of the public data. A law file; no running text
imports it.

Statements.
  `arms_give`: armsB X = true → X.p4 = true ∧ X.NGr = 12. Why: an attention's arm comes of the third
    branch of `armOf` alone (Johnson/Desc/First/Link/RowsRun.lean), and the written arm of link 1 is
    one: so a group has two links. The head's arm comes of the first branch alone, and the written
    arm of link 24 is the head's: so 24 = 2 * X.NGr.

Limits. That `armsB` says yes at any public files is shown nowhere here. Nothing on soundness.

-/
import Johnson.LPFE1R.RowsAtArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.Desc.LinkJoin (Arm armOf armAtW armsB arm_at)

/-- **The proof covers attention, and there are twelve groups of layers.** -/
theorem arms_give {X : OnBytes.Model.Verify.Public} (h : armsB X = true) :
    X.p4 = true ∧ X.NGr = 12 := by
  have a1 := arm_at h 1 (by omega)
  have a24 := arm_at h 24 (by omega)
  obtain ⟨l1, x1, s1, e1⟩ : ∃ l x s, armAtW 1 = .attention l x s := ⟨_, _, _, rfl⟩
  obtain ⟨l2, x2, s2, e2⟩ : ∃ l x s, armAtW 24 = .head l x s := ⟨_, _, _, rfl⟩
  rw [e1] at a1
  rw [e2] at a24
  have hp : X.p4 = true := by
    cases hf : X.p4 with
    | true => rfl
    | false =>
      exfalso
      simp only [armOf, hf, Bool.false_eq_true, if_false, Nat.mod_one, beq_self_eq_true,
        if_true] at a1
      split at a1
      · cases a1
      · split at a1 <;> cases a1
  refine ⟨hp, ?_⟩
  simp only [armOf, hp, if_true] at a24
  by_cases hN : (24 == 2 * X.NGr) = true
  · have : 24 = 2 * X.NGr := by simpa using hN
    omega
  · exfalso
    rw [if_neg hN, if_pos (show (24 % 2 == 0) = true from rfl)] at a24
    split at a24 <;> cases a24

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.arms_give

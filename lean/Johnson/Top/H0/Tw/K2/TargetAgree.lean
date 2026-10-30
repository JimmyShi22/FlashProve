-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2/TargetAgree.lean: A YARDSTICK BESIDE K2/Target.lean: NO BLOCK IMPORTS THIS
FILE. Each test of that file says, at every input, what the program's own yes-or-no function says;
and what it checks is stated as a proposition.
  padFits_eq · isPow2_eq · targetOk_eq    against (Send.pad …).isSome · powerOfTwo ·
  switchTargetCheck
  padFits_iff · targetOk_iff              what they check
No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2.Target

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

theorem iteSome {α : Type} {c : Prop} [Decidable c] (x : α) : (if c then none else
    some x).isSome = !decide c := by
  by_cases h : c <;> simp [h]

theorem leNotLt (a b : Nat) : decide (a ≤ b) = !decide (b < a) := by
  by_cases h : a ≤ b
  · simp [h, Nat.not_lt.2 h]
  · simp [h, Nat.lt_of_not_le h]

theorem padFits_eq (codes : Codes) (s : OracleShape) : padFits codes s = (Send.pad codes
    s).isSome := by
  simp only [padFits, Send.pad, Send.cube]
  rw [iteSome]
  by_cases h : 0 < s.maskRows <;> by_cases h3 : s.mainDeg = 3 <;> simp [h, h3] <;> exact leNotLt _ _

theorem isPow2_eq (n : Nat) : isPow2 n = powerOfTwo n := rfl

theorem targetOk_eq (S : Statement) (old : SingleRows) (T : SwitchTarget) : targetOk S old T =
    switchTargetCheck S old T := by
  unfold targetOk targetL switchTargetCheck
  simp only [List.all_cons, List.all_nil, Bool.and_true, padFits_eq, isPow2_eq, blocksFill,
      keptFits, Bool.and_assoc]
  rfl

theorem padFits_iff (codes : Codes) (s : OracleShape) :
    padFits codes s = true ↔
      (if 0 < s.maskRows ∨ s.mainDeg = 3 then 1 else 3) * s.answers ≤
        (if 0 < s.maskRows then (codes.mask.getD s.maskCode default).ell else
            (codes.base.getD s.code default).ell) := by
  unfold padFits
  by_cases h : 0 < s.maskRows <;> by_cases h3 : s.mainDeg = 3 <;> simp [h, h3]

theorem targetOk_iff (S : Statement) (old : SingleRows) (T : SwitchTarget) : targetOk S old T = true
    ↔ ∀ c ∈ targetL S old T, c.2 = true := by
  simp [targetOk, List.all_eq_true]

end Tw.K2

#print axioms Tw.K2.padFits_eq
#print axioms Tw.K2.targetOk_eq

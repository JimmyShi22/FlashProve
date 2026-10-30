-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/K3FormsJointKey.lean

«FORMS AGAINST KEYS»: THE STEP FROM THE CALLS' KEY VECTORS TO THE JOINT VECTOR, FOR ALL FOUR SORTS OF LOOKUP.
joint_key_agrees_where_the_calls_agree: under FoNums.ok h: two families of key vectors that agree at every call c < NC and every index
below 2 ^ nOf h c have one joint key vector at every index below 2 ^ h.v, at every shift. No public part, no trace.
-/
import Johnson.HonestTrace.CountsProducts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.HonestTrace

theorem joint_key_agrees_where_the_calls_agree {K : Type} [Field K] {h : OnBytes.Model.Forest.Shape}
    (hok : FoNums.ok h = true) (kv kv' : ℕ → ℕ → K) (θ : K)
    (H : ∀ c < h.NC, ∀ Y < 2 ^ FoNums.nOf h c, kv c Y = kv' c Y) {n : ℕ} (hn : n < 2 ^ h.v) :
    OnBytes.Ends.jointKey h kv θ n = OnBytes.Ends.jointKey h kv' θ n := by
  obtain ⟨-, b, c, -⟩ := Cb.Fo.ok_parts hok
  by_cases hy : n % 2 ^ h.rK < h.NT
  · obtain ⟨b1, b2, b3⟩ := b _ hy
    have hx : n / 2 ^ h.rK < 2 ^ h.dT := by
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, Nat.add_comm]
      exact hn
    have ha : n % 2 ^ h.rK - FoNums.fst h (FoNums.co h (n % 2 ^ h.rK)) + 1 ≤
        2 ^ FoNums.io h (FoNums.co h (n % 2 ^ h.rK)) := by omega
    have hY : (n % 2 ^ h.rK - FoNums.fst h (FoNums.co h (n % 2 ^ h.rK))) * 2 ^ h.dT + n / 2 ^ h.rK <
        2 ^ FoNums.nOf h (FoNums.co h (n % 2 ^ h.rK)) := by
      rw [(c _ b1).2.2.1, Nat.pow_add]
      calc (n % 2 ^ h.rK - FoNums.fst h (FoNums.co h (n % 2 ^ h.rK))) * 2 ^ h.dT + n / 2 ^ h.rK
          < (n % 2 ^ h.rK - FoNums.fst h (FoNums.co h (n % 2 ^ h.rK))) * 2 ^ h.dT + 2 ^ h.dT :=
            Nat.add_lt_add_left hx _
        _ = (n % 2 ^ h.rK - FoNums.fst h (FoNums.co h (n % 2 ^ h.rK)) + 1) * 2 ^ h.dT :=
            (Nat.succ_mul _ _).symm
        _ ≤ 2 ^ FoNums.io h (FoNums.co h (n % 2 ^ h.rK)) * 2 ^ h.dT := Nat.mul_le_mul_right _ ha
    rw [jointKey_tree h kv θ hy, jointKey_tree h kv' θ hy, H _ b1 _ hY]
  · rw [jointKey_empty hok kv θ (Nat.le_of_not_lt hy), jointKey_empty hok kv' θ (Nat.le_of_not_lt hy)]

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.joint_key_agrees_where_the_calls_agree

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KvNums.lean

"NumsA S" (Lane5KvKey.lean) AS A THEOREM: every shape that the verifier's own function shape
returns, at a configuration with ldh = 7, has the numbers that the terms of
OnBytes/Tie/Pv/Lookup/Ends/A.lean read as the library has them at "dimOf S". Likewise for shapeHid.

Main theorems: "numsA_of_shape", "numsA_of_hid".
The one test of shape that is used: af-shape-tiles (lB + 2 ≤ lt).

Not claimed: anything at ldh other than 7 (there the bound on a score is not the library's); how the
calls are laid; anything on the tables.
-/
import Johnson.Road.Lane5AttShape
import Johnson.Road.Lane5KvKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model.AttSeg

/-- A test that did not refuse was false. -/
theorem refuseIf_false {b : Bool} {n : String} {u : Unit}
    (h : Model.refuseIf b n = Except.ok u) : b = false := by
  cases b with
  | false => rfl
  | true =>
    have h' : (Except.error n : Except String Unit) = Except.ok u := h
    cases h'

/-- **What shape returns has the library's numbers.** -/
theorem numsA_of_shape {cf : Attention.Cfg} {S : Attention.Shape}
    (h : Attention.shape cf = Except.ok S) (hl : cf.ldh = 7) : NumsA S := by
  unfold Attention.shape at h
  obtain ⟨_, ht, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨Tt, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨calls, _, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  have hb := refuseIf_false ht
  have hlt : cf.lB + 2 ≤ cf.lt := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    omega
  obtain ⟨k, hk⟩ : ∃ k, cf.lt - cf.lB = k + 1 := ⟨cf.lt - cf.lB - 1, by omega⟩
  refine ⟨rfl, ?_, ?_, rfl, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · show 2 ^ (cf.lt - cf.lB) = 2 * 2 ^ (cf.lt - cf.lB - 1)
    rw [hk, Nat.add_sub_cancel, pow_succ, Nat.mul_comm]
  · show 2 ^ (cf.lt - cf.lB) / 2 = 2 ^ (cf.lt - cf.lB - 1)
    rw [hk, Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  · show 2 ^ cf.lt = 2 * 2 ^ (cf.lt - cf.lB - 1) * 2 ^ cf.lB
    rw [hk, Nat.add_sub_cancel, show cf.lt = (k + 1) + cf.lB by omega, pow_add, pow_succ]
    ring
  · show cf.lt = cf.lt - cf.lB - 1 + 1 + cf.lB
    omega
  · show (((2 ^ cf.ldh * Model.clamp * Model.clamp : ℕ)) : ℤ) = Inst.Model.Smax
    rw [hl]
    unfold Model.clamp Inst.Model.Smax
    norm_num

/-- **What shapeHid returns has the library's numbers.** -/
theorem numsA_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape}
    {fs : Model.Forest.Shape} (h : Attention.shapeHid lid cf = Except.ok (S, fs))
    (hl : cf.ldh = 7) : NumsA S := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have e := (Prod.mk.inj (Except.ok.inj h)).1
  have P := numsA_of_shape hA hl
  subst e
  exact ⟨P.B, P.nT, P.hP, P.G, P.T, P.dh, P.lt, P.nlQ, P.nlK, P.nlV, P.nlO, P.Sm⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.numsA_of_shape
#print axioms OnBytes.Road.L5.numsA_of_hid

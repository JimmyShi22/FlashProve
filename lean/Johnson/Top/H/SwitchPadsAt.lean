-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchPadsAt.lean: where the places of a sample's pad lie, for an oracle
message without mask rows: in the main table, at indices below (2 ^ row bits) * (the row's length).

A law on the program's pure function `padPlaces` (OnBytes/Iop/Cs.lean, over `Send.pad`,
OnBytes/Iop/Send.lean). A kept member of a code switch has no mask rows (`switchTargetCheck`).
Statements and proofs.
Main names:
  `pad_form_mem`: a place of a pad, by its number.
  `pad_index_lt`: the law. `pad_index_lt_pow`: the same with 2 ^ (row bits + ceilLog2 of the
    length).
Limits: nothing on a message with mask rows. Nothing on soundness.

-/
import Johnson.Top.H.SwitchPads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice

theorem pad_form_mem (part : Part) (c0 base e a rb : ℕ) (bs : ℕ → E) (p : PadPlace)
    (hp : p ∈ (List.range a).flatMap fun i => (List.range e).map fun t =>
      ({ part := part, index := c0 + (base + e * i + t) * 2 ^ rb, answer := i, basis := bs t } :
        PadPlace)) :
    ∃ m, m < e * a ∧ p.index = c0 + (base + m) * 2 ^ rb ∧ p.part = part := by
  rw [List.mem_flatMap] at hp
  obtain ⟨i, hi, hp⟩ := hp
  rw [List.mem_map] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  rw [List.mem_range] at hi ht
  refine ⟨e * i + t, ?_, ?_, rfl⟩
  · have h : e * (i + 1) ≤ e * a := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at h
    omega
  · show c0 + (base + e * i + t) * 2 ^ rb = c0 + (base + (e * i + t)) * 2 ^ rb
    rw [Nat.add_assoc]

theorem mem_getD_ite (c : Prop) [Decidable c] (L : List PadPlace) (p : PadPlace)
    (h : p ∈ (if c then none else some L : Option (List PadPlace)).getD []) : ¬ c ∧ p ∈ L := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact absurd h (by simp)
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- **Where a pad's places lie, for a message without mask rows.** -/
theorem pad_index_lt (codes : Codes) (s : OracleShape) (hm : s.maskRows = 0)
    (hr : 0 < s.mainRows) (p : PadPlace) (hp : p ∈ padPlaces codes s) :
    p.part = Part.main ∧
      p.index < 2 ^ ceilLog2 s.mainRows * (codes.base.getD s.code default).ell := by
  have hh : (Send.cube codes s).hasMask = false := by
    unfold Send.cube
    simp [hm]
  have hb : (Send.cube codes s).mainRowBits = ceilLog2 s.mainRows := by
    unfold Send.cube
    simp [hr]
  unfold padPlaces Send.pad at hp
  obtain ⟨h1, h2⟩ := mem_getD_ite _ _ p hp
  obtain ⟨m, m1, m2, m3⟩ := pad_form_mem _ _ _ _ _ _ _ p h2
  simp only [hh, hb, Bool.false_eq_true, if_false, Bool.false_or] at h1 m1 m2 m3
  refine ⟨m3, ?_⟩
  rw [m2]
  generalize (if (s.mainDeg == 3) = true then 1 else 3) * s.answers = Ea at h1 m1
  generalize (codes.base.getD s.code default).ell = len at h1 ⊢
  have hR := le_two_pow_ceilLog2 s.mainRows
  have hq : len - Ea + m + 1 ≤ len := by omega
  have h3 := Nat.mul_le_mul_right (2 ^ ceilLog2 s.mainRows) hq
  rw [Nat.add_mul, Nat.one_mul] at h3
  rw [Nat.mul_comm (2 ^ ceilLog2 s.mainRows) len]
  omega

theorem pad_index_lt_pow (codes : Codes) (s : OracleShape) (hm : s.maskRows = 0)
    (hr : 0 < s.mainRows) (p : PadPlace) (hp : p ∈ padPlaces codes s) :
    p.index < 2 ^ (ceilLog2 s.mainRows + (codes.base.getD s.code default).logEll) := by
  refine lt_of_lt_of_le (pad_index_lt codes s hm hr p hp).2 ?_
  rw [Nat.pow_add]
  exact Nat.mul_le_mul_left _ (le_two_pow_ceilLog2 _)

end Johnson.Top.H

#print axioms Johnson.Top.H.pad_index_lt
#print axioms Johnson.Top.H.pad_index_lt_pow

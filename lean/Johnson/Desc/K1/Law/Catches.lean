-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Catches.lean: the pads' places: which entries they are, and that they lie in
their table.

Main names: Msg.e_cases, mem_pads, padIdx_inj, find_pad, isPad, isPad_iff, weight_pad,
weight_proper; le_two_pow_clog', Msg.size, has_padPart, size_padPart, padIdx_lt_size.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Means2
import OnBytes.Slice.RecordOK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

/-! ## The pads' places -/

theorem Msg.e_cases (m : Msg) : m.e = 1 ∨ m.e = 3 := by
  unfold Msg.e
  split <;> simp

theorem Msg.mem_pads (m : Msg) (x : Nat × Nat × Nat) :
    x ∈ m.pads ↔ ∃ k t, k < m.answers ∧ t < m.e ∧ x = (k, m.padIdx k t, t) := by
  unfold Msg.pads
  simp only [List.mem_flatMap, List.mem_range, Msg.pad_eq, List.map_map, List.mem_map,
    Function.comp]
  constructor
  · rintro ⟨k, hk, t, ht, rfl⟩
    exact ⟨k, t, hk, ht, rfl⟩
  · rintro ⟨k, t, hk, ht, rfl⟩
    exact ⟨k, hk, t, ht, rfl⟩

theorem Msg.padIdx_inj (m : Msg) {k k' t t' : Nat} (ht : t < m.e) (ht' : t' < m.e)
    (h : m.padIdx k t = m.padIdx k' t') : k = k' ∧ t = t' := by
  have key : m.e * k + t = m.e * k' + t' := by
    rcases Nat.lt_trichotomy (m.e * k + t) (m.e * k' + t') with hlt | heq | hgt
    · exact absurd h (Nat.ne_of_lt (m.padIdx_lt _ _ _ _ hlt))
    · exact heq
    · exact absurd h.symm (Nat.ne_of_lt (m.padIdx_lt _ _ _ _ hgt))
  rcases m.e_cases with he | he <;> rw [he] at key ht ht' <;> omega

theorem Msg.find_pad (m : Msg) (k t : Nat) (hk : k < m.answers) (ht : t < m.e) :
    (m.pads.find? fun x => m.padPart == m.padPart && x.2.1 == m.padIdx k t) =
      some (k, m.padIdx k t, t) := by
  cases hf : m.pads.find? fun x => m.padPart == m.padPart && x.2.1 == m.padIdx k t with
  | none =>
    have := List.find?_eq_none.1 hf (k, m.padIdx k t, t) ((m.mem_pads _).2 ⟨k, t, hk, ht, rfl⟩)
    simp at this
  | some x =>
    have hx := List.find?_some hf
    obtain ⟨k', t', _, ht', rfl⟩ := (m.mem_pads _).1 (List.mem_of_find?_eq_some hf)
    simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq] at hx
    obtain ⟨rfl, rfl⟩ := m.padIdx_inj ht' ht hx
    rfl

/-- An entry is a pad's. -/
def Msg.isPad (m : Msg) (part : Part) (j : Nat) : Bool :=
  (m.pads.find? fun x => part == m.padPart && x.2.1 == j).isSome

theorem Msg.isPad_iff (m : Msg) (part : Part) (j : Nat) :
    m.isPad part j = true ↔
      part = m.padPart ∧ ∃ k t, k < m.answers ∧ t < m.e ∧ j = m.padIdx k t := by
  unfold Msg.isPad
  constructor
  · intro h
    obtain ⟨x, hf⟩ := Option.isSome_iff_exists.1 h
    have hx := List.find?_some hf
    obtain ⟨k, t, hk, ht, rfl⟩ := (m.mem_pads _).1 (List.mem_of_find?_eq_some hf)
    simp only [Bool.and_eq_true, beq_iff_eq] at hx
    exact ⟨hx.1, k, t, hk, ht, hx.2.symm⟩
  · rintro ⟨rfl, k, t, hk, ht, rfl⟩
    rw [m.find_pad k t hk ht]
    rfl

theorem Msg.weight_pad (m : Msg) (z : Nat → GE) (β : GE) (i k t : Nat) (hk : k < m.answers)
    (ht : t < m.e) :
    m.weight z β i m.padPart (m.padIdx k t) = if k = i then β * readE (thetaE t) else 0 := by
  unfold Msg.weight
  rw [m.find_pad k t hk ht]

theorem Msg.weight_proper (m : Msg) (z : Nat → GE) (β : GE) (i : Nat) (part : Part) (j : Nat)
    (h : m.isPad part j = false) :
    m.weight z β i part j = if m.has part then eqW m.v z (m.vertex part j) else 0 := by
  unfold Msg.isPad at h
  unfold Msg.weight
  cases hf : m.pads.find? fun x => part == m.padPart && x.2.1 == j with
  | none => rfl
  | some x => rw [hf] at h; cases h

/-! ## The pads lie in their table -/

theorem le_two_pow_clog' (n : Nat) : n ≤ 2 ^ clog n := by
  unfold clog
  by_cases h : n ≤ 1
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    have h1 : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) := Nat.lt_log2_self
    exact Nat.le_of_pred_lt h1

/-- The number of a table's entries. -/
def Msg.size (m : Msg) (part : Part) : Nat := if m.has part then 2 ^ m.bits part else 0

theorem Msg.has_padPart (m : Msg) (hne : (m.K != 0 || m.Kzk != 0) = true) :
    m.has m.padPart = true := by
  unfold Msg.padPart Msg.has
  cases hZ : (m.Kzk != 0)
  · simpa [hZ] using hne
  · simp

theorem Msg.size_padPart (m : Msg) (hne : (m.K != 0 || m.Kzk != 0) = true) :
    m.size m.padPart = 2 ^ clog m.padRows * m.padLen := by
  unfold Msg.size
  rw [m.has_padPart hne, if_pos rfl]
  unfold Msg.padPart Msg.padRows Msg.padLen
  cases hZ : (m.Kzk != 0)
  · have hK : m.K ≠ 0 := by simpa [hZ] using hne
    simp [Msg.bits, Msg.mainBits, hK, pow_add]
  · have hK : m.Kzk ≠ 0 := by simpa using hZ
    simp [Msg.bits, Msg.maskBits, hK, pow_add]

theorem Msg.padIdx_lt_size (m : Msg) (hne : (m.K != 0 || m.Kzk != 0) = true)
    (hf : m.padFits = true) (k t : Nat) (hk : k < m.answers) (ht : t < m.e) :
    m.padIdx k t < m.size m.padPart := by
  have hfit : m.e * m.answers ≤ m.padLen := by
    unfold Msg.padFits at hf
    unfold Msg.padLen
    exact of_decide_eq_true hf
  rw [m.size_padPart hne]
  unfold Msg.padIdx
  have h1 : m.e * (k + 1) ≤ m.e * m.answers := Nat.mul_le_mul_left _ hk
  rw [Nat.mul_succ] at h1
  have h2 : m.padLen - m.e * m.answers + m.e * k + t + 1 ≤ m.padLen := by omega
  have h3 := Nat.mul_le_mul_right (2 ^ clog m.padRows) h2
  rw [Nat.succ_mul] at h3
  have h4 := le_two_pow_clog' m.padRows
  have h5 : 0 < 2 ^ clog m.padRows := Nat.two_pow_pos _
  rw [Nat.mul_comm (2 ^ clog m.padRows)]
  omega

end VerifiableInference.Desc.K1

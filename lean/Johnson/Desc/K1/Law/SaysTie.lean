-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SaysTie.lean: what the sample row says of words, and that it has what the laying
of a row on a group asks.

Main names: has_eq, bits_eq, tableSize_eq (the statement's numbers of a table are the message's);
says_iff; fold_parts, Msg.bits_le_v, ten_vars; rowIn_sample.

What is not claimed. The reading is the one in the library's extension field. What words are on the
rows of a table beyond the real ones is not said. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.Catches3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

/-! ## The statement's numbers of a table are the message's -/

theorem has_eq (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (part : Part) : S.has o part = (Msg.of S.codes x.shape).has part := by
  unfold Statement.has
  rw [hx]
  cases part
  · show decide (0 < x.shape.mainRows) = (x.shape.mainRows != 0)
    by_cases h : x.shape.mainRows = 0 <;> simp [h, Nat.pos_iff_ne_zero]
  · show decide (0 < x.shape.maskRows) = (x.shape.maskRows != 0)
    by_cases h : x.shape.maskRows = 0 <;> simp [h, Nat.pos_iff_ne_zero]

theorem bits_eq (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (part : Part) (hp : (Msg.of S.codes x.shape).has part = true) :
    S.tableBits o part = (Msg.of S.codes x.shape).bits part := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [hx]
  cases part
  · have h : x.shape.mainRows ≠ 0 := by simpa [Msg.has, Msg.of] using hp
    simp [Msg.bits, Msg.mainBits, Msg.of, OracleShape.rows, h, clog, ceilLog2]
  · have h : x.shape.maskRows ≠ 0 := by simpa [Msg.has, Msg.of] using hp
    simp [Msg.bits, Msg.maskBits, Msg.of, OracleShape.rows, h, clog, ceilLog2]

theorem tableSize_eq (S : Statement) (o : Nat) (x : OnBytes.Oracle)
    (hx : S.oracles[o]? = some x) (part : Part) :
    Means.tableSize S o part = (Msg.of S.codes x.shape).size part := by
  unfold Means.tableSize Msg.size
  rw [has_eq S o x hx part]
  by_cases hp : (Msg.of S.codes x.shape).has part = true
  · rw [if_pos hp, if_pos hp, bits_eq S o x hx part hp]
  · rw [if_neg hp, if_neg hp]

theorem Msg.lt_of_size (m : Msg) (part : Part) (j : Nat) (h : j < m.size part) :
    j < 2 ^ m.bits part := by
  unfold Msg.size at h
  by_cases hp : m.has part = true
  · rwa [if_pos hp] at h
  · rw [if_neg hp] at h
    exact absurd h (Nat.not_lt_zero _)

/-! ## What the sample row says of words -/

/-- **The sample row says of words that the left side, in the page's closed form, on the message's
own two tables, is the answer.** -/
theorem says_iff (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (z : List E) (β : E) (i : Nat) (y : E) (w : Means.Words GE)
    (hne : ((Msg.of S.codes x.shape).K != 0 || (Msg.of S.codes x.shape).Kzk != 0) = true)
    (hz : (Msg.of S.codes x.shape).v ≤ z.length) :
    Means.Says rdE S (sampleRow (Msg.of S.codes x.shape) o z β i y) w ↔
      (Msg.of S.codes x.shape).form (readL z) (readE β) i (w o) = readE y := by
  obtain ⟨_, ht, h0, hc⟩ := meansLaw (Msg.of S.codes x.shape) o z β i y hne hz
  have ho : o < S.oracles.size := by
    by_contra h
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hx
    cases hx
  have hT : ∀ part, Means.onTable rdE S (sampleRow (Msg.of S.codes x.shape) o z β i y) w o part =
      ∑ j ∈ Finset.range ((Msg.of S.codes x.shape).size part),
        (Msg.of S.codes x.shape).weight (readL z) (readE β) i part j * w o part j := fun part => by
    unfold Means.onTable
    rw [tableSize_eq S o x hx part]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hc part j (Msg.lt_of_size _ part j (Finset.mem_range.1 hj))]
    rfl
  unfold Means.Says Means.value
  rw [Finset.sum_eq_single o, hT, hT, ht]
  · rfl
  · intro o' _ hne'
    have hz0 : ∀ part, Means.onTable rdE S (sampleRow (Msg.of S.codes x.shape) o z β i y) w o'
        part = 0 := fun part => by
      unfold Means.onTable
      refine Finset.sum_eq_zero fun j _ => ?_
      have := h0 o' part j hne'
      unfold coefAt at this
      rw [rdE_val, this, zero_mul]
    rw [hz0, hz0, add_zero]
  · intro h
    exact absurd (Finset.mem_range.2 ho) h

/-! ## The parts of the sample row -/

theorem fold_parts (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) :
    ∀ (l : List (Nat × Nat × Nat)) (r : OnBytes.Row),
      (l.foldl (m.padStep o z β i) r).terms = r.terms ∧
        (l.foldl (m.padStep o z β i) r).runs = r.runs ∧
        (l.foldl (m.padStep o z β i) r).forms = r.forms ∧
        ∀ u ∈ (l.foldl (m.padStep o z β i) r).units.toList, u ∈ r.units.toList ∨
          ∃ x ∈ l, u.oracle = o ∧ u.part = m.padPart ∧ u.index = x.2.1
  | [], _ => ⟨rfl, rfl, rfl, fun _ h => Or.inl h⟩
  | x :: l, r => by
    obtain ⟨h1, h2, h3, h4⟩ := fold_parts m o z β i l (m.padStep o z β i r x)
    refine ⟨h1, h2, h3, fun u hu => ?_⟩
    rcases h4 u hu with h | ⟨x', hx', h⟩
    · simp only [Msg.padStep, Row.addUnit, Array.toList_push, List.mem_append,
        List.mem_singleton] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨x, List.mem_cons_self, rfl, rfl, rfl⟩
    · exact Or.inr ⟨x', List.mem_cons_of_mem _ hx', h⟩

theorem Msg.bits_le_v (m : Msg) (part : Part) : m.bits part ≤ m.v := by
  unfold Msg.v
  split
  · cases part
    · exact Nat.le_succ_of_le (Nat.le_max_left _ _)
    · exact Nat.le_succ_of_le (Nat.le_max_right _ _)
  · cases part
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left _ _

theorem Msg.ten_vars (m : Msg) (z : List E) (part : Part) (hz : m.v ≤ z.length) :
    (m.ten z part).vars = m.bits part := by
  have h := m.bits_le_v part
  cases part
  · show (Tensor.eq (z.take m.mainBits) _).vars = m.mainBits
    have h' : m.mainBits ≤ m.v := h
    rw [vars_eqTensor, List.length_take]
    omega
  · show (Tensor.eq (z.take m.maskBits) _).vars = m.maskBits
    have h' : m.maskBits ≤ m.v := h
    rw [vars_eqTensor, List.length_take]
    omega

/-- **The sample row of a member of a group has what the laying of a row on the group asks.** -/
theorem rowIn_sample (S : Statement) (G : Group) (o : Nat) (x : OnBytes.Oracle)
    (hx : S.oracles[o]? = some x) (hG : G.members.contains o = true) (z : List E) (β : E) (i : Nat)
    (y : E) (hne : ((Msg.of S.codes x.shape).K != 0 || (Msg.of S.codes x.shape).Kzk != 0) = true)
    (hf : (Msg.of S.codes x.shape).padFits = true) (hz : (Msg.of S.codes x.shape).v ≤ z.length) :
    Means.RowIn S G (sampleRow (Msg.of S.codes x.shape) o z β i y) := by
  obtain ⟨p1, p2, p3, p4⟩ := fold_parts (Msg.of S.codes x.shape) o z β i
    (Msg.of S.codes x.shape).pads { kind := .sample }
  have hterm : ∀ part, (Msg.of S.codes x.shape).has part = true →
      Blk.placeOk S G o part ((Msg.of S.codes x.shape).ten z part).vars 0 = true :=
      fun part hp => by
    unfold Blk.placeOk
    rw [hG, has_eq S o x hx part, hp, Msg.ten_vars _ z part hz, bits_eq S o x hx part hp]
    simp
  rw [sampleRow_eq]
  unfold Msg.row₀
  refine ⟨fun t ht => ?_, fun u hu => ?_, fun w hw => ?_, fun f hf' => ?_⟩
  · cases hK : ((Msg.of S.codes x.shape).K != 0) <;>
      cases hZ : ((Msg.of S.codes x.shape).Kzk != 0) <;>
      simp only [hK, hZ, if_true, if_false, Bool.false_eq_true, Row.add, p1, Array.toList_push,
        List.mem_append, List.mem_singleton] at ht
    · simp at ht
    · rcases ht with ht | rfl
      · simp at ht
      · exact hterm .mask hZ
    · rcases ht with ht | rfl
      · simp at ht
      · exact hterm .main hK
    · rcases ht with (ht | rfl) | rfl
      · simp at ht
      · exact hterm .main hK
      · exact hterm .mask hZ
  · have hu' : u ∈ ((Msg.of S.codes x.shape).pads.foldl
        ((Msg.of S.codes x.shape).padStep o z β i) { kind := .sample }).units.toList := by
      cases hK : ((Msg.of S.codes x.shape).K != 0) <;>
        cases hZ : ((Msg.of S.codes x.shape).Kzk != 0) <;>
        simpa [hK, hZ, Row.add] using hu
    rcases p4 u hu' with h | ⟨q, hq, e1, e2, e3⟩
    · simp at h
    · obtain ⟨k, t, hk, ht, rfl⟩ := ((Msg.of S.codes x.shape).mem_pads q).1 hq
      have hp := (Msg.of S.codes x.shape).has_padPart hne
      have hlt := (Msg.of S.codes x.shape).padIdx_lt_size hne hf k t hk ht
      rw [e1, e2, e3]
      unfold Blk.placeOk
      rw [hG, has_eq S o x hx _, hp, bits_eq S o x hx _ hp]
      simpa using Msg.lt_of_size _ _ _ hlt
  · exfalso
    cases hK : ((Msg.of S.codes x.shape).K != 0) <;>
      cases hZ : ((Msg.of S.codes x.shape).Kzk != 0) <;>
      simp [hK, hZ, Row.add, p2] at hw
  · exfalso
    cases hK : ((Msg.of S.codes x.shape).K != 0) <;>
      cases hZ : ((Msg.of S.codes x.shape).Kzk != 0) <;>
      simp [hK, hZ, Row.add, p3] at hf'

end VerifiableInference.Desc.K1

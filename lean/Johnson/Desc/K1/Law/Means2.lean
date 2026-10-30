-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Means2.lean: the sample row's coefficients in closed form.

Main names: Msg.padRows, padLen, padIdx, pad_eq, padIdx_lt, pads_pairwise (the pads' places are
different); sum_find; Msg.cube, front_eq, ten_entry, ten_eqW (a table's weight is the weight of the
entry's vertex on the message's cube); meansLaw.
Lemmas on pure functions of the verifier program are spent: readE_eq (OnBytes/Slice/BlkTens.lean),
front_mul_eqW, readE_front_single (OnBytes/Slice/BlkSend.lean); the kind's front factor is
Send.front at the cube made of the message's numbers, by unfolding.

What is not claimed. Nothing on an index beyond a table. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.Means

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

/-! ## The pads' places are different -/

def Msg.padRows (m : Msg) : Nat := if m.Kzk != 0 then m.Kzk else m.K
def Msg.padLen (m : Msg) : Nat := if m.Kzk != 0 then 2 ^ m.logEllZk else 2 ^ m.logEll

/-- The index of entry t of the pad of answer k. -/
def Msg.padIdx (m : Msg) (k t : Nat) : Nat :=
  (m.padRows - 1) + (m.padLen - m.e * m.answers + m.e * k + t) * 2 ^ clog m.padRows

theorem Msg.pad_eq (m : Msg) (k : Nat) :
    m.pad k = (List.range m.e).map fun t => (m.padIdx k t, t) := by
  unfold Msg.pad Msg.padIdx Msg.padRows Msg.padLen
  cases h : (m.Kzk != 0) <;> rfl

theorem Msg.padIdx_lt (m : Msg) (k k' t t' : Nat) (h : m.e * k + t < m.e * k' + t') :
    m.padIdx k t < m.padIdx k' t' := by
  unfold Msg.padIdx
  have hp : 0 < 2 ^ clog m.padRows := Nat.two_pow_pos _
  have : (m.padLen - m.e * m.answers + m.e * k + t) * 2 ^ clog m.padRows <
      (m.padLen - m.e * m.answers + m.e * k' + t') * 2 ^ clog m.padRows :=
    Nat.mul_lt_mul_of_pos_right (by omega) hp
  omega

theorem Msg.pads_pairwise (m : Msg) : m.pads.Pairwise fun x y => x.2.1 < y.2.1 := by
  unfold Msg.pads
  rw [List.pairwise_flatMap]
  constructor
  · intro k _
    rw [Msg.pad_eq, List.map_map, List.pairwise_map]
    exact (List.pairwise_lt_range).imp fun {t t'} h => m.padIdx_lt k k t t' (by omega)
  · refine (List.pairwise_lt_range).imp fun {k k'} h x hx y hy => ?_
    rw [Msg.pad_eq, List.map_map] at hx hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    obtain ⟨t', _, rfl⟩ := List.mem_map.1 hy
    have ht := List.mem_range.1 ht
    have h2 : m.e * (k + 1) ≤ m.e * k' := Nat.mul_le_mul_left _ h
    rw [Nat.mul_succ] at h2
    exact m.padIdx_lt k k' t t' (by omega)

/-! ## A sum with at most one summand -/

theorem sum_find {α : Type} (c : α → Bool) (f : α → GE) : ∀ l : List α,
    l.Pairwise (fun x y => ¬ (c x = true ∧ c y = true)) →
    (l.map fun x => if c x then f x else 0).sum = ((l.find? c).map f).getD 0
  | [], _ => rfl
  | a :: l, h => by
    have h' := List.pairwise_cons.1 h
    rw [List.map_cons, List.sum_cons]
    by_cases ha : c a = true
    · have hz : (l.map fun x => if c x then f x else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
        have : c x ≠ true := fun hc => h'.1 x hx ⟨ha, hc⟩
        simp [this]
      simp [ha, hz]
    · rw [sum_find c f l h'.2]
      simp [ha]

/-! ## The weight of an entry on the cube -/

/-- The message's cube in the record that the laws on the front factor take. -/
def Msg.cube (m : Msg) : SampleCube :=
  { hasMain := m.K != 0, hasMask := m.Kzk != 0, mainBits := m.mainBits, maskBits := m.maskBits
    bits := m.v }

theorem Msg.front_eq (m : Msg) (z : List E) (tb : Nat) (mask : Bool) :
    m.front z tb mask = Send.front z m.cube tb mask := rfl

theorem ten_entry (m : Msg) (z : List E) (part : Part) (j : Nat) :
    readE ((m.ten z part).entry j) =
      readE (Send.front z m.cube (m.bits part) (part == .mask)) *
        eqW (min (m.bits part) z.length) (readL z) j := by
  have key : ∀ (n : ℕ) (f : E), readE ((Tensor.eq (z.take n) f).entry j) =
      readE f * eqW (min n z.length) (readL z) j := fun n f => by
    rw [readE_eq, List.length_take]
    exact congrArg _ (eqW_congr _ _ _ _ fun t ht =>
      readL_take _ _ _ (Nat.lt_of_lt_of_le ht (Nat.min_le_left _ _)))
  cases part
  · exact key _ _
  · exact key _ _

theorem ten_eqW (m : Msg) (z : List E) (part : Part) (j : Nat) (hz : m.v ≤ z.length)
    (hp : m.has part = true) (hj : j < 2 ^ m.bits part) :
    readE ((m.ten z part).entry j) = eqW m.v (readL z) (m.vertex part j) := by
  rw [ten_entry]
  unfold Msg.vertex
  by_cases hb : (m.K != 0 && m.Kzk != 0) = true
  · have hv : m.v = max m.mainBits m.maskBits + 1 := by
      unfold Msg.v
      rw [if_pos hb]
    have hle : m.bits part + 1 ≤ m.v := by
      rw [hv]
      cases part
      · exact Nat.succ_le_succ (Nat.le_max_left _ _)
      · exact Nat.succ_le_succ (Nat.le_max_right _ _)
    have hmin : min (m.bits part) z.length = m.bits part := by omega
    rw [hmin, front_mul_eqW z m.cube _ _ hb hle hz j hj, hb, Bool.true_and]
    rfl
  · have hb' : (m.K != 0 && m.Kzk != 0) = false := Bool.eq_false_iff.2 hb
    have hv : m.v = m.bits part := by
      unfold Msg.v
      rw [if_neg hb]
      cases part
      · have hK : (m.K != 0) = true := hp
        rw [hK, Bool.true_and] at hb'
        have : m.Kzk = 0 := by simpa using hb'
        simp [Msg.bits, Msg.maskBits, this]
      · have hZ : (m.Kzk != 0) = true := hp
        rw [hZ, Bool.and_true] at hb'
        have : m.K = 0 := by simpa using hb'
        simp [Msg.bits, Msg.mainBits, this]
    rw [readE_front_single _ _ _ _ hb', one_mul, ← hv, Nat.min_eq_left hz, hb', Bool.false_and,
      if_neg Bool.false_ne_true, Nat.zero_add]

/-! ## MEANS -/

theorem meansLaw : MeansLaw sampleRow := by
  intro m o z β i y hne hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sampleRow_eq]
    have h0 := fold_kind m o z β i m.pads { kind := .sample }
    unfold Msg.row₀
    cases hK : (m.K != 0) <;> cases hZ : (m.Kzk != 0) <;> exact h0
  · rw [sampleRow_eq]
  · intro o' part j ho
    have hb : (o == o') = false := beq_eq_false_iff_ne.2 fun e => ho e.symm
    rw [coefAt_sampleRow]
    simp [hb]
  · intro part j hj
    rw [coefAt_sampleRow]
    have hs := sum_find (fun x : Nat × Nat × Nat => part == m.padPart && x.2.1 == j)
      (fun x => padW β i x - readE ((m.ten z m.padPart).entry x.2.1)) m.pads
      (m.pads_pairwise.imp fun {x y} hlt hc => by
        have h1 := hc.1
        have h2 := hc.2
        simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
        omega)
    have e : (m.pads.map fun x => if o == o && m.padPart == part && x.2.1 == j then
          padW β i x - readE ((m.ten z m.padPart).entry x.2.1) else 0) =
        m.pads.map fun x => if (part == m.padPart && x.2.1 == j) = true then
          padW β i x - readE ((m.ten z m.padPart).entry x.2.1) else 0 := by
      refine List.map_congr_left fun x _ => ?_
      have : (m.padPart == part) = (part == m.padPart) := by
        cases part <;> cases m.padPart <;> rfl
      simp [this]
    rw [e, hs]
    unfold Msg.weight
    cases hf : m.pads.find? fun x => part == m.padPart && x.2.1 == j with
    | none =>
      by_cases hp : m.has part = true
      · simp [hp, ten_eqW m z part j hz hp hj]
      · simp [hp]
    | some x =>
      have hx := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have hp : m.has m.padPart = true := by
        unfold Msg.padPart Msg.has
        cases hZ : (m.Kzk != 0)
        · simpa [hZ] using hne
        · simp
      simp [hp, padW]

end VerifiableInference.Desc.K1

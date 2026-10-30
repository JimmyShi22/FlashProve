-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Port2.lean: towards the tie between the kind's sample row and the library's
sample map of a shape with one answer: the pads' places of the two sides are the same entries.

Main names: Tie (the premises: one answer, lengths that are powers of two, an admitted shape, pads
that fit); padIdx_main, padIdx_mask; isPad_main, isPad_mask.

What is not claimed. The tie itself is not in this file. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.Port1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack

/-- The premises of the tie. -/
structure Tie (cs : Codes) (s : OracleShape) : Prop where
  one : s.answers = 1
  lengths : cs.lengthsOk = true
  shape : Blk.shapeOk cs s = true
  fits : (Msg.of cs s).padFits = true

variable {cs : Codes} {s : OracleShape}

theorem Tie.rows (h : Tie cs s) : 0 < s.mainRows + s.maskRows := by
  have := h.shape
  simp only [Blk.shapeOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1.1

theorem Tie.lenMain (h : Tie cs s) (h0 : 0 < s.mainRows) :
    2 ^ (Msg.of cs s).logEll = (pMain cs s).ell := by
  have hs := h.shape
  have hl := h.lengths
  simp only [Codes.lengthsOk, Bool.and_eq_true] at hl
  simp only [Blk.shapeOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  have hm : s.code < cs.base.size := by
    rcases hs.1.1.2 with c | c
    · omega
    · exact c
  exact pow_logEll cs.base s.code hm hl.1

theorem Tie.lenMask (h : Tie cs s) (h0 : 0 < s.maskRows) :
    2 ^ (Msg.of cs s).logEllZk = (pMask cs s).ell := by
  have hs := h.shape
  have hl := h.lengths
  simp only [Codes.lengthsOk, Bool.and_eq_true] at hl
  simp only [Blk.shapeOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  have hm : s.maskCode < cs.mask.size := by
    rcases hs.1.2 with c | c
    · omega
    · exact c
  exact pow_logEll cs.mask s.maskCode hm hl.2

theorem e_main (hz : s.maskRows = 0) : (Msg.of cs s).e = eachZ s := by
  unfold Msg.e eachZ
  by_cases h3 : s.mainDeg = 3 <;> simp [Msg.of, hz, h3]

theorem e_mask (hz : 0 < s.maskRows) : (Msg.of cs s).e = 1 := by
  have : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 hz
  simp [Msg.e, Msg.of, this]

theorem Tie.fitMain (h : Tie cs s) (hz : s.maskRows = 0) : eachZ s ≤ (pMain cs s).ell := by
  have h0 : 0 < s.mainRows := by have := h.rows; omega
  have hf := h.fits
  unfold Msg.padFits at hf
  have hf := of_decide_eq_true hf
  rw [e_main hz, show (Msg.of cs s).answers = s.answers from rfl, h.one, Nat.mul_one] at hf
  have hk : ((Msg.of cs s).Kzk != 0) = false := by simp [Msg.of, hz]
  rw [hk, if_neg Bool.false_ne_true, h.lenMain h0] at hf
  exact hf

theorem Tie.fitMask (h : Tie cs s) (hz : 0 < s.maskRows) : 1 ≤ (pMask cs s).ell := by
  have hf := h.fits
  unfold Msg.padFits at hf
  have hf := of_decide_eq_true hf
  rw [e_mask hz, show (Msg.of cs s).answers = s.answers from rfl, h.one, Nat.mul_one] at hf
  have hk : ((Msg.of cs s).Kzk != 0) = true := by
    have : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 hz
    simp [Msg.of, this]
  rw [hk, if_pos rfl, h.lenMask hz] at hf
  exact hf

/-- Without mask rows: the index of entry t of the one pad. -/
theorem padIdx_main (h : Tie cs s) (hz : s.maskRows = 0) (t : Nat) :
    (Msg.of cs s).padIdx 0 t =
      (s.mainRows - 1) + 2 ^ k1 s * ((pMain cs s).ell - eachZ s + t) := by
  have h0 : 0 < s.mainRows := by have := h.rows; omega
  have hk : ((Msg.of cs s).Kzk != 0) = false := by simp [Msg.of, hz]
  unfold Msg.padIdx Msg.padRows Msg.padLen
  rw [hk, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, h.lenMain h0, e_main hz,
    show (Msg.of cs s).answers = s.answers from rfl, h.one, Nat.mul_one, Nat.mul_zero,
    Nat.add_zero, Nat.mul_comm]
  rfl

/-- With mask rows: the index of the one pad's one entry. -/
theorem padIdx_mask (h : Tie cs s) (hz : 0 < s.maskRows) :
    (Msg.of cs s).padIdx 0 0 = (s.maskRows - 1) + 2 ^ k2 s * ((pMask cs s).ell - 1) := by
  have hk : ((Msg.of cs s).Kzk != 0) = true := by
    have : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 hz
    simp [Msg.of, this]
  unfold Msg.padIdx Msg.padRows Msg.padLen
  rw [hk, if_pos rfl, if_pos rfl, h.lenMask hz, e_mask hz,
    show (Msg.of cs s).answers = s.answers from rfl, h.one, Nat.mul_one, Nat.mul_zero,
    Nat.add_zero, Nat.mul_comm]
  rfl

theorem padPart_main (hz : s.maskRows = 0) : (Msg.of cs s).padPart = .main := by
  simp [Msg.padPart, Msg.of, hz]

theorem padPart_mask (hz : 0 < s.maskRows) : (Msg.of cs s).padPart = .mask := by
  have : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 hz
  simp [Msg.padPart, Msg.of, this]

/-- **An entry of the main table is a pad's on both sides or on neither**, and on both it is the
same entry of the pad. -/
theorem isPad_main (h : Tie cs s) (x : Fin s.mainRows × Fin (pMain cs s).ell) :
    ((Msg.of cs s).isPad .main (x.1.val + 2 ^ k1 s * x.2.val) = true ↔
        padP cs s (Sum.inl x)) ∧
      (padP cs s (Sum.inl x) → padNo cs s (Sum.inl x) < (Msg.of cs s).e ∧
        (Msg.of cs s).padPart = .main ∧
        x.1.val + 2 ^ k1 s * x.2.val = (Msg.of cs s).padIdx 0 (padNo cs s (Sum.inl x))) := by
  have hx1 : x.1.val < 2 ^ k1 s := Nat.lt_of_lt_of_le x.1.isLt (le_two_pow_ceilLog2 _)
  have hx2 := x.2.isLt
  have hx0 := x.1.isLt
  have key : padP cs s (Sum.inl x) → padNo cs s (Sum.inl x) < (Msg.of cs s).e ∧
      (Msg.of cs s).padPart = .main ∧
      x.1.val + 2 ^ k1 s * x.2.val = (Msg.of cs s).padIdx 0 (padNo cs s (Sum.inl x)) := by
    rintro ⟨hz, a, b⟩
    have hf := h.fitMain hz
    refine ⟨?_, padPart_main hz, ?_⟩
    · rw [e_main hz]
      show x.2.val + eachZ s - (pMain cs s).ell < eachZ s
      omega
    · rw [padIdx_main h hz]
      show _ = s.mainRows - 1 + 2 ^ k1 s *
        ((pMain cs s).ell - eachZ s + (x.2.val + eachZ s - (pMain cs s).ell))
      have e1 : (pMain cs s).ell - eachZ s + (x.2.val + eachZ s - (pMain cs s).ell) = x.2.val := by
        omega
      rw [e1]
      omega
  refine ⟨⟨fun hp => ?_, fun hp => ?_⟩, key⟩
  · obtain ⟨hpart, k, t, hk, ht, hidx⟩ := ((Msg.of cs s).isPad_iff _ _).1 hp
    have hz : s.maskRows = 0 := by
      by_contra c
      rw [padPart_mask (Nat.pos_of_ne_zero c)] at hpart
      cases hpart
    have hk0 : k = 0 := by
      have : (Msg.of cs s).answers = 1 := h.one
      omega
    subst hk0
    rw [padIdx_main h hz] at hidx
    rw [e_main hz] at ht
    have hf := h.fitMain hz
    have hR : s.mainRows - 1 < 2 ^ k1 s :=
      Nat.lt_of_lt_of_le (by omega : s.mainRows - 1 < s.mainRows) (le_two_pow_ceilLog2 _)
    obtain ⟨a, b⟩ := idx_inj (k1 s) hx1 hR hidx
    exact ⟨hz, by omega, by omega⟩
  · obtain ⟨a, b, c⟩ := key hp
    rw [c]
    exact ((Msg.of cs s).isPad_iff _ _).2 ⟨b.symm, 0, _, by
      rw [show (Msg.of cs s).answers = s.answers from rfl, h.one]; exact Nat.one_pos, a, rfl⟩

/-- **The like of the mask table.** -/
theorem isPad_mask (h : Tie cs s) (x : Fin s.maskRows × Fin (pMask cs s).ell) :
    ((Msg.of cs s).isPad .mask (x.1.val + 2 ^ k2 s * x.2.val) = true ↔
        padP cs s (Sum.inr x)) ∧
      (padP cs s (Sum.inr x) → (Msg.of cs s).padPart = .mask ∧
        x.1.val + 2 ^ k2 s * x.2.val = (Msg.of cs s).padIdx 0 0) := by
  have hx1 : x.1.val < 2 ^ k2 s := Nat.lt_of_lt_of_le x.1.isLt (le_two_pow_ceilLog2 _)
  have hx2 := x.2.isLt
  have hx0 := x.1.isLt
  have hz : 0 < s.maskRows := by omega
  have key : padP cs s (Sum.inr x) → (Msg.of cs s).padPart = .mask ∧
      x.1.val + 2 ^ k2 s * x.2.val = (Msg.of cs s).padIdx 0 0 := by
    rintro ⟨a, b⟩
    refine ⟨padPart_mask hz, ?_⟩
    rw [padIdx_mask h hz]
    have e1 : (pMask cs s).ell - 1 = x.2.val := by omega
    rw [e1]
    omega
  refine ⟨⟨fun hp => ?_, fun hp => ?_⟩, key⟩
  · obtain ⟨_, k, t, hk, ht, hidx⟩ := ((Msg.of cs s).isPad_iff _ _).1 hp
    have hk0 : k = 0 := by
      have : (Msg.of cs s).answers = 1 := h.one
      omega
    have ht0 : t = 0 := by
      rw [e_mask hz] at ht
      omega
    subst hk0 ht0
    rw [padIdx_mask h hz] at hidx
    have hf := h.fitMask hz
    have hR : s.maskRows - 1 < 2 ^ k2 s :=
      Nat.lt_of_lt_of_le (by omega : s.maskRows - 1 < s.maskRows) (le_two_pow_ceilLog2 _)
    obtain ⟨a, b⟩ := idx_inj (k2 s) hx1 hR hidx
    exact ⟨by omega, by omega⟩
  · obtain ⟨b, c⟩ := key hp
    rw [c]
    exact ((Msg.of cs s).isPad_iff _ _).2 ⟨b.symm, 0, 0, by
      rw [show (Msg.of cs s).answers = s.answers from rfl, h.one]; exact Nat.one_pos, by
      rw [e_mask hz]; exact Nat.one_pos, rfl⟩

end VerifiableInference.Desc.K1

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Port3.lean: the tie: at a shape with one answer, the answer of the library's
sample map of the shape (Johnson/Pack/PortZ.lean: portZ) on a message is the left side of the kind's
sample row on the tables that hold the message on the real rows and places, and 0 beyond.

Main names: tabOf; mat_pad, mat_proper; weight_main, weight_mask; port_val.

What is not claimed. One answer a message, as in the library's file. The premise that every code's
length is a power of two is used. Nothing on lists, on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Port2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood

variable {cs : Codes} {s : OracleShape}

/-- The two tables that hold a message of the library's code of the shape. -/
def tabOf (cs : Codes) (s : OracleShape) (msg : (portCode cs s).J → GE) : Part → Nat → GE
  | .main => tabAt (k1 s) fun x : Fin s.mainRows × Fin (pMain cs s).ell => msg (Sum.inl x)
  | .mask => tabAt (k2 s) fun x : Fin s.maskRows × Fin (pMask cs s).ell => msg (Sum.inr x)

theorem mat_pad (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (j : (portCode cs s).J) (h : padP cs s j) :
    (portZ cs s).mat ρ () j = (ρ.2 : GE) * wZ cs s ⟨j, h⟩ := by
  have e : sigmaZ cs s j = Sum.inr ⟨j, h⟩ := by
    apply (sigmaZ cs s).symm.injective
    simp [sigmaZ]
  show Sum.elim _ _ (sigmaZ cs s j) = _
  rw [e]
  rfl

theorem mat_proper (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (j : (portCode cs s).J)
    (h : ¬ padP cs s j) :
    (portZ cs s).mat ρ () j =
      Alg.eqk ρ.1 fun t : Fin (bitsZ cs s) => (idxZ cs s j).testBit t.val := by
  have e : sigmaZ cs s j = Sum.inl ⟨j, h⟩ := by
    apply (sigmaZ cs s).symm.injective
    simp [sigmaZ]
  show Sum.elim _ _ (sigmaZ cs s j) = _
  rw [e]
  rfl

theorem one_pos_answers (h : Tie cs s) : 0 < (Msg.of cs s).answers := by
  rw [show (Msg.of cs s).answers = s.answers from rfl, h.one]
  exact Nat.one_pos

theorem e_le_three (m : Msg) : m.e ≤ 3 := by
  rcases m.e_cases with h | h <;> omega

/-- The weight of a real entry of the main table is the library's coefficient. -/
theorem weight_main (h : Tie cs s) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ)
    (x : Fin s.mainRows × Fin (pMain cs s).ell) :
    (Msg.of cs s).weight (pointOf ρ.1) (ρ.2 : GE) 0 .main (x.1.val + 2 ^ k1 s * x.2.val) =
      (portZ cs s).mat ρ () (Sum.inl x) := by
  by_cases hp : padP cs s (Sum.inl x)
  · obtain ⟨a, b, c⟩ := (isPad_main h x).2 hp
    have w := (Msg.of cs s).weight_pad (pointOf ρ.1) (ρ.2 : GE) 0 0 _ (one_pos_answers h) a
    rw [b, ← c, if_pos rfl] at w
    rw [w, mat_pad ρ _ hp]
    congr 1
    have h3 : padNo cs s (Sum.inl x) < 3 := Nat.lt_of_lt_of_le a (e_le_three _)
    have := theta_padW ⟨padNo cs s (Sum.inl x) % 3, Nat.mod_lt _ (by decide)⟩
    simp only [Nat.mod_eq_of_lt h3] at this
    rw [this]
    unfold wZ
    simp only [Nat.mod_eq_of_lt h3]
  · have hn : (Msg.of cs s).isPad .main (x.1.val + 2 ^ k1 s * x.2.val) = false :=
      Bool.eq_false_iff.2 fun c => hp ((isPad_main h x).1.1 c)
    have h0 : s.mainRows ≠ 0 := by have := x.1.isLt; omega
    have hh : (Msg.of cs s).has .main = true := by simp [Msg.has, Msg.of, h0]
    rw [mat_proper ρ _ hp, (Msg.of cs s).weight_proper _ _ _ _ _ hn, if_pos hh]
    have hv : (Msg.of cs s).vertex .main (x.1.val + 2 ^ k1 s * x.2.val) =
        idxZ cs s (Sum.inl x) := by
      simp [Msg.vertex, idxZ]
    rw [hv, v_bitsZ, eqW_pointOf]

/-- The like of the mask table. -/
theorem weight_mask (h : Tie cs s) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ)
    (x : Fin s.maskRows × Fin (pMask cs s).ell) :
    (Msg.of cs s).weight (pointOf ρ.1) (ρ.2 : GE) 0 .mask (x.1.val + 2 ^ k2 s * x.2.val) =
      (portZ cs s).mat ρ () (Sum.inr x) := by
  have hz : 0 < s.maskRows := by have := x.1.isLt; omega
  have hz' : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 hz
  by_cases hp : padP cs s (Sum.inr x)
  · obtain ⟨b, c⟩ := (isPad_mask h x).2 hp
    have w := (Msg.of cs s).weight_pad (pointOf ρ.1) (ρ.2 : GE) 0 0 0 (one_pos_answers h)
      (by rw [e_mask hz]; exact Nat.one_pos)
    rw [b, ← c, if_pos rfl] at w
    rw [w, mat_pad ρ _ hp]
    exact congrArg _ (theta_padW 0)
  · have hn : (Msg.of cs s).isPad .mask (x.1.val + 2 ^ k2 s * x.2.val) = false :=
      Bool.eq_false_iff.2 fun c => hp ((isPad_mask h x).1.1 c)
    have hh : (Msg.of cs s).has .mask = true := by simp [Msg.has, Msg.of, hz']
    rw [mat_proper ρ _ hp, (Msg.of cs s).weight_proper _ _ _ _ _ hn, if_pos hh]
    have hv : (Msg.of cs s).vertex .mask (x.1.val + 2 ^ k2 s * x.2.val) =
        idxZ cs s (Sum.inr x) := by
      unfold Msg.vertex
      rw [v_bitsZ]
      show _ = x.1.val + 2 ^ k2 s * x.2.val +
        (if 0 < s.mainRows then 2 ^ max (B1 cs s) (B2 cs s) else 0)
      by_cases h1 : 0 < s.mainRows
      · have h1' : s.mainRows ≠ 0 := Nat.pos_iff_ne_zero.1 h1
        have hb : bitsZ cs s - 1 = max (B1 cs s) (B2 cs s) := by
          unfold bitsZ
          rw [if_pos ⟨h1, hz⟩, Nat.add_sub_cancel]
        rw [hb, if_pos h1]
        simp [Msg.of, h1', hz', Nat.add_comm]
      · have h1' : s.mainRows = 0 := by omega
        rw [if_neg h1]
        simp [Msg.of, h1']
    rw [hv, v_bitsZ, eqW_pointOf]

theorem pow_room (k Lc : Nat) : 2 ^ k * Lc ≤ 2 ^ (k + ceilLog2 Lc) := by
  rw [pow_add]
  exact Nat.mul_le_mul_left _ (le_two_pow_ceilLog2 Lc)

/-- **The tie.** -/
theorem port_val (h : Tie cs s) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ)
    (msg : (portCode cs s).J → GE) :
    (portZ cs s).val ρ msg () =
      (Msg.of cs s).form (pointOf ρ.1) (ρ.2 : GE) 0 (tabOf cs s msg) := by
  have hmain : ∑ j ∈ Finset.range (if (Msg.of cs s).has .main then 2 ^ (Msg.of cs s).bits .main
        else 0), (Msg.of cs s).weight (pointOf ρ.1) (ρ.2 : GE) 0 .main j * tabOf cs s msg .main j =
      ∑ x : Fin s.mainRows × Fin (pMain cs s).ell,
        (portZ cs s).mat ρ () (Sum.inl x) * msg (Sum.inl x) := by
    by_cases h0 : 0 < s.mainRows
    · have h0' : s.mainRows ≠ 0 := Nat.pos_iff_ne_zero.1 h0
      have hh : (Msg.of cs s).has .main = true := by simp [Msg.has, Msg.of, h0']
      rw [if_pos hh, bits_main cs s h0]
      show ∑ j ∈ Finset.range (2 ^ B1 cs s), _ * tabAt (k1 s) _ j = _
      rw [sum_table (k1 s) (2 ^ B1 cs s) (le_two_pow_ceilLog2 _) (pow_room _ _)]
      exact Finset.sum_congr rfl fun x _ => by rw [weight_main h ρ x]
    · have h0' : s.mainRows = 0 := by omega
      have hh : (Msg.of cs s).has .main = false := by simp [Msg.has, Msg.of, h0']
      rw [hh, if_neg Bool.false_ne_true, Finset.range_zero, Finset.sum_empty]
      exact (Finset.sum_eq_zero fun x _ => absurd x.1.isLt (by omega)).symm
  have hmask : ∑ j ∈ Finset.range (if (Msg.of cs s).has .mask then 2 ^ (Msg.of cs s).bits .mask
        else 0), (Msg.of cs s).weight (pointOf ρ.1) (ρ.2 : GE) 0 .mask j * tabOf cs s msg .mask j =
      ∑ x : Fin s.maskRows × Fin (pMask cs s).ell,
        (portZ cs s).mat ρ () (Sum.inr x) * msg (Sum.inr x) := by
    by_cases h0 : 0 < s.maskRows
    · have h0' : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 h0
      have hh : (Msg.of cs s).has .mask = true := by simp [Msg.has, Msg.of, h0']
      rw [if_pos hh, bits_mask cs s h0]
      show ∑ j ∈ Finset.range (2 ^ B2 cs s), _ * tabAt (k2 s) _ j = _
      rw [sum_table (k2 s) (2 ^ B2 cs s) (le_two_pow_ceilLog2 _) (pow_room _ _)]
      exact Finset.sum_congr rfl fun x _ => by rw [weight_mask h ρ x]
    · have h0' : s.maskRows = 0 := by omega
      have hh : (Msg.of cs s).has .mask = false := by simp [Msg.has, Msg.of, h0']
      rw [hh, if_neg Bool.false_ne_true, Finset.range_zero, Finset.sum_empty]
      exact (Finset.sum_eq_zero fun x _ => absurd x.1.isLt (by omega)).symm
  unfold Msg.form
  rw [hmain, hmask]
  show ∑ j : (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell),
    (portZ cs s).mat ρ () j * msg j = _
  rw [Fintype.sum_sum_type]
  rfl

end VerifiableInference.Desc.K1

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/Reads.lean: the maps of the library's steps s16 and s21 of an attention
segment, written as reads of arrays.

The library defines the two maps of a step as multilinear extensions over the step's cube
(Inst/Model/Att/Sums.lean: Aext, Bext). A claim of the verifier reads an array head by head,
position by position and channel by channel; the library's words for such reads are rd2 and rd3
(the same file). This file shows that the maps are such reads, for all sizes, cells and points.
 - aext16: the first map of step s16 is the read of the queries.
 - bitCube_ext, aext21: the first map of step s21 is the sum over the bits k of eq(ξ_k, k) times
   the read of bit k of the index. bext21: the second map is the first minus 1.

Tools: eqN_sh, ext_three.

What this file does not claim. Nothing is said about a verifier, a proof or hiding.


-/
import Cb.Pv.Att.Mean.BitsScore
import Cb.Pv.Att.Bits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E]

/-- A part of a point, read from its own coordinate 0 on. -/
theorem eqN_sh (n off : ℕ) (ξ : ℕ → E) (X : ℕ) : eqN n 0 (sh ξ off) X = eqN n off ξ X :=
  eqN_agree (fun k _ => by simp only [sh, Nat.zero_add]) X

/-- The extension of a vector with three-part indices (x | y | z), as a triple sum. -/
theorem ext_three (a b c : ℕ) (v ξ : ℕ → E) :
    ext (a + b + c) v ξ =
      ∑ x ∈ range (2 ^ a), ∑ y ∈ range (2 ^ b), ∑ z ∈ range (2 ^ c),
        eqN a 0 ξ x * eqN b 0 (sh ξ a) y * eqN c 0 (sh ξ (a + b)) z *
          v ((x * 2 ^ b + y) * 2 ^ c + z) := by
  rw [ext_two, pow_add, Alg.sum_range_mul_add]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y hy => sum_congr rfl fun z _ => ?_
  rw [eqN_append' a b 0 ξ x (mem_range.mp hy), Nat.zero_add, eqN_sh, eqN_sh]

variable (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E)

/-! ## Step s16 -/

/-- **The first map of step s16 is the read of the queries.** -/
theorem aext16 (b : ℕ) (ξ : ℕ → E) :
    Aext D C p t .s16 b ξ =
      rd3 D (sh ξ D.lT) (eqT D ξ) (sh ξ (D.lT + D.lg)) (qryV t b) := by
  show ext (D.lT + D.lg + D.ln)
    (fun X => qryV t b (X / 2 ^ D.ln % 2 ^ D.lg) (X / 2 ^ D.ln / 2 ^ D.lg) (X % 2 ^ D.ln)) ξ = _
  rw [ext_three, sum_comm]
  unfold rd3 eqT
  rw [D.T_eq]
  refine sum_congr rfl fun g hg => sum_congr rfl fun i _ => sum_congr rfl fun n hn => ?_
  have e1 := Dim.div_step (a := i * 2 ^ D.lg + g) (Nat.two_pow_pos D.ln) (mem_range.mp hn)
  have e2 := Dim.div_step (a := i) (Nat.two_pow_pos D.lg) (mem_range.mp hg)
  simp only [e1.1, e1.2, e2.1, e2.2]
  ring

/-! ## Step s21 -/

/-- **The first map of the sumcheck for the bits, bit by bit**, for any number kap of bits that can
number the bits of a position. -/
theorem bitCube_ext (kap : ℕ) (hK : D.lT ≤ 2 ^ kap) (b : ℕ) (ξ : ℕ → E) :
    ext (D.lT + D.lg + kap) (bitCube kap D t b) ξ =
      ∑ k ∈ range D.lT, eqN kap 0 (sh ξ (D.lT + D.lg)) k *
        rd2 D (sh ξ D.lT) (eqT D ξ) (ibV t k b) := by
  rw [ext_three]
  have s1 : ∀ i ∈ range (2 ^ D.lT), ∀ g ∈ range (2 ^ D.lg), ∀ k ∈ range (2 ^ kap),
      eqN D.lT 0 ξ i * eqN D.lg 0 (sh ξ D.lT) g * eqN kap 0 (sh ξ (D.lT + D.lg)) k *
          bitCube kap D t b ((i * 2 ^ D.lg + g) * 2 ^ kap + k) =
        (if k < D.lT then eqN kap 0 (sh ξ (D.lT + D.lg)) k *
          (eqN D.lg 0 (sh ξ D.lT) g * eqN D.lT 0 ξ i * ibV t k b g i) else 0) := by
    intro i _ g hg k hk
    have e1 := Dim.div_step (a := i * 2 ^ D.lg + g) (Nat.two_pow_pos kap) (mem_range.mp hk)
    have e2 := Dim.div_step (a := i) (Nat.two_pow_pos D.lg) (mem_range.mp hg)
    show _ * (if ((i * 2 ^ D.lg + g) * 2 ^ kap + k) % 2 ^ kap < D.lT then
        ibV t (((i * 2 ^ D.lg + g) * 2 ^ kap + k) % 2 ^ kap) b
          (((i * 2 ^ D.lg + g) * 2 ^ kap + k) / 2 ^ kap % 2 ^ D.lg)
          (((i * 2 ^ D.lg + g) * 2 ^ kap + k) / 2 ^ kap / 2 ^ D.lg) else 0) = _
    simp only [e1.1, e1.2, e2.1, e2.2]
    split_ifs <;> ring
  rw [sum_congr rfl fun i hi => sum_congr rfl fun g hg => sum_congr rfl fun k hk =>
      s1 i hi g hg k hk,
    sum_congr rfl fun i _ => sum_comm, sum_comm, ← sum_subset (range_subset_range.mpr hK)]
  · refine sum_congr rfl fun k hk => ?_
    unfold rd2 eqT
    rw [D.T_eq, sum_comm, mul_sum]
    refine sum_congr rfl fun g _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by rw [if_pos (mem_range.mp hk)]
  · intro k _ hk
    exact sum_eq_zero fun i _ => sum_eq_zero fun g _ =>
      if_neg fun h' => hk (mem_range.mpr h')

/-- **The first map of step s21, bit by bit.** -/
theorem aext21 (b : ℕ) (ξ : ℕ → E) :
    Aext D C p t .s21 b ξ =
      ∑ k ∈ range D.lT, eqN D.lK 0 (sh ξ (D.lT + D.lg)) k *
        rd2 D (sh ξ D.lT) (eqT D ξ) (ibV t k b) :=
  bitCube_ext D t D.lK (Nat.le_pow_clog (by norm_num) D.lT) b ξ

/-- **The second map of step s21 is the first minus 1.** -/
theorem bext21 (b : ℕ) (ξ : ℕ → E) :
    Bext D C p t .s21 b ξ = Aext D C p t .s21 b ξ - 1 := by
  show ext (D.lT + D.lg + D.lK) (fun X => Acube D C p t .s21 b X - 1) ξ =
    ext (D.lT + D.lg + D.lK) (Acube D C p t .s21 b) ξ - 1
  rw [ext_sub, ext_const]

end Cb.Pv.Att

#print axioms Cb.Pv.Att.aext16
#print axioms Cb.Pv.Att.bitCube_ext
#print axioms Cb.Pv.Att.aext21
#print axioms Cb.Pv.Att.bext21

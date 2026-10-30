-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/TensorProofs.lean: the proofs of the statements of Cb/Gen/Tensor.lean on the layout by column
blocks and on the tensor form. Arithmetic of quotients and remainders by 2^lo, and a change of the
order of summation; no code, no protocol.

Main names (statements and hypotheses: Cb/Gen/Tensor.lean):
  `get_put`: reading after writing.
  `put_inj`: injectivity of writing.
  `form_rows`: the tensor form as a linear form on the message.

Limits: see "Limits" in the head of Cb/Gen/Tensor.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.Tensor
import Blocks.EqN

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop Finset

theorem natAt {K : Type} [Zero K] {n : ℕ} (v : Fin n → K) {t : ℕ} (h : t < n) :
    nat v t = v ⟨t, h⟩ := dif_pos h
theorem natOff {K : Type} [Zero K] {n : ℕ} (v : Fin n → K) {t : ℕ} (h : ¬ t < n) : nat v t = 0 :=
  dif_neg h

namespace IdxFmt
variable {F : Type} (Φ : IdxFmt F)

/-- a place of the layout -/
theorem place_lt {y b : ℕ} (hy : y < Φ.h) (hb : b < 2 ^ Φ.lo) : 2 ^ Φ.lo * y + b < 2 ^ Φ.lo * Φ.h :=
  calc 2 ^ Φ.lo * y + b < 2 ^ Φ.lo * y + 2 ^ Φ.lo := Nat.add_lt_add_left hb _
    _ = 2 ^ Φ.lo * (y + 1) := (Nat.mul_succ _ _).symm
    _ ≤ 2 ^ Φ.lo * Φ.h := Nat.mul_le_mul_left _ hy

theorem div_block (a : ℕ) {b : ℕ} (hb : b < 2 ^ Φ.lo) : (2 ^ Φ.lo * a + b) / 2 ^ Φ.lo = a := by
  rw [Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hb, Nat.add_zero]

theorem mod_block (a : ℕ) {b : ℕ} (hb : b < 2 ^ Φ.lo) : (2 ^ Φ.lo * a + b) % 2 ^ Φ.lo = b := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

theorem row_lt_iff (c : ℕ) : c / 2 ^ Φ.lo < 2 ^ Φ.hi ↔ c < 2 ^ (Φ.hi + Φ.lo) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]

variable [Zero F]

/-- for y < h and b < 2^lo, the entry (y, 2^lo ι + b) is read at the place 2^lo y + b of row ι -/
theorem get_block (m : Φ.Msg) {y b : ℕ} (hy : y < Φ.h) (ι : Fin (2 ^ Φ.hi)) (hb : b < 2 ^ Φ.lo) :
    Φ.get m y (2 ^ Φ.lo * ι.val + b) = nat (m ι) (2 ^ Φ.lo * y + b) := by
  unfold get
  rw [if_pos hy, Φ.div_block _ hb, Φ.mod_block _ hb, natAt _ ι.2]

end IdxFmt

theorem inRange_get : Spec.inRange_get := by
  intro F _ Φ m y c h
  unfold IdxFmt.get
  by_cases hy : y < Φ.h
  · rw [if_pos hy, natOff _ fun hc => h ⟨hy, (Φ.row_lt_iff c).1 hc⟩]
  · rw [if_neg hy]

theorem put_get : Spec.put_get := by
  intro F _ Φ m ι j hj
  have hb : j.val % 2 ^ Φ.lo < 2 ^ Φ.lo := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hy : j.val / 2 ^ Φ.lo < Φ.h := Nat.div_lt_of_lt_mul hj
  unfold IdxFmt.put
  rw [if_pos hj, Φ.get_block m hy ι hb, Nat.div_add_mod, natAt _ j.2]

theorem get_put : Spec.get_put := by
  intro F _ Φ hF W hW
  funext y c
  by_cases h : y < Φ.h ∧ c < 2 ^ (Φ.hi + Φ.lo)
  · obtain ⟨hy, hc⟩ := h
    have hb : c % 2 ^ Φ.lo < 2 ^ Φ.lo := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hj := Φ.place_lt hy hb
    have e := Φ.get_block (Φ.put W) hy ⟨c / 2 ^ Φ.lo, (Φ.row_lt_iff c).2 hc⟩ hb
    rw [Nat.div_add_mod] at e
    rw [e, natAt _ (lt_of_lt_of_le hj hF)]
    unfold IdxFmt.put
    rw [if_pos hj]
    show W ((2 ^ Φ.lo * y + c % 2 ^ Φ.lo) / 2 ^ Φ.lo)
        (2 ^ Φ.lo * (c / 2 ^ Φ.lo) + (2 ^ Φ.lo * y + c % 2 ^ Φ.lo) % 2 ^ Φ.lo) = W y c
    rw [Φ.div_block _ hb, Φ.mod_block _ hb, Nat.div_add_mod]
  · rw [inRange_get F Φ _ y c h, hW y c h]

theorem put_inj : Spec.put_inj := by
  intro F _ Φ hF W W' hW hW' h
  rw [← get_put F Φ hF W hW, h, get_put F Φ hF W' hW']

theorem put_off : Spec.put_off := by
  intro F _ Φ W ι j hj
  unfold IdxFmt.put
  rw [if_neg (Nat.not_lt.2 hj)]

theorem get_congr : Spec.get_congr := by
  intro F _ Φ m m' h
  funext y c
  unfold IdxFmt.get
  by_cases hy : y < Φ.h
  · rw [if_pos hy, if_pos hy]
    by_cases hc : c / 2 ^ Φ.lo < 2 ^ Φ.hi
    · rw [natAt _ hc, natAt _ hc]
      have hj := Φ.place_lt hy (Nat.mod_lt c (Nat.two_pow_pos Φ.lo))
      by_cases hm : 2 ^ Φ.lo * y + c % 2 ^ Φ.lo < Φ.code.msg
      · rw [natAt _ hm, natAt _ hm]
        exact h _ ⟨_, hm⟩ hj
      · rw [natOff _ hm, natOff _ hm]
    · rw [natOff _ hc, natOff _ hc]
  · rw [if_neg hy, if_neg hy]

theorem form_rows : Spec.form_rows := by
  intro F _ E _ _ Φ hF g ψ m
  have hR : ∀ ι : Fin (2 ^ Φ.hi), ∑ j : Fin Φ.code.msg,
        Φ.rowCoef g ψ ι.val j.val * algebraMap F E (m ι j) =
      ∑ y ∈ range Φ.h, ∑ b ∈ range (2 ^ Φ.lo), g y * (eqN Φ.hi 0 ψ ι.val * eqN Φ.lo Φ.hi ψ b) *
        algebraMap F E (nat (m ι) (2 ^ Φ.lo * y + b)) := by
    intro ι
    have e1 : ∑ j : Fin Φ.code.msg, Φ.rowCoef g ψ ι.val j.val * algebraMap F E (m ι j)
        = ∑ j ∈ range Φ.code.msg, Φ.rowCoef g ψ ι.val j * algebraMap F E (nat (m ι) j) := by
      rw [← Fin.sum_univ_eq_sum_range
          (fun j => Φ.rowCoef g ψ ι.val j * algebraMap F E (nat (m ι) j)) Φ.code.msg]
      exact sum_congr rfl fun j _ => by rw [natAt (m ι) j.2]
    have e2 : ∑ j ∈ range Φ.code.msg, Φ.rowCoef g ψ ι.val j * algebraMap F E (nat (m ι) j)
        = ∑ j ∈ range (2 ^ Φ.lo * Φ.h), Φ.rowCoef g ψ ι.val j * algebraMap F E (nat (m ι) j) :=
      (sum_subset (range_subset_range.mpr hF) fun j _ hj => by
        unfold IdxFmt.rowCoef
        rw [if_neg (fun h => hj (mem_range.mpr h)), mul_zero, zero_mul]).symm
    rw [e1, e2, Nat.mul_comm, Alg.sum_range_mul_add]
    refine sum_congr rfl fun y hy => sum_congr rfl fun b hb => ?_
    have hb' := mem_range.mp hb
    rw [Nat.mul_comm y]
    unfold IdxFmt.rowCoef
    rw [if_pos (Φ.place_lt (mem_range.mp hy) hb'), Φ.div_block _ hb', Φ.mod_block _ hb']
    ring
  calc
    Φ.form g ψ (Φ.get m) =
        ∑ y ∈ range Φ.h, ∑ ι : Fin (2 ^ Φ.hi), ∑ b ∈ range (2 ^ Φ.lo), g y *
          (eqN Φ.hi 0 ψ ι.val * eqN Φ.lo Φ.hi ψ b) *
          algebraMap F E (nat (m ι) (2 ^ Φ.lo * y + b)) := by
        unfold IdxFmt.form
        refine sum_congr rfl fun y hy => ?_
        rw [pow_add, Alg.sum_range_mul_add,
          ← Fin.sum_univ_eq_sum_range
            (fun a =>
              ∑ b ∈ range (2 ^ Φ.lo), g y * eqN (Φ.hi + Φ.lo) 0 ψ (a * 2 ^ Φ.lo + b) *
                algebraMap F E (Φ.get m y (a * 2 ^ Φ.lo + b))) (2 ^ Φ.hi)]
        refine sum_congr rfl fun ι _ => sum_congr rfl fun b hb => ?_
        rw [eqN_append' Φ.hi Φ.lo 0 ψ ι.val (mem_range.mp hb), Nat.zero_add, Nat.mul_comm ι.val,
          Φ.get_block m (mem_range.mp hy) ι (mem_range.mp hb)]
    _ = ∑ ι : Fin (2 ^ Φ.hi), ∑ y ∈ range Φ.h, ∑ b ∈ range (2 ^ Φ.lo), g y *
          (eqN Φ.hi 0 ψ ι.val * eqN Φ.lo Φ.hi ψ b) *
          algebraMap F E (nat (m ι) (2 ^ Φ.lo * y + b)) := sum_comm
    _ = _ := sum_congr rfl fun ι _ => (hR ι).symm

end Cb

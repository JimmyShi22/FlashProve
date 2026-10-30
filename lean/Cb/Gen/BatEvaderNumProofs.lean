-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/BatEvaderNumProofs.lean: the proofs of Cb/Gen/BatEvaderNum.lean. A sum over Fin n is a sum
over the numbers below n; the count is `Blocks.cnt_eqN_zero_le`; the fraction is `Blocks.point_le`.
-/
import Cb.Gen.BatEvaderNum

set_option autoImplicit false

namespace Cb
open Blocks Iop Prob Alg Finset
open scoped ENNReal

theorem nat_fin {K : Type} [Zero K] {n : ℕ} (v : Fin n → K) (j : Fin n) : nat v j.val = v j := by
  unfold nat
  rw [dif_pos j.2]

theorem ok_eqNum : Spec.ok_eqNum := by
  intro E _ _ g n hn v hv
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hv
  refine le_trans (le_of_eq ?_)
    (cnt_eqN_zero_le g n hn (nat v) ⟨j0.val, j0.2, by rw [nat_fin]; exact hj0⟩)
  congr 1
  funext p
  have h : ∑ j : Fin n, eqN g 0 (nat p) j.val * v j =
      ∑ y ∈ range n, eqN g 0 (nat p) y * nat v y := by
    rw [← Fin.sum_univ_eq_sum_range (fun y => eqN g 0 (nat p) y * nat v y) n]
    exact sum_congr rfl fun j _ => by rw [nat_fin]
  show (∑ j : Fin n, eqN g 0 (nat p) j.val * v j = 0) = _
  rw [h]

theorem comb_eqNum : Spec.comb_eqNum := by
  intro E N _ _ g n hn p f
  show ∑ j : Fin n, eqN g 0 (nat p) j.val • f j.val =
    ∑ X ∈ range (2 ^ g), eqN g 0 (nat p) X • (if X < n then f X else 0)
  rw [Fin.sum_univ_eq_sum_range (fun y => eqN g 0 (nat p) y • f y) n]
  have h1 : ∑ X ∈ range n, eqN g 0 (nat p) X • f X =
      ∑ X ∈ range n, eqN g 0 (nat p) X • (if X < n then f X else 0) :=
    sum_congr rfl fun X hX => by rw [if_pos (mem_range.1 hX)]
  rw [h1]
  exact sum_subset (range_subset_range.2 hn) fun X _ hX => by
    rw [if_neg fun h => hX (mem_range.2 h), smul_zero]

theorem err_eqNum : Spec.err_eqNum := by
  intro E _ _ g n κ h
  exact point_le g
    ((ENNReal.div_le_iff (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)).2 h)

end Cb

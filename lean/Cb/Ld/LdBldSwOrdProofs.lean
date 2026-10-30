-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldSwOrdProofs.lean: the proofs of the statements of Cb/Ld/LdBldSwOrd.lean (book-keeping for
the code switch from one fold into the next). Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.
Main names (statements and hypotheses: Cb/Ld/LdBldSwOrd.lean):
  `bldSwP_rowsNo`: the index of (row b, place j)
  `bldSwP_cor`, `bldSwP_kind`: the corners: injectivity; the last coordinate and the first ones
  `bldSwP_rows`: the batching's rows
  `bldSwP_at`: where each entry stands
  `bldSwP_ok`: see its statement in Cb/Ld/LdBldSwOrd.lean
  `bldSwP_nums`: the four numbers
Limits: what the heads of Cb/Ld/LdBldSw.lean and Cb/Ld/LdBldSwOrd.lean list as not said is not said
here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldSwOrd
import Cb.Ld.LdBldSwProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood Cb.Bld

namespace Bld

theorem ofBits_bitsL {n c : ℕ} (h : c < 2 ^ n) : Nat.ofBits (bitsL n c) = c :=
  (Nat.ofBits_testBit c n).trans (Nat.mod_eq_of_lt h)

theorem bitsL_inj {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : bitsL n a = bitsL n b) :
    a = b := by
  rw [← ofBits_bitsL ha, ← ofBits_bitsL hb, h]

section Cor
variable {mv k lc : ℕ} (b : Fin k → Bool) (c : Fin lc → Bool) (kind : Bool)

theorem corAt_row (i : Fin mv) (hi : i.val < k) : corAt mv k lc b c kind i = b ⟨i.val, hi⟩ :=
  dif_pos hi

theorem corAt_place (i : Fin lc) (hi : k + i.val < mv) :
    corAt mv k lc b c kind ⟨k + i.val, hi⟩ = c i := by
  have h1 : ¬ k + i.val < k := by omega
  have h2 : k + i.val - k < lc := by rw [Nat.add_sub_cancel_left]; exact i.2
  unfold corAt
  rw [dif_neg h1, dif_pos h2]
  exact congrArg c (Fin.ext (Nat.add_sub_cancel_left k i.val))

theorem corAt_last (h : k + lc < mv) (hm : mv - 1 < mv) :
    corAt mv k lc b c kind ⟨mv - 1, hm⟩ = kind := by
  have h1 : ¬ mv - 1 < k := by omega
  have h2 : ¬ mv - 1 - k < lc := by omega
  have h3 : mv - 1 + 1 = mv := by omega
  unfold corAt
  rw [dif_neg h1, dif_neg h2, decide_eq_true h3, Bool.true_and]

theorem corAt_inj (h : k + lc < mv) {b b' : Fin k → Bool} {c c' : Fin lc → Bool} {κ κ' : Bool}
    (e : corAt mv k lc b c κ = corAt mv k lc b' c' κ') : b = b' ∧ c = c' := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · have hi : i.val < mv := by have := i.2; omega
    have e1 := congrFun e ⟨i.val, hi⟩
    rw [corAt_row b c κ ⟨i.val, hi⟩ i.2, corAt_row b' c' κ' ⟨i.val, hi⟩ i.2] at e1
    exact e1
  · have hi : k + i.val < mv := by have := i.2; omega
    have e1 := congrFun e ⟨k + i.val, hi⟩
    rw [corAt_place b c κ i hi, corAt_place b' c' κ' i hi] at e1
    exact e1

end Cor

theorem sumNo_inl {A B : Type} {a b : ℕ} (eA : A ≃ Fin a) (eB : B ≃ Fin b) (x : A) :
    (sumNo eA eB (.inl x)).val = (eA x).val := rfl
theorem sumNo_inr {A B : Type} {a b : ℕ} (eA : A ≃ Fin a) (eB : B ≃ Fin b) (y : B) :
    (sumNo eA eB (.inr y)).val = a + (eB y).val := rfl

end Bld

theorem bldSwP_rowsNo : Spec.bldSwP_rowsNo := fun _ _ _ _ _ _ => rfl

theorem bldSwP_cor : Spec.bldSwP_cor := by
  intro E P' _ Y' N' mv lc lz hC hZ vC vZ
  have hm : mv - 1 < mv := by omega
  rintro (x | x) (y | y) e
  · obtain ⟨e1, e2⟩ := corAt_inj vC e
    have e3 : N'.cJ x.2 = N'.cJ y.2 :=
      Fin.ext (bitsL_inj (lt_of_lt_of_le (N'.cJ x.2).2 hC) (lt_of_lt_of_le (N'.cJ y.2).2 hC) e2)
    exact congrArg Sum.inl (Prod.ext e1 (N'.cJ.injective e3))
  · have e1 := congrFun e ⟨mv - 1, hm⟩
    have a1 : pCor N' mv lc lz (.inl x) ⟨mv - 1, hm⟩ = false := corAt_last _ _ _ vC hm
    have a2 : pCor N' mv lc lz (.inr y) ⟨mv - 1, hm⟩ = true := corAt_last _ _ _ vZ hm
    rw [a1, a2] at e1
    cases e1
  · have e1 := congrFun e ⟨mv - 1, hm⟩
    have a1 : pCor N' mv lc lz (.inr x) ⟨mv - 1, hm⟩ = true := corAt_last _ _ _ vZ hm
    have a2 : pCor N' mv lc lz (.inl y) ⟨mv - 1, hm⟩ = false := corAt_last _ _ _ vC hm
    rw [a1, a2] at e1
    cases e1
  · obtain ⟨e1, e2⟩ := corAt_inj vZ e
    have e3 : N'.zJ x.2 = N'.zJ y.2 :=
      Fin.ext (bitsL_inj (lt_of_lt_of_le (N'.zJ x.2).2 hZ) (lt_of_lt_of_le (N'.zJ y.2).2 hZ) e2)
    exact congrArg Sum.inr (Prod.ext e1 (N'.zJ.injective e3))

theorem bldSwP_kind : Spec.bldSwP_kind := fun _ _ _ _ _ _ _ _ _ vC vZ =>
  ⟨fun _ => corAt_last _ _ _ vC _,
    fun _ => corAt_last _ _ _ vZ _,
    fun _ i hi => corAt_row _ _ _ i hi,
    fun _ i hi => corAt_row _ _ _ i hi⟩

theorem bldSwP_rows : Spec.bldSwP_rows := by
  intro E P _ Y N ts gb
  refine ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun h x y e => ?_⟩
  exact (rowNo N ts).injective
    (Fin.ext (bitsL_inj (lt_of_lt_of_le (rowNo N ts x).2 h) (lt_of_lt_of_le (rowNo N ts y).2 h) e))

theorem bldSwP_at : Spec.bldSwP_at := by
  intro E P P' _ Y Y' N N' fl mv lc lz ts gb h
  refine ⟨fun j => ⟨_, rfl, ?_⟩, fun j => ⟨_, rfl, ?_⟩, fun j => ⟨_, rfl, ?_⟩,
    fun j => ⟨_, rfl, ?_⟩, fun j => ⟨_, rfl, ?_⟩, fun j => ⟨_, rfl, ?_⟩,
    fun j => ⟨_, rfl, ?_⟩, ⟨_, rfl, ?_⟩⟩
  all_goals
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h.rest

theorem bldSwP_ok : Spec.bldSwP_ok := by
  intro E P P' _ _ _ _ Y _ Y' N N' fl mv lc lz ts gb h
  have hc := bldSwP_cor E P' Y' N' mv lc lz h.bC h.bZ h.vC h.vZ
  have hn := (bldSwP_rows E P Y N ts gb).2.2.2.2 h.rows
  have hF : (pZo h).PadFillForm := bldSw_zo E _ (Fin fl) _ (pPlace h) mv _ hc
  have hB : (pZb (E := E) N ts gb).Form := bldSw_zb E _ gb _ hn
  have hO := bldSw_fill E _ _ _ hF
  exact ⟨⟨hO.1, evForm_ok E _ _ hB, hO.2, hF, hB⟩,
    fun e => bldSw_sw E P P' Y Y'.Cin (Fin fl) (pPlace h) mv _ ts gb _ hc hn e⟩

theorem bldSwP_nums : Spec.bldSwP_nums := fun E _ _ _ _ _ _ N _ fl mv lc lz ts gb h =>
  bldSw_nums E _ (Fin fl) _ _ (pPlace h) mv (pCor _ mv lc lz) gb (pNum N ts gb)

end Cb

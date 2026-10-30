-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/LkpAlgProofs.lean: the statements of Cb/Gen/LkpAlg.lean, proved.
-/
import Cb.Gen.LkpAlg

set_option autoImplicit false

namespace Cb
open Finset Prob Cb.Lkp

namespace Lkp
variable {E : Type} [Field E]

open Classical in
/-- An entry that is a bit is 1 or 0 as the test "is it 1" says. -/
theorem eq_ite_of_bit {x : E} (h : x * (x - 1) = 0) :
    x = if decide (x = 1) = true then 1 else 0 := by
  rcases mul_eq_zero.mp h with h | h
  · subst h
    simp
  · have : x = 1 := sub_eq_zero.mp h
    subst this
    simp

open Classical in
/-- The identity of `Spec.planes`, over the index type Fin (2^T), for any bits β with which M agrees
on the first W positions. -/
theorem planes_fin (T W : ℕ) (t : ℕ → E) (M : ℕ → ℕ → E) (al : E) (β : ℕ → ℕ → Bool)
    (hM : ∀ u < 2 ^ T, ∀ j < W, M u j = if β u j = true then 1 else 0) :
    ∏ j ∈ range W, tabProd T t M al j ^ 2 ^ j =
      ∏ u : Fin (2 ^ T), (al - t u) ^ Alg.Lookup.mult W (fun (u : Fin (2 ^ T)) j => β u j) u := by
  rw [← Alg.Lookup.planes_eq W (fun (u : Fin (2 ^ T)) j => β u j) (fun u : Fin (2 ^ T) => t u) al]
  refine prod_congr rfl fun j hj => ?_
  congr 1
  unfold tabProd
  rw [prod_range]
  refine prod_congr rfl fun u _ => ?_
  rw [hM u u.2 j (mem_range.mp hj)]

theorem sum_bits_fin (T W : ℕ) (M : ℕ → ℕ → E) (β : ℕ → ℕ → Bool)
    (hM : ∀ u < 2 ^ T, ∀ j < W, M u j = if β u j = true then 1 else 0) :
    ∑ u ∈ range (2 ^ T), ∑ j ∈ range W, (2 : E) ^ j * M u j =
      ∑ u : Fin (2 ^ T), ∑ j ∈ range W, (2 : E) ^ j * (if β u j = true then (1 : E) else 0) := by
  rw [sum_range]
  refine sum_congr rfl fun u _ => sum_congr rfl fun j hj => ?_
  rw [hM u u.2 j (mem_range.mp hj)]

end Lkp

theorem planes : Spec.planes := by
  classical
  intro E _ T w W t M al hW hB
  rw [planes_fin T W t M al (fun u j => decide (M u j = 1)) fun u hu j hj =>
        eq_ite_of_bit (hB u hu j (lt_of_lt_of_le hj hW)), prod_range]
  rfl

theorem cnt_badAl_le : Spec.cnt_badAl_le := by
  classical
  intro E _ _ p _ n T w W key t M hW hnW hp hnot
  by_cases hBN : Bits T w M ∧ NumKeys n T W M
  · obtain ⟨hB, hN⟩ := hBN
    have hM : ∀ u < 2 ^ T, ∀ j < W, M u j = if decide (M u j = 1) = true then 1 else 0 :=
      fun u hu j hj => eq_ite_of_bit (hB u hu j (lt_of_lt_of_le hj hW))
    set β : Fin (2 ^ T) → ℕ → Bool := fun u j => decide (M u j = 1) with hβ
    have h1 : ∑ u, Alg.Lookup.mult W β u < p := by
      refine lt_of_le_of_lt ?_ hp
      have := Finset.sum_le_card_nsmul (univ : Finset (Fin (2 ^ T))) (Alg.Lookup.mult W β)
        (2 ^ W - 1) fun u _ => Nat.le_sub_one_of_lt (Alg.Lookup.mult_lt W β u)
      simpa using this
    have h2 : 2 ^ n < p := by
      refine lt_of_le_of_lt ?_ hp
      have h3 : 2 ^ n ≤ 2 ^ W - 1 := Nat.le_sub_one_of_lt hnW
      exact le_trans h3 (Nat.le_mul_of_pos_left _ (by positivity))
    have hsum : ∑ u, Alg.Lookup.mult W β u = 2 ^ n := by
      refine Alg.Lookup.sum_mult_eq (E := E) p W β (2 ^ n) ?_ h1 h2
      rw [← hN, sum_bits_fin T W M (fun u j => decide (M u j = 1)) hM]
    unfold InTable at hnot
    push Not at hnot
    obtain ⟨b, hb, hbt⟩ := hnot
    have hc := Alg.Lookup.count_badAlpha_le (fun i : Fin (2 ^ n) => key i)
      (fun u : Fin (2 ^ T) => t u) ⟨0, by positivity⟩ 0 (Alg.Lookup.mult W β)
    rw [Fintype.card_fin] at hc
    refine le_trans (cnt_mono fun al hal => ?_) hc
    refine ⟨by rw [Nat.zero_add, hsum, Fintype.card_fin], ⟨⟨b, hb⟩, fun u => hbt u u.2⟩, ?_⟩
    rw [pow_zero, one_mul, ← planes_fin T W t M al (fun u j => decide (M u j = 1)) hM, ← hal.2.2]
    unfold keyProd
    rw [prod_range]
  · rw [cnt_false fun al hal => hBN ⟨hal.1, hal.2.1⟩]
    exact Nat.zero_le _

theorem mid_of_rows : Spec.mid_of_rows := by
  intro E _ n T w W key t M al PK PT U V hW hB hN hK hT hR
  refine ⟨hB, hN, ?_⟩
  have h := Alg.Lookup.chain_of_rel (W - 1) PT U V hR.top hR.sq hR.mul
  rw [Nat.sub_add_cancel hW] at h
  rw [hK, hR.eq, h]
  exact prod_congr rfl fun j hj => by rw [hT j (mem_range.mp hj)]

theorem relK_iff : Spec.relK_iff := by
  intro E _ n key al PK
  unfold Gp.Rel keyProd facK
  constructor
  · intro h
    simpa using h 0 (by simp)
  · intro h θ hθ
    have : θ = 0 := by simpa using hθ
    subst this
    simpa using h

theorem relT_iff : Spec.relT_iff := by
  intro E _ T w t M al PT
  unfold Gp.Rel tabProd facT
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  have hpos : 0 < 2 ^ w := by positivity
  have e : ∀ u, (u * 2 ^ w + j) / 2 ^ w = u ∧ (u * 2 ^ w + j) % 2 ^ w = j := fun u => by
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [e]

theorem key_end : Spec.key_end := by
  intro E _ n key z al h
  unfold facK
  rw [Blocks.ext_sub, Blocks.ext_const]
  constructor <;> intro h' <;> linear_combination -h'

theorem tab_end : Spec.tab_end := by
  intro E _ T w t M z al h
  unfold facT
  rw [Blocks.ext_add, Blocks.ext_const]
  have : (fun X => M (X / 2 ^ w) (X % 2 ^ w) * (al - 1 - t (X / 2 ^ w))) =
      fun X => (al - 1 - t (X / 2 ^ w)) * M (X / 2 ^ w) (X % 2 ^ w) := by
    funext X
    ring
  rw [this]
  constructor <;> intro h' <;> linear_combination h'

theorem honest_bits : Spec.honest_bits := by
  intro E _ n T w W key t u _ j _
  unfold hbit
  split_ifs <;> simp

namespace Lkp
variable {E : Type} [Field E]

theorem hbit_eq (n W : ℕ) (key t : ℕ → E) (u : ℕ) {j : ℕ} (hj : j < W) :
    hbit n W key t u j = if (hmult n key t u).testBit j = true then 1 else 0 := by
  unfold hbit
  simp [hj]

omit [Field E] in
theorem hmult_lt (n W : ℕ) (key t : ℕ → E) (h : 2 ^ n < 2 ^ W) (u : ℕ) :
    hmult n key t u < 2 ^ W := by
  classical
  refine lt_of_le_of_lt ?_ h
  unfold hmult
  refine le_trans (card_filter_le _ _) ?_
  simp

open Classical in
/-- The honest identity, as polynomials. -/
theorem keySide_eq (n T : ℕ) (key t : ℕ → E) (h : InTable n T key t) :
    Alg.Lookup.keySide (fun i : Fin (2 ^ n) => key i) =
      Alg.Lookup.tableSide (fun u : Fin (2 ^ T) => t u) ⟨0, by positivity⟩ 0
        (fun u : Fin (2 ^ T) => hmult n key t u) := by
  have hex : ∀ i : Fin (2 ^ n), ∃ u, u < 2 ^ T ∧ key i = t u := fun i => h i i.2
  let row : Fin (2 ^ n) → Fin (2 ^ T) := fun i => ⟨Nat.find (hex i), (Nat.find_spec (hex i)).1⟩
  have hk := Alg.Lookup.keySide_eq_tableSide (fun i : Fin (2 ^ n) => key i)
    (fun u : Fin (2 ^ T) => t u) ⟨0, by positivity⟩ (fun _ => False) row
    (fun _ hf => hf.elim) (fun i _ => (Nat.find_spec (hex i)).2)
  rw [hk]
  congr 1
  · simp
  · funext u
    unfold hmult
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, not_false_eq_true]
    constructor
    · intro hr
      have hr' : Nat.find (hex i) = u := congrArg Fin.val hr
      rw [Nat.find_eq_iff] at hr'
      exact ⟨hr'.1.2, fun u' hu' he => hr'.2 u' hu' ⟨lt_trans hu' u.2, he⟩⟩
    · rintro ⟨h1, h2⟩
      refine Fin.ext ?_
      show Nat.find (hex i) = u
      rw [Nat.find_eq_iff]
      exact ⟨⟨u.2, h1⟩, fun u' hu' he => h2 u' hu' he.2⟩

omit [Field E] in
theorem mult_hmult (n T W : ℕ) (key t : ℕ → E) (h : 2 ^ n < 2 ^ W) (u : Fin (2 ^ T)) :
    Alg.Lookup.mult W (fun (u : Fin (2 ^ T)) j => (hmult n key t u).testBit j) u =
      hmult n key t u :=
  Alg.Lookup.mult_testBit W (fun u : Fin (2 ^ T) => hmult n key t u) u (hmult_lt n W key t h u)

end Lkp

theorem honest_ident : Spec.honest_ident := by
  intro E _ n T W key t hW hin al
  rw [planes_fin T W t (hbit n W key t) al (fun u j => (hmult n key t u).testBit j)
      fun u _ j hj => hbit_eq n W key t u hj]
  have h := congrArg (Polynomial.eval al) (keySide_eq n T key t hin)
  rw [Alg.Lookup.keySide_eval, Alg.Lookup.tableSide_eval, pow_zero, one_mul] at h
  unfold keyProd
  rw [prod_range, h]
  exact prod_congr rfl fun u _ => by rw [mult_hmult n T W key t hW u]

theorem honest_numKeys : Spec.honest_numKeys := by
  intro E _ n T W key t hW hin
  unfold NumKeys
  rw [sum_bits_fin T W (hbit n W key t) (fun u j => (hmult n key t u).testBit j)
        fun u _ j hj => hbit_eq n W key t u hj,
    Alg.Lookup.sum_bits_eq W (fun (u : Fin (2 ^ T)) j => (hmult n key t u).testBit j)]
  congr 1
  have h := congrArg Polynomial.natDegree (keySide_eq n T key t hin)
  rw [Alg.Lookup.keySide_natDegree, Alg.Lookup.tableSide_natDegree,
    Fintype.card_fin, Nat.zero_add] at h
  rw [h]
  exact sum_congr rfl fun u _ => mult_hmult n T W key t hW u

theorem honest_rows : Spec.honest_rows := by
  intro E _ W PT hW
  refine ⟨?_, fun j _ => rfl, fun j hj => ?_, ?_⟩
  · unfold hU
    rw [Nat.sub_self]
    rfl
  · unfold hV hU
    rw [show W - 1 - j = (W - 1 - (j + 1)) + 1 by omega]
    rfl
  · unfold hU
    rw [Alg.Lookup.chainFrom_eq_prod, Nat.sub_zero, Nat.sub_add_cancel hW]
    simp

end Cb

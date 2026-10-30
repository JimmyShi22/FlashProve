-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/JohnsonListProofs.lean: the Johnson bound on the size of a list: the proofs of the
statements of Cb/Gen/JohnsonList.lean.

The proof, in the classical steps. Let T_i (i in the list L, of l members) be sets of positions
with exactly t elements each, any two of which share at most s. Let deg j be the number of members
whose set contains the position j.
 1. The sum of deg j over the positions is l t (`sum_deg`): count the pairs (position, member).
 2. The sum of (deg j)^2 is the sum of |T_i ∩ T_i'| over all ordered pairs of members
    (`sum_deg_sq`), which is at most l (t + (l - 1) s) (`sum_inter_le`): a member shares t
    positions with itself and at most s with any other.
 3. By the Cauchy-Schwarz inequality over the n positions, (l t)^2 <= n l (t + (l - 1) s). Dividing
    by l and sorting the terms gives l (t^2 - n s) <= n (t - s) (`arith`).
 4. Sets with more than t elements are cut down to t elements; what two of them share does not grow
    (`johnson_sets`).
 5. For words, T_i is the set of positions at which the i-th word agrees with the centre; where two
    words both agree with the centre they agree with each other (`johnson_agree`). With t = n - e
    and s = n - d this is the bound in distances (`family_aux`).
 6. A table is a word whose symbols are columns; two different tables of messages differ in a row,
    whose two codewords differ in d positions or more, so the two tables of codewords differ in d
    columns or more (`johnson_tables`).

Nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.
Limits: what the head of Cb/Gen/JohnsonList.lean lists as not said is not said here either.
Terms: lean/GLOSSARY.md.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Cb.Gen.JohnsonList

set_option autoImplicit false

namespace Cb
open Prob Blocks

namespace JohnsonList

/-! ## Arithmetic -/

theorem sub_le_sub_of_add_le {a b c e : ℕ} (h : a + e ≤ c + b) : a - b ≤ c - e := by omega

/-- Step 3, second half. -/
theorem arith {l n t s : ℕ} (h : (l * t) ^ 2 ≤ n * (l * (t + (l - 1) * s))) :
    l * (t ^ 2 - n * s) ≤ n * (t - s) := by
  rcases l with _ | k
  · rw [Nat.zero_mul]
    exact Nat.zero_le _
  · rw [Nat.add_sub_cancel] at h
    have h1 : (k + 1) * ((k + 1) * t ^ 2) ≤ (k + 1) * (n * (t + k * s)) :=
      calc (k + 1) * ((k + 1) * t ^ 2) = ((k + 1) * t) ^ 2 := by ring
        _ ≤ n * ((k + 1) * (t + k * s)) := h
        _ = (k + 1) * (n * (t + k * s)) := by ring
    have h2 : (k + 1) * t ^ 2 ≤ n * (t + k * s) := Nat.le_of_mul_le_mul_left h1 (Nat.succ_pos k)
    have h3 : (k + 1) * t ^ 2 + n * s ≤ n * t + (k + 1) * (n * s) :=
      calc (k + 1) * t ^ 2 + n * s ≤ n * (t + k * s) + n * s := Nat.add_le_add_right h2 _
        _ = n * t + (k + 1) * (n * s) := by ring
    rw [Nat.mul_sub, Nat.mul_sub]
    exact sub_le_sub_of_add_le h3

/-! ## The count -/

section Count
variable {I ι : Type} [DecidableEq ι]

/-- The number of members of the list whose set contains the position j. -/
def deg (L : Finset I) (T : I → Finset ι) (j : ι) : ℕ := ∑ i ∈ L, if j ∈ T i then 1 else 0

theorem sum_indicator [Fintype ι] (S : Finset ι) : (∑ j : ι, if j ∈ S then 1 else 0) = S.card := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]

/-- Step 1. -/
theorem sum_deg [Fintype ι] (L : Finset I) (T : I → Finset ι) :
    ∑ j, deg L T j = ∑ i ∈ L, (T i).card := by
  unfold deg
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_indicator (T i)

/-- Step 2, the equation. -/
theorem sum_deg_sq [Fintype ι] (L : Finset I) (T : I → Finset ι) :
    ∑ j, deg L T j ^ 2 = ∑ i ∈ L, ∑ i' ∈ L, (T i ∩ T i').card := by
  have h1 : ∀ j : ι, deg L T j ^ 2 = ∑ i ∈ L, ∑ i' ∈ L, if j ∈ T i ∩ T i' then 1 else 0 := by
    intro j
    unfold deg
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    by_cases h : j ∈ T i <;> by_cases h' : j ∈ T i' <;> simp [h, h']
  calc
    ∑ j, deg L T j ^ 2 = ∑ j, ∑ i ∈ L, ∑ i' ∈ L, (if j ∈ T i ∩ T i' then 1 else 0) :=
      Finset.sum_congr rfl fun j _ => h1 j
    _ = ∑ i ∈ L, ∑ j, ∑ i' ∈ L, (if j ∈ T i ∩ T i' then 1 else 0) := Finset.sum_comm
    _ = ∑ i ∈ L, ∑ i' ∈ L, ∑ j, (if j ∈ T i ∩ T i' then 1 else 0) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ L, ∑ i' ∈ L, (T i ∩ T i').card :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => sum_indicator (T i ∩ T i')

/-- Step 2, the bound. -/
theorem sum_inter_le (L : Finset I) (T : I → Finset ι) (t s : ℕ) (ht : ∀ i ∈ L, (T i).card = t)
    (hs : ∀ i ∈ L, ∀ i' ∈ L, i ≠ i' → (T i ∩ T i').card ≤ s) :
    ∑ i ∈ L, ∑ i' ∈ L, (T i ∩ T i').card ≤ L.card * (t + (L.card - 1) * s) := by
  classical
  have h : ∀ i ∈ L, ∑ i' ∈ L, (T i ∩ T i').card ≤ t + (L.card - 1) * s := by
    intro i hi
    have e1 : ∑ i' ∈ L, (T i ∩ T i').card =
        (T i ∩ T i).card + ∑ i' ∈ L.erase i, (T i ∩ T i').card :=
      (Finset.add_sum_erase L (fun i' => (T i ∩ T i').card) hi).symm
    have e2 : ∑ i' ∈ L.erase i, (T i ∩ T i').card ≤ (L.erase i).card • s :=
      Finset.sum_le_card_nsmul (L.erase i) (fun i' => (T i ∩ T i').card) s fun i' hi' =>
        hs i hi i' (Finset.mem_of_mem_erase hi') (Finset.ne_of_mem_erase hi').symm
    rw [Finset.card_erase_of_mem hi, smul_eq_mul] at e2
    rw [e1, Finset.inter_self, ht i hi]
    exact Nat.add_le_add_left e2 t
  calc
    ∑ i ∈ L, ∑ i' ∈ L, (T i ∩ T i').card ≤ ∑ _i ∈ L, (t + (L.card - 1) * s) := Finset.sum_le_sum h
    _ = L.card * (t + (L.card - 1) * s) := by rw [Finset.sum_const, smul_eq_mul]

/-- Steps 1 to 3: sets with exactly t elements. -/
theorem sets_exact [Fintype ι] (L : Finset I) (T : I → Finset ι) (t s : ℕ)
    (ht : ∀ i ∈ L, (T i).card = t) (hs : ∀ i ∈ L, ∀ i' ∈ L, i ≠ i' → (T i ∩ T i').card ≤ s) :
    L.card * (t ^ 2 - Fintype.card ι * s) ≤ Fintype.card ι * (t - s) := by
  refine arith ?_
  have hS : ∑ j, deg L T j = L.card * t := by
    rw [sum_deg, Finset.sum_congr rfl ht, Finset.sum_const, smul_eq_mul]
  have hCS : (∑ j, deg L T j) ^ 2 ≤ Fintype.card ι * ∑ j, deg L T j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := deg L T)
    rwa [Finset.card_univ, Nat.cast_id] at h
  rw [← hS]
  exact hCS.trans (Nat.mul_le_mul_left _ ((sum_deg_sq L T).le.trans (sum_inter_le L T t s ht hs)))

end Count
end JohnsonList

open JohnsonList

/-! ## Sets and words -/

theorem johnson_sets : Spec.johnson_sets := by
  intro I ι _ _ L T t s ht hs
  have h : ∀ i, ∃ T' : Finset ι, i ∈ L → T' ⊆ T i ∧ T'.card = t := by
    intro i
    by_cases hi : i ∈ L
    · obtain ⟨T', h1, h2⟩ := Finset.exists_subset_card_eq (ht i hi)
      exact ⟨T', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose T' hT' using h
  exact sets_exact L T' t s (fun i hi => (hT' i hi).2) fun i hi i' hi' hne =>
    (Finset.card_le_card (Finset.inter_subset_inter (hT' i hi).1 (hT' i' hi').1)).trans
      (hs i hi i' hi' hne)

theorem johnson_agree : Spec.johnson_agree := by
  intro I ι A _ c w L t s ht hs
  classical
  refine johnson_sets I ι L (fun i => Finset.univ.filter fun j => c i j = w j) t s ?_ ?_
  · intro i hi
    have h := ht i hi
    rw [cnt_eq_card_filter] at h
    exact h
  · intro i hi i' hi' hne
    refine le_trans ?_ (hs i hi i' hi' hne)
    rw [cnt_eq_card_filter]
    refine Finset.card_le_card fun j hj => ?_
    have h1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h1.trans h2.symm⟩

namespace JohnsonList

/-- Step 5: the bound in distances; of the family only the members of the list enter. -/
theorem family_aux {I ι A : Type} [Fintype ι] (c : I → ι → A) (d e : ℕ)
    (hJ : InJohnson (Fintype.card ι) d e) (w : ι → A) (L : Finset I)
    (hd : ∀ i ∈ L, ∀ i' ∈ L, i ≠ i' → d ≤ cnt fun j => c i j ≠ c i' j)
    (hL : ∀ i ∈ L, cnt (fun j => c i j ≠ w j) ≤ e) :
    L.card ≤ listMax (Fintype.card ι) d e := by
  have key := johnson_agree I ι A c w L (Fintype.card ι - e) (Fintype.card ι - d)
    (fun i hi => by
      have h := cnt_add_cnt_not (fun j => c i j = w j)
      have h' : cnt (fun j => ¬ c i j = w j) ≤ e := hL i hi
      omega)
    (fun i hi i' hi' hne => by
      have h := cnt_add_cnt_not (fun j => c i j = c i' j)
      have h' : d ≤ cnt (fun j => ¬ c i j = c i' j) := hd i hi i' hi' hne
      omega)
  unfold listMax
  rw [Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hJ)]
  exact key.trans (Nat.mul_le_mul_left _ (by omega))

/-- A set all of whose finite subsets have at most k elements has at most k elements. -/
theorem encard_le_of_finsets
    {α : Type} {S : Set α} {k : ℕ} (h : ∀ Y : Finset α, (∀ x ∈ Y, x ∈ S) → Y.card ≤ k) :
    S.encard ≤ (k : ℕ∞) := by
  by_cases hf : S.Finite
  · rw [hf.encard_eq_coe_toFinset_card]
    exact_mod_cast h hf.toFinset fun x hx => hf.mem_toFinset.mp hx
  · obtain ⟨Y, hY, hc⟩ := Set.Infinite.exists_subset_card_eq hf (k + 1)
    have := h Y fun x hx => hY (Finset.mem_coe.mpr hx)
    omega

end JohnsonList

theorem johnson_family : Spec.johnson_family := by
  intro I ι A _ c d e hd hJ w L hL
  exact family_aux c d e hJ w L (fun i _ i' _ hne => hd i i' hne) hL

theorem johnson_code : Spec.johnson_code := by
  intro ι A _ Cd d e hd hJ w
  exact encard_le_of_finsets fun Y hY =>
    family_aux (fun c : ι → A => c) d e hJ w Y
      (fun c hc c' hc' hne => hd c (hY c hc).1 c' (hY c' hc').1 hne) fun c hc => (hY c hc).2

/-! ## Tables -/

theorem johnson_tables : Spec.johnson_tables := by
  intro E ι κ _ _ _ G d e hd hJ R f L hL
  refine family_aux (I := R → κ → E) (A := R → E) (fun M j a => G.mulVec (M a) j) d e hJ
    (fun j a => f a j) L ?_ ?_
  · intro M _ M' _ hne
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
    exact (hd.le_cnt_ne ha).trans (cnt_mono fun j hj h => hj (congrFun h a))
  · intro M hM
    refine le_trans (cnt_mono fun j hj => ?_) (hL M hM)
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hj
    exact ⟨a, fun h => ha h.symm⟩

theorem johnson_tables_cnt : Spec.johnson_tables_cnt := by
  intro E ι κ _ _ _ _ G d e hd hJ R _ f
  exact cnt_le_of_forall_finset fun L hL => johnson_tables E ι κ G d e hd hJ R f L hL

theorem johnson_enc : Spec.johnson_enc := by
  intro F E _ _ _ _ C e hd hJ R _ f
  have h := johnson_tables_cnt
    E (Fin C.n) (Fin C.k) (C.GE E) C.d e (HasDist.map (E := E) hd) (by rwa [Fintype.card_fin]) R f
  rwa [Fintype.card_fin] at h

/-! ## The condition and the number -/

theorem inJohnson_anti : Spec.inJohnson_anti := by
  intro n d e e' he h
  exact lt_of_lt_of_le h (Nat.pow_le_pow_left (by omega) 2)

theorem inJohnson_of_unique : Spec.inJohnson_of_unique := by
  intro n d e hdn h2
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hdn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt h2
  unfold InJohnson
  have e1 : 2 * e + r + 1 + m - (2 * e + r + 1) = m := by omega
  have e2 : 2 * e + r + 1 + m - e = e + r + 1 + m := by omega
  have e3 : (e + r + 1 + m) ^ 2 = (2 * e + r + 1 + m) * m + ((e + r + 1) ^ 2 + (r + 1) * m) := by
    ring
  rw [e1, e2, e3]
  exact Nat.lt_add_of_pos_right (by positivity)

theorem listMax_le_of_gap : Spec.listMax_le_of_gap := by
  intro n d e g hg h
  refine ⟨lt_of_lt_of_le (Nat.lt_add_of_pos_right hg) h, ?_⟩
  unfold listMax
  exact Nat.div_le_div_left (Nat.le_sub_of_add_le' h) hg

theorem listMax_le_mul : Spec.listMax_le_mul := by
  intro n d e
  have h : listMax n d e ≤ n * d / ((n - e) ^ 2 - n * (n - d)) :=
    Nat.div_le_div_right (Nat.mul_le_mul_left n (Nat.sub_le d e))
  exact ⟨h, h.trans (Nat.div_le_self _ _)⟩

end Cb

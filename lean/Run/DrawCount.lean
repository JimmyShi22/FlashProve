-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawCount.lean: readers of a row of words at moving places: how many rows give a value.

A reader (`Tr W C`, Run/DrawRow.lean) makes a value from the next words of a row and uses a number
of words that depends on the words, as in rejection sampling; so a reader that comes after it
starts at a place that moves. This file counts the rows of K words on which a reader has a given
value (`N d K t c`); from these counts come the bounds on the bias of such sampling (`Tr.Good`).
Under the hypotheses below (each reader asks for a bounded number of words), the count of a reader
after a reader is a sum of products; of a pair it is the product: the same as if every draw had
words of its own.
Definitions, and theorems with their proofs, on the trees of Run/DrawRow.lean.
Pure counting: the words are any finite type, the values any type, in many statements a finite one;
no field stands in this file.

Main names (the argument d of `N` is left out; "t at most K" is `t.Most K`):
  `N_pad`: t asks for at most K words ⇒ N (K + j) t c = N K t c · |W|^j.
  `N_bind`: t at most K₁, every f a at most K₂ ⇒ N (K₁ + K₂) (t.bind f) c = the sum over a of
    N K₁ t a · N K₂ (f a) c.
  `N_pair`: s at most K₁, t at most K₂ ⇒ N (K₁ + K₂) (pair s t) (c, e) = N K₁ s c · N K₂ t e: the
    product lemma.
  `geo F T n`: T^(n-1) + F T^(n-2) + .. + F^(n-1).
  `N_tries`: N n (tries ok dflt n) c = (the number of words that give c) · geo (the number of words
    that fail) |W| n + (F^n if dflt = c), F the number of words that fail.
  `again t z o`: a value other than z: at most two runs of t: the first value that is not z; if
    both are z: o.
  `good_pad`, `good_map`, `good_pair`, `good_vec`: the law (`Tr.Good`) is kept:
    (K + j, w |W|^j, κ); (K, w, κ) along a bijection; (K₁ + K₂, w₁ w₂, κ₁ κ₂); (n K, w^n, κ^n).

Limits: this file does not say which readers the format has, or the numbers at its two fields:
Run/DrawCountNum.lean. It does not say that a program's function on bytes is such a tree's run. It
says nothing on the tie to Iop/Draw.lean's samplers: Run/DrawBS.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.DrawRow
import Prob.Count
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Run
open Prob
open scoped ENNReal

/-- T^(n-1) + F T^(n-2) + .. + F^(n-1) -/
def geo (F T : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => T ^ n + F * geo F T n

namespace Tr
variable {W C D : Type}

/-- a value other than z: at most two runs of t; then o -/
def again [DecidableEq C] (t : Tr W C) (z : C) (o : {e : C // e ≠ z}) : Tr W {e : C // e ≠ z} :=
  t.bind fun e =>
    if h : e ≠ z then ret ⟨e, h⟩ else t.bind fun e' => if h' : e' ≠ z then ret ⟨e', h'⟩ else ret o

/-! ### At most K words -/

theorem most_mono {t : Tr W C} {K : ℕ} (h : t.Most K) : ∀ {K' : ℕ}, K ≤ K' → t.Most K' := by
  induction h with
  | ret c K => exact fun _ => Most.ret c _
  | ask k K _ ih =>
    intro K' hk
    obtain ⟨K'', rfl⟩ : ∃ K'', K' = K'' + 1 := ⟨K' - 1, by omega⟩
    exact Most.ask k K'' fun w => ih w (by omega)

theorem most_bind {t : Tr W C} {K₁ : ℕ} (h : t.Most K₁) (f : C → Tr W D)
    {K₂ : ℕ} (hf : ∀ a, (f a).Most K₂) : (t.bind f).Most (K₁ + K₂) := by
  induction h with
  | ret c K => exact most_mono (hf c) (Nat.le_add_left _ _)
  | ask k K _ ih =>
    rw [Nat.succ_add]
    exact Most.ask _ _ ih

theorem most_map (g : C → D) {t : Tr W C} {K : ℕ} (h : t.Most K) : (t.map g).Most K :=
  most_bind h _ (K₂ := 0) fun a => Most.ret (g a) 0

theorem most_pair {s : Tr W C} {t : Tr W D} {K₁ K₂ : ℕ} (h₁ : s.Most K₁) (h₂ : t.Most K₂) :
    (pair s t).Most (K₁ + K₂) :=
  most_bind h₁ _ fun _ => most_map _ h₂

theorem most_vec {t : Tr W C} {K : ℕ} (h : t.Most K) : ∀ n, (vec n t).Most (n * K)
  | 0 => Most.ret _ _
  | n + 1 => by
    have e : (n + 1) * K = K + n * K := by ring
    rw [e]
    exact most_map _ (most_pair h (most_vec h n))

theorem most_word : (word : Tr W W).Most 1 := Most.ask _ 0 fun w => Most.ret w 0

theorem most_tries (ok : W → Option C) (dflt : C) : ∀ n, (tries ok dflt n).Most n
  | 0 => Most.ret _ _
  | n + 1 => Most.ask _ n fun w => by
    show (match ok w with | some c => ret c | none => tries ok dflt n).Most n
    cases ok w with
    | some a => exact Most.ret a n
    | none => exact most_tries ok dflt n

theorem most_again [DecidableEq C] {t : Tr W C} {K : ℕ} (h : t.Most K)
    (z : C) (o : {e : C // e ≠ z}) : (again t z o).Most (K + K) :=
  most_bind h _ fun e => by
    by_cases he : e ≠ z
    · rw [dif_pos he]
      exact Most.ret _ _
    · rw [dif_neg he]
      refine most_bind h _ (K₂ := 0) fun e' => ?_
      by_cases he' : e' ≠ z
      · rw [dif_pos he']
        exact Most.ret _ _
      · rw [dif_neg he']
        exact Most.ret _ _

/-! ### The count -/

section
variable [Fintype W] (d : W)

open Classical in
theorem N_ret (K : ℕ) (a c : C) :
    N d K (ret a : Tr W C) c = if a = c then Fintype.card W ^ K else 0 := by
  show cnt (fun _ : Fin K → W => a = c) = _
  split
  · rename_i h
    rw [cnt_congr (Q := fun _ => True) fun _ => iff_true_intro h, cnt_true,
      Fintype.card_fun, Fintype.card_fin]
  · rename_i h
    exact cnt_false fun _ => h

theorem N_ask (K : ℕ) (k : W → Tr W C) (c : C) : N d (K + 1) (ask k) c = ∑ w, N d K (k w) c := by
  show cnt (fun u : Fin (K + 1) → W => ev d (K + 1) (ask k) u = c) = _
  rw [← cnt_equiv (Fin.consEquiv fun _ : Fin (K + 1) => W)
        (fun u : Fin (K + 1) → W => ev d (K + 1) (ask k) u = c), cnt_prod_eq_sum]
  refine Finset.sum_congr rfl fun w _ => cnt_congr fun u => ?_
  show ev d K (k ((Fin.cons w u : Fin (K + 1) → W) 0)) (Fin.tail (Fin.cons w u : Fin (K + 1) → W)) =
      c ↔
    _
  rw [Fin.cons_zero, Fin.tail_cons]

/-- Words that are not read are free. -/
theorem N_pad {t : Tr W C} {K : ℕ} (h : t.Most K) (j : ℕ) (c : C) :
    N d (K + j) t c = N d K t c * Fintype.card W ^ j := by
  induction h with
  | ret a K =>
    rw [N_ret, N_ret]
    split
    · rw [pow_add]
    · rw [zero_mul]
  | ask k K _ ih =>
    rw [Nat.succ_add, N_ask, N_ask, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => ih w

/-- A reader after a reader. -/
theorem N_bind [Fintype C] {t : Tr W C} {K₁ : ℕ} (h : t.Most K₁) (f : C → Tr W D) {K₂ : ℕ}
    (hf : ∀ a, (f a).Most K₂) (c : D) :
    N d (K₁ + K₂) (t.bind f) c = ∑ a, N d K₁ t a * N d K₂ (f a) c := by
  classical
  induction h with
  | ret a K =>
    show N d (K + K₂) (f a) c = _
    rw [Nat.add_comm, N_pad d (hf a), Finset.sum_eq_single a]
    · rw [N_ret, if_pos rfl, mul_comm]
    · intro b _ hb
      rw [N_ret, if_neg (Ne.symm hb), zero_mul]
    · exact fun hn => absurd (Finset.mem_univ a) hn
  | ask k K _ ih =>
    rw [Nat.succ_add]
    show N d (K + K₂ + 1) (ask fun w => (k w).bind f) c = _
    rw [N_ask]
    simp_rw [ih, N_ask, Finset.sum_mul]
    exact Finset.sum_comm

/-- under a one-to-one function (not all hypotheses are named here: see the statement below) -/
theorem N_map_inj [Fintype C] {t : Tr W C} {K : ℕ} (h : t.Most K) (g : C → D)
    (hg : Function.Injective g) (c : C) :
    N d K (t.map g) (g c) = N d K t c := by
  classical
  have e := N_bind d h (fun a => ret (g a)) (K₂ := 0) (fun a => Most.ret (g a) 0) (g c)
  rw [Nat.add_zero] at e
  show N d K (t.bind fun a => ret (g a)) (g c) = _
  rw [e, Finset.sum_eq_single c]
  · rw [N_ret, if_pos rfl, pow_zero, mul_one]
  · intro b _ hb
    rw [N_ret, if_neg fun hh => hb (hg hh), mul_zero]
  · exact fun hn => absurd (Finset.mem_univ c) hn

theorem N_map_equiv [Fintype C] {t : Tr W C} {K : ℕ} (h : t.Most K) (e : C ≃ D) (x : D) :
    N d K (t.map e) x = N d K t (e.symm x) := by
  have := N_map_inj d h e e.injective (e.symm x)
  rwa [e.apply_symm_apply] at this

/-- The product lemma. -/
theorem N_pair [Fintype C] [Fintype D] {s : Tr W C} {t : Tr W D} {K₁ K₂ : ℕ} (h₁ : s.Most K₁)
    (h₂ : t.Most K₂) (c : C) (e : D) :
    N d (K₁ + K₂) (pair s t) (c, e) = N d K₁ s c * N d K₂ t e := by
  classical
  show N d (K₁ + K₂) (s.bind fun a => t.map fun b => (a, b)) (c, e) = _
  rw [N_bind d h₁ _ (fun _ => most_map _ h₂), Finset.sum_eq_single c]
  · rw [N_map_inj d h₂ (fun b => (c, b)) (fun _ _ hh => (Prod.mk.inj hh).2)]
  · intro a _ ha
    have z : N d K₂ (t.map fun b => (a, b)) (c, e) = 0 := by
      have e0 :=
        N_bind d h₂ (fun b => (ret (a, b) : Tr W (C × D))) (K₂ := 0) (fun b => Most.ret _ 0) (c, e)
      rw [Nat.add_zero] at e0
      show N d K₂ (t.bind fun b => ret (a, b)) (c, e) = 0
      rw [e0]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [N_ret, if_neg fun hh => ha (Prod.mk.inj hh).1, mul_zero]
    rw [z, mul_zero]
  · exact fun hn => absurd (Finset.mem_univ c) hn

/-- the product over the coordinates -/
theorem N_vec [Fintype C] {t : Tr W C} {K : ℕ} (h : t.Most K) :
    ∀ (n : ℕ) (x : Fin n → C), N d (n * K) (vec n t) x = ∏ i, N d K t (x i)
  | 0, x => by
    classical
    show N d (0 * K) (ret Fin.elim0 : Tr W (Fin 0 → C)) x = _
    rw [N_ret, if_pos (Subsingleton.elim _ _), Nat.zero_mul, pow_zero,
      Finset.univ_eq_empty, Finset.prod_empty]
  | n + 1, x => by
    have e : (n + 1) * K = K + n * K := by ring
    rw [e]
    show N d (K + n * K) ((pair t (vec n t)).map (Fin.consEquiv fun _ : Fin (n + 1) => C)) x = _
    rw [N_map_equiv d (most_pair h (most_vec h n))]
    show N d (K + n * K) (pair t (vec n t)) (x 0, Fin.tail x) = _
    rw [N_pair d h (most_vec h n), N_vec h n, Fin.prod_univ_succ]
    rfl

open Classical in
/-- At most n tries, then the constant. -/
theorem N_tries (ok : W → Option C) (dflt c : C) :
    ∀ n, N d n (tries ok dflt n) c =
      cnt (fun w => ok w = some c) * geo (cnt fun w => ok w = none) (Fintype.card W) n +
        if dflt = c then (cnt fun w => ok w = none) ^ n else 0
  | 0 => by
    show N d 0 (ret dflt : Tr W C) c = _
    rw [N_ret]
    simp [geo]
  | n + 1 => by
    show N d (n + 1) (ask fun w => match ok w with | some a => ret a | none => tries ok dflt n) c =
      _
    rw [N_ask]
    have hw : ∀ w, N d n (match ok w with | some a => ret a | none => tries ok dflt n) c =
        (if ok w = some c then Fintype.card W ^ n else 0) +
          (if ok w = none then N d n (tries ok dflt n) c else 0) := by
      intro w
      cases hok : ok w with
      | some a =>
        show N d n (ret a : Tr W C) c = _
        rw [N_ret]
        by_cases hac : a = c
        · simp [hac]
        · simp [hac]
      | none => simp
    simp_rw [hw]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
      Finset.sum_const, ← cnt_eq_card_filter, ← cnt_eq_card_filter, N_tries ok dflt c n]
    simp only [smul_eq_mul, geo]
    split
    · ring
    · ring

open Classical in
/-- one word, the value g w -/
theorem N_word_map (g : W → C) (c : C) :
    N d 1 (ask fun w => ret (g w) : Tr W C) c = cnt fun w => g w = c := by
  rw [N_ask]
  simp_rw [N_ret, pow_zero]
  rw [← Finset.sum_filter, Finset.sum_const, ← cnt_eq_card_filter, smul_eq_mul, mul_one]

open Classical in
/-- A value other than z: two runs, then o. -/
theorem N_again [Fintype C] [DecidableEq C] {t : Tr W C} {K : ℕ} (h : t.Most K)
    (z : C) (o c : {e : C // e ≠ z}) :
    N d (K + K) (again t z o) c =
      N d K t c.1 * Fintype.card W ^ K + N d K t z * N d K t c.1 +
        if o = c then N d K t z ^ 2 else 0 := by
  have inner : N d K (t.bind fun e' => if h' : e' ≠ z then ret ⟨e', h'⟩ else ret o) c =
      N d K t c.1 + if o = c then N d K t z else 0 := by
    have e0 := N_bind d h
      (fun e' => if h' : e' ≠ z then (ret ⟨e', h'⟩ : Tr W {e : C // e ≠ z}) else ret o) (K₂ := 0)
      (fun e' => by
        beta_reduce
        by_cases he' : e' ≠ z
        · rw [dif_pos he']
          exact Most.ret _ _
        · rw [dif_neg he']
          exact Most.ret _ _) c
    rw [Nat.add_zero] at e0
    rw [e0, ← Finset.add_sum_erase _ _ (Finset.mem_univ z), dif_neg (not_not.2 rfl), N_ret,
      pow_zero, ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨c.2, Finset.mem_univ c.1⟩),
      dif_pos c.2, N_ret, if_pos (Subtype.ext rfl), pow_zero, Finset.sum_eq_zero]
    · split <;> ring
    · intro b hb
      have hbz : b ≠ z := (Finset.mem_erase.1 (Finset.mem_erase.1 hb).2).1
      have hbc : b ≠ c.1 := (Finset.mem_erase.1 hb).1
      rw [dif_pos hbz, N_ret, if_neg fun hh => hbc (congrArg Subtype.val hh), mul_zero]
  show N d (K + K)
      (t.bind fun e =>
        if h : e ≠ z then ret ⟨e, h⟩
        else t.bind fun e' => if h' : e' ≠ z then ret ⟨e', h'⟩ else ret o) c = _
  rw [N_bind d h _ (fun e => by
      by_cases he : e ≠ z
      · rw [dif_pos he]
        exact Most.ret _ _
      · rw [dif_neg he]
        refine most_bind h _ (K₂ := 0) fun e' => ?_
        by_cases he' : e' ≠ z
        · rw [dif_pos he']
          exact Most.ret _ _
        · rw [dif_neg he']
          exact Most.ret _ _) c,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ z), dif_neg (not_not.2 rfl), inner,
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨c.2, Finset.mem_univ c.1⟩), dif_pos c.2, N_ret,
    if_pos (Subtype.ext rfl), Finset.sum_eq_zero]
  · split <;> ring
  · intro b hb
    have hbz : b ≠ z := (Finset.mem_erase.1 (Finset.mem_erase.1 hb).2).1
    have hbc : b ≠ c.1 := (Finset.mem_erase.1 hb).1
    rw [dif_pos hbz, N_ret, if_neg fun hh => hbc (congrArg Subtype.val hh), mul_zero]

/-! ### The law is kept -/

theorem good_pad {t : Tr W C} {K w : ℕ} {κ : ℝ≥0∞} (h : Good d t K w κ) (j : ℕ) :
    Good d t (K + j) (w * Fintype.card W ^ j) κ where
  most := most_mono h.most (Nat.le_add_right _ _)
  fib := fun c => by
    rw [N_pad d h.most]
    exact Nat.mul_le_mul_right _ (h.fib c)
  ratio := by
    have e := h.ratio
    rw [Nat.card_eq_fintype_card (α := W)] at e ⊢
    push_cast
    calc
      (w : ℝ≥0∞) * (Fintype.card W : ℝ≥0∞) ^ j * (Nat.card C : ℝ≥0∞) =
          (w : ℝ≥0∞) * (Nat.card C : ℝ≥0∞) * (Fintype.card W : ℝ≥0∞) ^ j := by ring
      _ ≤ κ * (Fintype.card W : ℝ≥0∞) ^ K * (Fintype.card W : ℝ≥0∞) ^ j := mul_le_mul' e le_rfl
      _ = κ * (Fintype.card W : ℝ≥0∞) ^ (K + j) := by rw [pow_add, mul_assoc]

theorem good_map [Fintype C] {t : Tr W C} {K w : ℕ} {κ : ℝ≥0∞} (h : Good d t K w κ) (e : C ≃ D) :
    Good d (t.map e) K w κ where
  most := most_map _ h.most
  fib := fun x => by
    rw [N_map_equiv d h.most]
    exact h.fib _
  ratio := by
    rw [← Nat.card_congr e]
    exact h.ratio

theorem good_pair [Fintype C] [Fintype D] {s : Tr W C} {t : Tr W D} {K₁ K₂ w₁ w₂ : ℕ} {κ₁ κ₂ : ℝ≥0∞}
    (h₁ : Good d s K₁ w₁ κ₁) (h₂ : Good d t K₂ w₂ κ₂) :
    Good d (pair s t) (K₁ + K₂) (w₁ * w₂) (κ₁ * κ₂) where
  most := most_pair h₁.most h₂.most
  fib := fun x => by
    obtain ⟨c, e⟩ := x
    rw [N_pair d h₁.most h₂.most]
    exact Nat.mul_le_mul (h₁.fib c) (h₂.fib e)
  ratio := by
    rw [Nat.card_prod]
    push_cast
    calc
      (w₁ : ℝ≥0∞) * w₂ * ((Nat.card C : ℝ≥0∞) * (Nat.card D : ℝ≥0∞)) =
          ((w₁ : ℝ≥0∞) * (Nat.card C : ℝ≥0∞)) * ((w₂ : ℝ≥0∞) * (Nat.card D : ℝ≥0∞)) := by ring
      _ ≤ (κ₁ * (Nat.card W : ℝ≥0∞) ^ K₁) * (κ₂ * (Nat.card W : ℝ≥0∞) ^ K₂) :=
        mul_le_mul' h₁.ratio h₂.ratio
      _ = κ₁ * κ₂ * (Nat.card W : ℝ≥0∞) ^ (K₁ + K₂) := by rw [pow_add]; ring

theorem good_vec [Fintype C] {t : Tr W C} {K w : ℕ} {κ : ℝ≥0∞} (h : Good d t K w κ) (n : ℕ) :
    Good d (vec n t) (n * K) (w ^ n) (κ ^ n) where
  most := most_vec h.most n
  fib := fun x => by
    rw [N_vec d h.most]
    calc ∏ i, N d K t (x i) ≤ ∏ _i : Fin n, w := Finset.prod_le_prod' fun i _ => h.fib (x i)
      _ = w ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ratio := by
    have e : Nat.card (Fin n → C) = Nat.card C ^ n := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    rw [e]
    push_cast
    calc
      (w : ℝ≥0∞) ^ n * (Nat.card C : ℝ≥0∞) ^ n = ((w : ℝ≥0∞) * (Nat.card C : ℝ≥0∞)) ^ n := by
        rw [mul_pow]
      _ ≤ (κ * (Nat.card W : ℝ≥0∞) ^ K) ^ n := pow_le_pow_left' h.ratio n
      _ = κ ^ n * (Nat.card W : ℝ≥0∞) ^ (n * K) := by rw [mul_pow, ← pow_mul, Nat.mul_comm]

end

end Tr
end Run

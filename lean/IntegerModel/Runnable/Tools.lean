-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Runnable/Tools.lean: tools for showing that a program on arrays and Option
(ArrayProgram, IntegerModel/Runnable/ArrayModel.lean) computes the library's formulas (the integer
model, Inst/Model/Program.lean). Nothing here names a model: no model's sizes, weights or tables
occur here. Three groups:
 1. Is r p v: the Option value r is "some v" if p holds and "none" if not; how it passes through
    bind, map and mapM.
 2. tabl n f: the array f 0, .., f (n - 1); its size, entries, map, all, folds, flatMap.
 3. Folds over List.range compared with Finset.sum, maxTo, argTo; an integer root by bits compared
    with Nat.sqrt.
-/
import Inst.Model.Sanity

set_option autoImplicit false

namespace IntegerModel.Runnable

open Inst.Model

/-! ## 1. Option against a proposition -/

/-- r is "some v" if p holds, and "none" if p does not hold -/
def Is {β : Type} (r : Option β) (p : Prop) (v : β) : Prop :=
  (p → r = Option.some v) ∧ (¬ p → r = none)

section Is
variable {α β : Type}

theorem Is.eq_ite {r : Option β} {p : Prop} {v : β} [Decidable p] (h : Is r p v) :
    r = if p then Option.some v else none := by
  by_cases hp : p
  · rw [if_pos hp]; exact h.1 hp
  · rw [if_neg hp]; exact h.2 hp

theorem Is.pure (v : β) : Is (Option.some v) True v := ⟨fun _ => rfl, fun h => absurd trivial h⟩

theorem Is.ofBool (b : Bool) (v : β) : Is (if b = true then Option.some v else none) (b = true) v :=
  ⟨fun h => if_pos h, fun h => if_neg h⟩

theorem Is.iff {r : Option β} {p q : Prop} {v : β} (h : Is r p v) (e : p ↔ q) : Is r q v :=
  ⟨fun hq => h.1 (e.2 hq), fun hq => h.2 fun hp => hq (e.1 hp)⟩

theorem Is.val {r : Option β} {p : Prop} {v u : β} (h : Is r p v) (e : p → v = u) : Is r p u :=
  ⟨fun hp => (h.1 hp).trans (congrArg _ (e hp)), h.2⟩

theorem Is.of {r : Option β} {p q : Prop} {v u : β} (e : p ↔ q) (e2 : p → v = u) (h : Is r p v) :
    Is r q u := (h.val e2).iff e

theorem Is.bind {r : Option α} {f : α → Option β} {p q : Prop} {v : α} {u : β}
    (h : Is r p v) (k : Is (f v) q u) : Is (r.bind f) (p ∧ q) u := by
  constructor
  · rintro ⟨hp, hq⟩
    rw [h.1 hp]
    exact k.1 hq
  · intro hn
    by_cases hp : p
    · rw [h.1 hp]
      exact k.2 fun hq => hn ⟨hp, hq⟩
    · rw [h.2 hp]
      rfl

theorem Is.map {r : Option α} {p : Prop} {v : α} (h : Is r p v) (f : α → β) :
    Is (r.map f) p (f v) :=
  ⟨fun hp => by rw [h.1 hp]; rfl, fun hp => by rw [h.2 hp]; rfl⟩

theorem Is.mapM_list {f : α → Option β} {p : α → Prop} {g : α → β} :
    ∀ (l : List α), (∀ a ∈ l, Is (f a) (p a) (g a)) → Is (l.mapM f) (∀ a ∈ l, p a) (l.map g)
  | [], _ => ⟨fun _ => by simp, fun h => absurd (fun a ha => absurd ha (List.not_mem_nil)) h⟩
  | a :: l, h => by
      have ha := h a (List.mem_cons_self)
      have hl := Is.mapM_list l fun b hb => h b (List.mem_cons_of_mem _ hb)
      have e : (a :: l).mapM f =
          (f a).bind fun y => (l.mapM f).bind fun ys => Option.some (y :: ys) := by
        rw [List.mapM_cons]; rfl
      rw [e]
      refine (Is.bind ha (Is.bind hl (Is.pure (g a :: l.map g)))).iff ?_
      simp only [List.mem_cons, forall_eq_or_imp, and_true]

theorem Is.mapM_array {f : α → Option β} {p : α → Prop} {g : α → β} (a : Array α)
    (h : ∀ x ∈ a.toList, Is (f x) (p x) (g x)) :
    Is (a.mapM f) (∀ x ∈ a.toList, p x) (a.map g) := by
  have e : a.mapM f = (a.toList.mapM f).map List.toArray := by
    rw [Array.mapM_eq_mapM_toList]; rfl
  rw [e]
  have e2 : (a.toList.map g).toArray = a.map g := by
    apply Array.toList_inj.1
    simp
  exact e2 ▸ (Is.mapM_list a.toList h).map List.toArray

end Is

/-! ## 2. The array f 0, .., f (n - 1) -/

/-- the array f 0, .., f (n - 1) -/
abbrev tabl {α : Type} (n : ℕ) (f : ℕ → α) : Array α := (Array.range n).map f

section Tabl
variable {α β : Type}

theorem tabl_size (n : ℕ) (f : ℕ → α) : (tabl n f).size = n := by simp [tabl]

theorem tabl_get [Inhabited α] {n : ℕ} (f : ℕ → α) {i : ℕ} (h : i < n) : (tabl n f)[i]! = f i := by
  simp [tabl, h]

theorem tabl_congr {n : ℕ} {f g : ℕ → α} (h : ∀ i < n, f i = g i) : tabl n f = tabl n g := by
  apply Array.ext
  · simp [tabl]
  · intro i h1 _
    have : i < n := by simpa [tabl] using h1
    simp [tabl, h i this]

theorem tabl_map (n : ℕ) (f : ℕ → α) (g : α → β) : (tabl n f).map g = tabl n fun i => g (f i) := by
  simp [tabl, Function.comp_def]

theorem tabl_toList (n : ℕ) (f : ℕ → α) : (tabl n f).toList = (List.range n).map f := by simp [tabl]

theorem tabl_ofFn (n : ℕ) (f : ℕ → α) : (Array.ofFn fun t : Fin n => f t.val) = tabl n f := by
  apply Array.ext
  · simp [tabl]
  · intro i h1 h2
    simp [tabl]

theorem tabl_foldl (n : ℕ) (f : ℕ → α) (op : β → α → β) (b : β) :
    (tabl n f).foldl op b = (List.range n).foldl (fun s j => op s (f j)) b := by
  rw [← Array.foldl_toList, tabl_toList, List.foldl_map]

theorem tabl_all (n : ℕ) (f : ℕ → α) (p : α → Bool) :
    (tabl n f).all p = true ↔ ∀ i < n, p (f i) = true := by
  rw [← Array.all_toList, tabl_toList]
  simp

theorem Is.mapM_range {n : ℕ} {f : ℕ → Option β} {p : ℕ → Prop}
    {g : ℕ → β} (h : ∀ i < n, Is (f i) (p i) (g i)) :
    Is ((Array.range n).mapM f) (∀ i < n, p i) (tabl n g) := by
  refine (Is.mapM_array (Array.range n) fun x hx => h x (by simpa using hx)).iff ?_
  simp

theorem Is.mapM_tabl {n : ℕ} {t : ℕ → α} {f : α → Option β} {p : ℕ → Prop} {g : ℕ → β}
    (h : ∀ i < n, Is (f (t i)) (p i) (g i)) :
    Is ((tabl n t).mapM f) (∀ i < n, p i) (tabl n g) := by
  have e : (tabl n t).mapM f = (Array.range n).mapM fun i => f (t i) := by
    rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, tabl_toList, List.mapM_map]
    simp [Function.comp_def]
  rw [e]
  exact Is.mapM_range h

/-- rows of one length, one after the other -/
theorem list_flatMap_range (n m : ℕ) (F : ℕ → ℕ → α) :
    (List.range n).flatMap (fun h => (List.range m).map (F h)) =
      (List.range (n * m)).map fun c => F (c / m) (c % m) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add,
        List.map_append, List.map_map]
      congr 1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine List.map_congr_left fun k hk => ?_
      have hk' : k < m := List.mem_range.1 hk
      have hm : 0 < m := by omega
      show F n k = F ((n * m + k) / m) ((n * m + k) % m)
      rw [Nat.mul_comm n m, Nat.mul_add_div hm, Nat.mul_add_mod, Nat.div_eq_of_lt hk',
        Nat.mod_eq_of_lt hk', Nat.add_zero]

theorem tabl_flatMap (n m : ℕ) (F : ℕ → ℕ → α) :
    (Array.range n).flatMap (fun h => tabl m (F h)) = tabl (n * m) fun c => F (c / m) (c % m) := by
  apply Array.toList_inj.1
  rw [Array.toList_flatMap, tabl_toList, ← list_flatMap_range]
  simp [tabl]

end Tabl

/-! ## 3. Folds against Finset.sum, maxTo, argTo; the integer root -/

theorem foldl_sum (g : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun s j => s + g j) 0 = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

theorem foldl_max (f : Vec) (n : ℕ) :
    (List.range (n + 1)).foldl (fun s j => max s (f j)) (f 0) = maxTo f n := by
  induction n with
  | zero => show max (f 0) (f 0) = f 0; exact max_self _
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem foldl_arg (f : Vec) (n : ℕ) :
    (List.range (n + 1)).foldl (fun b j => if f b < f j then j else b) 0 = argTo f n := by
  induction n with
  | zero => show (if f 0 < f 0 then 0 else 0) = 0; exact ite_self _
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem foldl_arg' (f : Vec) (n : ℕ) :
    (List.range n).foldl (fun b j => if f b < f j then j else b) 0 = argTo f (n - 1) := by
  cases n with
  | zero => rfl
  | succ n => exact foldl_arg f n

theorem argTo_congr {f g : Vec} : ∀ n : ℕ, (∀ j ≤ n, f j = g j) → argTo f n = argTo g n
  | 0, _ => rfl
  | n + 1, h => by
      have ih := argTo_congr n fun j hj => h j (Nat.le_succ_of_le hj)
      show (if f (argTo f n) < f (n + 1) then n + 1 else argTo f n) =
        if g (argTo g n) < g (n + 1) then n + 1 else argTo g n
      rw [ih, h (argTo g n) (Nat.le_succ_of_le (argTo_spec g n).1), h (n + 1) le_rfl]

/-- the root, bit by bit from the top -/
theorem bits_sqrt (n : ℕ) : ∀ k r : ℕ, r * r ≤ n → n < (r + 2 ^ k) * (r + 2 ^ k) →
    (let q := (List.range k).reverse.foldl (fun r b => if (r + 2 ^ b) * (r + 2 ^ b) ≤ n then r + 2 ^ b else r) r; q * q ≤ n ∧ n < (q + 1) * (q + 1))
  | 0, r, h1, h2 => ⟨h1, by simpa using h2⟩
  | k + 1, r, h1, h2 => by
      rw [List.range_succ, List.reverse_append]
      show (let q := (List.range k).reverse.foldl _ (if (r + 2 ^ k) * (r + 2 ^ k) ≤ n then r + 2 ^ k else r); q * q ≤ n ∧ n < (q + 1) * (q + 1))
      split_ifs with h
      · exact bits_sqrt n k _ h (by rw [Nat.add_assoc, ← Nat.two_mul, ← Nat.pow_succ']; exact h2)
      · exact bits_sqrt n k _ h1 (not_le.1 h)

theorem bits_sqrt_eq (n : ℕ) :
    (List.range (n.log2 / 2 + 1)).reverse.foldl
        (fun r b => if (r + 2 ^ b) * (r + 2 ^ b) ≤ n then r + 2 ^ b else r) 0 = Nat.sqrt n := by
  refine Nat.eq_sqrt.2 (bits_sqrt n _ 0 (Nat.zero_le _) ?_)
  have h1 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have h2 : n.log2 + 1 ≤ (n.log2 / 2 + 1) + (n.log2 / 2 + 1) := by omega
  calc n < 2 ^ (n.log2 + 1) := h1
    _ ≤ 2 ^ ((n.log2 / 2 + 1) + (n.log2 / 2 + 1)) := Nat.pow_le_pow_right (by norm_num) h2
    _ = (0 + 2 ^ (n.log2 / 2 + 1)) * (0 + 2 ^ (n.log2 / 2 + 1)) := by rw [Nat.zero_add, Nat.pow_add]

end IntegerModel.Runnable

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Blocks.lean: the placing of blocks (layBlocks), for any list of sizes.

layBlocks places a block of 2^a rows for each member that has a size a, from row 0 on, by decreasing
size. This file shows, for every array of sizes: a member has a block just if it has a size; each
block begins at a multiple of its own length and ends within the rows taken in all; two members'
blocks have no row in common.

Main definitions: layStep, LayInv. Main theorem: layBlocks_right.

What is not claimed. Nothing on the order of blocks of one size, and nothing on how few rows are
taken.

-/
import OnBytes.Iop.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

/-- One step of the placing: member i gets the next block if its size is e. -/
def layStep (sizes : Array (Option Nat)) (e : Nat) (acc : Array (Option Nat) × Nat) (i : Nat) :
    Array (Option Nat) × Nat :=
  if sizes.getD i none == some e then (acc.1.setIfInBounds i (some acc.2), acc.2 + 2 ^ e)
  else acc

/-- The greatest size. -/
def topSize (sizes : Array (Option Nat)) : Nat := sizes.foldl (fun m s => max m (s.getD 0)) 0

/-- layBlocks as a fold of layStep. -/
theorem layBlocks_eq (sizes : Array (Option Nat)) :
    layBlocks sizes = (List.range (topSize sizes + 1)).reverse.foldl
      (fun acc e => (List.range sizes.size).foldl (layStep sizes e) acc)
      (Array.replicate sizes.size none, 0) := rfl

/-- Reading an array after one entry was set. -/
theorem getD_set (F : Array (Option Nat)) (i j v : Nat) :
    (F.setIfInBounds i (some v)).getD j none =
      if i = j ∧ i < F.size then some v else F.getD j none := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h
    by_cases h2 : i < F.size
    · simp [h2]
    · simp [h2, Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
  · simp [h]

/-- An index at which an array has something is within the array. -/
theorem lt_of_getD {F : Array (Option Nat)} {i v : Nat} (h : F.getD i none = some v) :
    i < F.size := by
  by_contra hc
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h
  cases h

/-- What holds of the blocks placed so far, while the sizes from e on are being placed. -/
structure LayInv (sizes : Array (Option Nat)) (e : Nat) (st : Array (Option Nat) × Nat) : Prop where
  size : st.1.size = sizes.size
  mult : 2 ^ e ∣ st.2
  placed : ∀ i f, st.1.getD i none = some f →
    ∃ a, sizes.getD i none = some a ∧ e ≤ a ∧ 2 ^ a ∣ f ∧ f + 2 ^ a ≤ st.2
  apart : ∀ i j f f' a a', i ≠ j → st.1.getD i none = some f → st.1.getD j none = some f' →
    sizes.getD i none = some a → sizes.getD j none = some a' → f + 2 ^ a ≤ f' ∨ f' + 2 ^ a' ≤ f

variable {sizes : Array (Option Nat)} {e : Nat} {st : Array (Option Nat) × Nat}

/-- A step keeps it. -/
theorem LayInv.step (h : LayInv sizes e st) (i : Nat) : LayInv sizes e (layStep sizes e st i) := by
  unfold layStep
  by_cases hs : sizes.getD i none = some e
  · have hi : i < st.1.size := by
      rw [h.size]
      exact lt_of_getD hs
    rw [if_pos (by rw [hs]; exact beq_self_eq_true _)]
    refine ⟨by simp [h.size], Nat.dvd_add h.mult (Nat.dvd_refl _), ?_, ?_⟩
    · intro j f hf
      dsimp only at hf ⊢
      rw [getD_set] at hf
      by_cases hij : i = j
      · subst hij
        rw [if_pos ⟨rfl, hi⟩] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨e, hs, Nat.le_refl _, h.mult, Nat.le_refl _⟩
      · rw [if_neg (fun c => hij c.1)] at hf
        obtain ⟨a, h1, h2, h3, h4⟩ := h.placed j f hf
        exact ⟨a, h1, h2, h3, Nat.le_trans h4 (Nat.le_add_right _ _)⟩
    · intro j l f f' a a' hjl hf hf' ha ha'
      dsimp only at hf hf'
      rw [getD_set] at hf hf'
      by_cases h1 : i = j
      · subst h1
        rw [if_pos ⟨rfl, hi⟩] at hf
        rw [if_neg (fun c => hjl c.1)] at hf'
        obtain rfl := Option.some.inj hf
        obtain ⟨b, b1, _, _, b4⟩ := h.placed l f' hf'
        rw [ha'] at b1
        obtain rfl := Option.some.inj b1
        exact Or.inr b4
      · rw [if_neg (fun c => h1 c.1)] at hf
        by_cases h2 : i = l
        · subst h2
          rw [if_pos ⟨rfl, hi⟩] at hf'
          obtain rfl := Option.some.inj hf'
          obtain ⟨b, b1, _, _, b4⟩ := h.placed j f hf
          rw [ha] at b1
          obtain rfl := Option.some.inj b1
          exact Or.inl b4
        · rw [if_neg (fun c => h2 c.1)] at hf'
          exact h.apart j l f f' a a' hjl hf hf' ha ha'
  · rw [if_neg (by simpa using hs)]
    exact h

/-- The steps of one size keep it. -/
theorem LayInv.inner : ∀ (l : List Nat) (st : Array (Option Nat) × Nat), LayInv sizes e st →
    LayInv sizes e (l.foldl (layStep sizes e) st)
  | [], _, h => h
  | i :: l, _, h => LayInv.inner l _ (h.step i)

/-- It goes on to the next smaller size. -/
theorem LayInv.weaken (h : LayInv sizes (e + 1) st) : LayInv sizes e st :=
  ⟨h.size, Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ e)) h.mult,
    fun i f hf => by
      obtain ⟨a, h1, h2, h3⟩ := h.placed i f hf
      exact ⟨a, h1, Nat.le_of_succ_le h2, h3⟩,
    h.apart⟩

/-- The sizes from n down to 0, one after the other. -/
def layAll (sizes : Array (Option Nat)) (l : List Nat) (n : Nat)
    (st : Array (Option Nat) × Nat) : Array (Option Nat) × Nat :=
  (List.range (n + 1)).reverse.foldl (fun acc e => l.foldl (layStep sizes e) acc) st

theorem layAll_zero (l : List Nat) : layAll sizes l 0 st = l.foldl (layStep sizes 0) st := rfl

theorem layAll_succ (l : List Nat) (n : Nat) :
    layAll sizes l (n + 1) st = layAll sizes l n (l.foldl (layStep sizes (n + 1)) st) := by
  unfold layAll
  rw [List.range_succ (n := n + 1), List.reverse_append]
  rfl

/-- All sizes keep it. -/
theorem LayInv.outer (l : List Nat) : ∀ (n : Nat) (st : Array (Option Nat) × Nat),
    LayInv sizes n st → LayInv sizes 0 (layAll sizes l n st)
  | 0, st, h => by
    rw [layAll_zero]
    exact h.inner l st
  | n + 1, st, h => by
    rw [layAll_succ]
    exact LayInv.outer l n _ (h.inner l st).weaken

/-! ## Every member with a size gets a block -/

/-- A step takes no block away. -/
theorem layStep_keeps (i j : Nat) (h : (st.1.getD j none).isSome = true) :
    ((layStep sizes e st i).1.getD j none).isSome = true := by
  unfold layStep
  split
  · dsimp only
    rw [getD_set]
    split
    · rfl
    · exact h
  · exact h

theorem inner_keeps (j : Nat) : ∀ (l : List Nat) (st : Array (Option Nat) × Nat),
    (st.1.getD j none).isSome = true → ((l.foldl (layStep sizes e) st).1.getD j none).isSome = true
  | [], _, h => h
  | i :: l, _, h => inner_keeps j l _ (layStep_keeps i j h)

theorem layAll_keeps (l : List Nat) (j : Nat) : ∀ (n : Nat) (st : Array (Option Nat) × Nat),
    (st.1.getD j none).isSome = true → ((layAll sizes l n st).1.getD j none).isSome = true
  | 0, st, h => by
    rw [layAll_zero]
    exact inner_keeps j l st h
  | n + 1, st, h => by
    rw [layAll_succ]
    exact layAll_keeps l j n _ (inner_keeps j l st h)

/-- The steps of size e give a block to each listed member of that size. -/
theorem inner_places (j : Nat) (hj : sizes.getD j none = some e) :
    ∀ (l : List Nat) (st : Array (Option Nat) × Nat), st.1.size = sizes.size → j ∈ l →
      ((l.foldl (layStep sizes e) st).1.getD j none).isSome = true
  | [], _, _, h => by cases h
  | i :: l, st, hs, h => by
    rw [List.foldl_cons]
    by_cases hij : i = j
    · subst hij
      apply inner_keeps
      unfold layStep
      rw [if_pos (by rw [hj]; exact beq_self_eq_true _)]
      dsimp only
      rw [getD_set, if_pos ⟨rfl, by rw [hs]; exact lt_of_getD hj⟩]
      rfl
    · have h' : j ∈ l := by
        rcases List.mem_cons.1 h with c | c
        · exact absurd c.symm hij
        · exact c
      apply inner_places j hj l _ _ h'
      unfold layStep
      split
      · simp [hs]
      · exact hs

/-- All sizes: each listed member with a size up to n gets a block. -/
theorem layAll_places (l : List Nat) (j a : Nat) (hj : sizes.getD j none = some a) (hl : j ∈ l) :
    ∀ (n : Nat) (st : Array (Option Nat) × Nat), LayInv sizes n st → a ≤ n →
      ((layAll sizes l n st).1.getD j none).isSome = true
  | 0, st, h, ha => by
    obtain rfl : a = 0 := Nat.le_zero.1 ha
    rw [layAll_zero]
    exact inner_places j hj l st h.size hl
  | n + 1, st, h, ha => by
    rw [layAll_succ]
    by_cases c : a = n + 1
    · subst c
      exact layAll_keeps l j n _ (inner_places j hj l st h.size hl)
    · exact layAll_places l j a hj hl n _ (h.inner l st).weaken (by omega)

/-- No size is above the greatest. -/
theorem le_topSize (j a : Nat) (hj : sizes.getD j none = some a) : a ≤ topSize sizes := by
  have gen : ∀ (l : List (Option Nat)) (m : Nat),
      m ≤ l.foldl (fun m s => max m (s.getD 0)) m ∧
        ∀ s ∈ l, s.getD 0 ≤ l.foldl (fun m s => max m (s.getD 0)) m := by
    intro l
    induction l with
    | nil => intro m; exact ⟨Nat.le_refl _, by simp⟩
    | cons s l ih =>
      intro m
      rw [List.foldl_cons]
      obtain ⟨i1, i2⟩ := ih (max m (s.getD 0))
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) i1, ?_⟩
      intro t ht
      rcases List.mem_cons.1 ht with c | c
      · subst c
        exact Nat.le_trans (Nat.le_max_right _ _) i1
      · exact i2 t c
  have hi := lt_of_getD hj
  have hm : some a ∈ sizes.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at hj
    have e : sizes[j] = some a := hj
    rw [← e]
    exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
  unfold topSize
  rw [← Array.foldl_toList]
  exact (gen sizes.toList 0).2 _ hm

/-- The start. -/
theorem LayInv.start (n : Nat) : LayInv sizes n (Array.replicate sizes.size none, 0) := by
  have h0 : ∀ i, (Array.replicate sizes.size (none : Option Nat)).getD i none = none := by
    intro i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  refine ⟨by simp, Nat.dvd_zero _, ?_, ?_⟩
  · intro i f hf
    rw [h0] at hf
    cases hf
  · intro i j f f' a a' _ hf
    rw [h0] at hf
    cases hf

/-- **The placing of blocks is in order**, for every array of sizes. -/
theorem layBlocks_right (sizes : Array (Option Nat)) :
    (∀ i f, (layBlocks sizes).1.getD i none = some f →
      ∃ a, sizes.getD i none = some a ∧ 2 ^ a ∣ f ∧ f + 2 ^ a ≤ (layBlocks sizes).2) ∧
    (∀ i j f f' a a', i ≠ j → (layBlocks sizes).1.getD i none = some f →
      (layBlocks sizes).1.getD j none = some f' → sizes.getD i none = some a →
      sizes.getD j none = some a' → f + 2 ^ a ≤ f' ∨ f' + 2 ^ a' ≤ f) ∧
    (∀ i a, sizes.getD i none = some a → ∃ f, (layBlocks sizes).1.getD i none = some f) := by
  have e : layBlocks sizes = layAll sizes (List.range sizes.size) (topSize sizes)
      (Array.replicate sizes.size none, 0) := layBlocks_eq sizes
  have inv := LayInv.outer (List.range sizes.size) (topSize sizes) _
    (LayInv.start (sizes := sizes) (topSize sizes))
  rw [← e] at inv
  refine ⟨?_, inv.apart, ?_⟩
  · intro i f hf
    obtain ⟨a, h1, _, h3, h4⟩ := inv.placed i f hf
    exact ⟨a, h1, h3, h4⟩
  · intro i a hi
    have p := layAll_places (List.range sizes.size) i a hi (List.mem_range.2 (lt_of_getD hi))
      (topSize sizes) _ (LayInv.start (sizes := sizes) (topSize sizes)) (le_topSize i a hi)
    rw [← e] at p
    exact Option.isSome_iff_exists.1 p

end OnBytes.Means

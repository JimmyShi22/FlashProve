-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/WalkLaw.lean: given a list R of wanted counts (one a place, the places numbered from
i) and a SORTED list rs of places, all at i or above: that each place stands in rs as often as R
wants can be tested by ONE walk down both lists, in place of a count over all of rs at every place.

Why. Measured outside this tree, at the 48,293 rounds of the proof file's first chain
(`dryProofFull_length`, Johnson/G/DryProofLit.lean) and 83 numbers: the count at every place, asked
of Lean's kernel, was ended by a cap on memory of 8 GiB after 46 s; the walk was borne (two walks in
27 s; 5.07 GiB with mapped files).

Definition.
  `walkN R i rs`: at the place i as many heads of rs are i as R wants; these are dropped; on to i +
    1.
Statements. General.
  `mem_take_eq`, `lt_of_mem_drop`, `count_split`: on `takeWhile` and `dropWhile` of a sorted list.
  **`walkN_sound`**: where rs is sorted, all of it lies at i or above, and the walk accepts: every
    place stands in rs as often as R wants.
Tests: `walk_yes`; negative: `walk_no`.

Limits. Sound; that the walk accepts wherever the counts are right is not shown. No import: Lean's
own library alone.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds

/-- One walk: at the place i as many heads of rs are i as R wants; these are dropped; on to i + 1.
-/
def walkN : List Nat → Nat → List Nat → Bool
  | [], _, _ => true
  | r :: R, i, rs =>
    (r == (rs.takeWhile (· == i)).length) && walkN R (i + 1) (rs.dropWhile (· == i))

/-- What `takeWhile` keeps is i. -/
theorem mem_take_eq {i x : Nat} : ∀ {rs : List Nat}, x ∈ rs.takeWhile (· == i) → x = i
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ha : a = i
    · have e : (a :: t).takeWhile (· == i) = a :: t.takeWhile (· == i) := by simp [ha]
      rw [e] at h
      cases List.mem_cons.1 h with
      | inl e' => rw [e', ha]
      | inr hm => exact mem_take_eq hm
    · have e : (a :: t).takeWhile (· == i) = [] := by simp [ha]
      rw [e] at h
      cases h

/-- Behind the heads that are i a sorted list from i on holds only larger places. -/
theorem lt_of_mem_drop {i : Nat} : ∀ {rs : List Nat}, rs.Pairwise (· ≤ ·) → (∀ x ∈ rs, i ≤ x) →
    ∀ x ∈ rs.dropWhile (· == i), i < x
  | [], _, _, x, hx => by simp at hx
  | a :: t, hs, hl, x, hx => by
    have hs' := List.pairwise_cons.1 hs
    by_cases ha : a = i
    · have : (a :: t).dropWhile (· == i) = t.dropWhile (· == i) := by
        simp [ha]
      rw [this] at hx
      exact lt_of_mem_drop hs'.2 (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx
    · have : (a :: t).dropWhile (· == i) = a :: t := by
        simp [ha]
      rw [this] at hx
      have hai : i < a := Nat.lt_of_le_of_ne (hl a List.mem_cons_self) (fun e => ha e.symm)
      cases List.mem_cons.1 hx with
      | inl e => rw [e]; exact hai
      | inr hm => exact Nat.lt_of_lt_of_le hai (hs'.1 x hm)

/-- The count of a place splits along `takeWhile` and `dropWhile`. -/
theorem count_split (j i : Nat) (rs : List Nat) :
    rs.count j = (rs.takeWhile (· == i)).count j + (rs.dropWhile (· == i)).count j := by
  rw [← List.count_append, List.takeWhile_append_dropWhile]

/-- **Where rs is sorted, all of it lies at i or above, and the walk accepts: every place stands in
rs as often as R wants.** -/
theorem walkN_sound : ∀ (R : List Nat) (i : Nat) (rs : List Nat), rs.Pairwise (· ≤ ·) →
    (∀ x ∈ rs, i ≤ x) → walkN R i rs = true → ∀ e ∈ R.zipIdx i, rs.count e.2 = e.1
  | [], _, _, _, _, _, e, he => by simp at he
  | r :: R, i, rs, hs, hl, hw, e, he => by
    rw [walkN, Bool.and_eq_true] at hw
    have h1 : r = (rs.takeWhile (· == i)).length := by simpa using hw.1
    have hd := lt_of_mem_drop hs hl
    rw [List.zipIdx_cons] at he
    cases List.mem_cons.1 he with
    | inl e0 =>
      rw [e0]
      show rs.count i = r
      rw [count_split i i rs, h1]
      have a : (rs.takeWhile (· == i)).count i = (rs.takeWhile (· == i)).length :=
        List.count_eq_length.2 fun b hb => (mem_take_eq hb).symm
      have b : (rs.dropWhile (· == i)).count i = 0 :=
        List.count_eq_zero.2 fun hm => Nat.lt_irrefl i (hd i hm)
      rw [a, b, Nat.add_zero]
    | inr hm =>
      have hs' : (rs.dropWhile (· == i)).Pairwise (· ≤ ·) :=
        hs.sublist (List.dropWhile_sublist _)
      have ih := walkN_sound R (i + 1) (rs.dropWhile (· == i)) hs' (fun x hx => hd x hx) hw.2 e hm
      have hj : i < e.2 := by
        have := List.le_snd_of_mem_zipIdx hm
        omega
      rw [count_split e.2 i rs, ih]
      have a : (rs.takeWhile (· == i)).count e.2 = 0 :=
        List.count_eq_zero.2 fun hx => Nat.lt_irrefl i (by rw [mem_take_eq hx] at hj; exact hj)
      rw [a, Nat.zero_add]

/-- A closed test. -/
theorem walk_yes : walkN [2, 0, 1, 0] 0 [0, 0, 2] = true := by decide +kernel
/-- A negative test, stated positively: with one place bent the walk says no. -/
theorem walk_no : walkN [2, 0, 1, 0] 0 [0, 2, 2] = false := by decide +kernel

end Johnson.Unfolds

#print axioms Johnson.Unfolds.mem_take_eq
#print axioms Johnson.Unfolds.lt_of_mem_drop
#print axioms Johnson.Unfolds.count_split
#print axioms Johnson.Unfolds.walkN_sound
#print axioms Johnson.Unfolds.walk_yes
#print axioms Johnson.Unfolds.walk_no

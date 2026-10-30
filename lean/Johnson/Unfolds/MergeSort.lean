-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/MergeSort.lean: `List.mergeSort` in a form that Lean's kernel can evaluate, and the
equation between the two, at all lists and every comparison `le`.

ADAPTED from Lean 4's core library (toolchain v4.29.1): `List.merge`, `List.mergeSort`,
`List.MergeSort.Internal.splitInTwo`. What is theirs: the routines' text, as Lean prints their
equations (`List.merge.eq_1` to `eq_3`, `List.mergeSort.eq_1` to `eq_3`,
`List.MergeSort.Internal.splitInTwo.eq_1`). What is ours: the bound on the steps and the laws.
Licence of the adapted text, as a program read it off the toolchain's own file LICENSE (71 lines;
sha256 8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e): its first lines are
"Apache License 2.0 (Apache)", "Apache License", "Version 2.0, January 2004".
The adapted file's own header, as a program read it off the toolchain's sources
(src/lean/Init/Data/List/Sort/Basic.lean, 101 lines, sha256
a100c2a753aae0dda38a6e3afaca64f7ea70f4eba73d007ac29b5889fbf842ac; the three definitions stand at its
lines 39, 60 and 79):
  Copyright (c) 2024 Lean FRO. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Kim Morrison

Why. Asked by `decide +kernel` whether `[3, 1, 2].mergeSort` is `[1, 2, 3]`, Lean reports that the
instance "did not reduce to `isTrue` or `isFalse`": the kernel's check fails, at an input so small
that no limit can be at work (seen at lists of two and of three members; at none and at one the
check passes). Our reading: `List.merge`, beneath it, recurses by well-foundedness, and that
recursion is not unfolded there. So a closed statement whose evaluation reaches a sort of two or
more members is not had that way. Behind one rewriting with `mergeSort_eq` it is.

Main names.
  `mergeF le n`, `sortF le n`: the two routines' texts with a bound n in front: each call of itself
    stands at the bound less one; at the bound 0 the result is `none`. They recurse on the bound.
  `mergeF_sound`, `sortF_sound`: where the bounded text returns a list, the library's routine has
    that value. By induction on the bound. Nothing on termination, order or stability is used.
  `mergeF_returns`, `sortF_returns`: the bounded text returns where the bound is above the two
    lengths' sum, or above the length.
  `mergeSort_eq`: `xs.mergeSort le = (sortF le (xs.length + 1) xs).getD []`.
How to use it: `simp only [mergeSort_eq]` (it reaches under binders), then `decide +kernel`.
Tests: `sort_three`, `sort_ties` (members with one key keep their order), `sorts_under_a_binder`;
negative: `sort_three_no`.

Limits. The bounded text does the library's work over again and is no faster. A bound of the
list's length + 1 is far above the depth that is needed. Evaluation in the kernel of a sort of a
long list has not been measured. No import: Lean's own library alone.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds

universe u

/-- `List.merge` with a bound on its steps. -/
def mergeF {α : Type u} (le : α → α → Bool) : Nat → List α → List α → Option (List α)
  | 0, _, _ => none
  | _ + 1, [], ys => some ys
  | _ + 1, x :: xs, [] => some (x :: xs)
  | n + 1, x :: xs, y :: ys =>
    if le x y = true then (mergeF le n xs (y :: ys)).map (x :: ·)
    else (mergeF le n (x :: xs) ys).map (y :: ·)

/-- **Where the bounded text returns a list, `List.merge` has that value.** -/
theorem mergeF_sound {α : Type u} (le : α → α → Bool) : ∀ (n : Nat) (xs ys l : List α),
    mergeF le n xs ys = some l → xs.merge ys le = l
  | 0, _, _, _, h => by
    rw [mergeF] at h
    cases h
  | _ + 1, [], ys, l, h => by
    rw [mergeF] at h
    rw [List.merge.eq_1]
    exact Option.some.inj h
  | _ + 1, x :: xs, [], l, h => by
    rw [mergeF] at h
    rw [List.merge.eq_2 _ _ (by intro e; cases e)]
    exact Option.some.inj h
  | n + 1, x :: xs, y :: ys, l, h => by
    rw [mergeF] at h
    rw [List.merge.eq_3]
    by_cases c : le x y = true
    · rw [if_pos c] at h ⊢
      cases e : mergeF le n xs (y :: ys) with
      | none =>
        rw [e] at h
        cases h
      | some t =>
        rw [e] at h
        rw [mergeF_sound le n _ _ _ e]
        exact Option.some.inj h
    · rw [if_neg c] at h ⊢
      cases e : mergeF le n (x :: xs) ys with
      | none =>
        rw [e] at h
        cases h
      | some t =>
        rw [e] at h
        rw [mergeF_sound le n _ _ _ e]
        exact Option.some.inj h

/-- `List.mergeSort` with a bound on its depth. -/
def sortF {α : Type u} (le : α → α → Bool) : Nat → List α → Option (List α)
  | 0, _ => none
  | _ + 1, [] => some []
  | _ + 1, [a] => some [a]
  | n + 1, a :: b :: xs =>
    (sortF le n (List.splitAt (((a :: b :: xs).length + 1) / 2) (a :: b :: xs)).1).bind fun L =>
      (sortF le n (List.splitAt (((a :: b :: xs).length + 1) / 2) (a :: b :: xs)).2).bind fun R =>
        mergeF le (L.length + R.length + 1) L R

/-- **Where the bounded text returns a list, `List.mergeSort` has that value.** -/
theorem sortF_sound {α : Type u} (le : α → α → Bool) : ∀ (n : Nat) (xs l : List α),
    sortF le n xs = some l → xs.mergeSort le = l
  | 0, _, _, h => by
    rw [sortF] at h
    cases h
  | _ + 1, [], l, h => by
    rw [sortF] at h
    rw [List.mergeSort.eq_1]
    exact Option.some.inj h
  | _ + 1, [a], l, h => by
    rw [sortF] at h
    rw [List.mergeSort.eq_2]
    exact Option.some.inj h
  | n + 1, a :: b :: xs, l, h => by
    rw [sortF] at h
    rw [List.mergeSort.eq_3]
    show ((List.splitAt (((a :: b :: xs).length + 1) / 2) (a :: b :: xs)).1.mergeSort le).merge
      ((List.splitAt (((a :: b :: xs).length + 1) / 2) (a :: b :: xs)).2.mergeSort le) le = l
    cases e1 : sortF le n (List.splitAt (((a :: b :: xs).length + 1) / 2) (a :: b :: xs)).1 with
    | none =>
      rw [e1] at h
      cases h
    | some L =>
      cases e2 : sortF le n (List.splitAt (((a :: b :: xs).length + 1) / 2) (a :: b :: xs)).2 with
      | none =>
        rw [e1, e2] at h
        cases h
      | some R =>
        rw [e1, e2] at h
        rw [sortF_sound le n _ _ e1, sortF_sound le n _ _ e2]
        exact mergeF_sound le _ _ _ _ h

/-- The bounded `List.merge` returns where the bound is above the two lengths. -/
theorem mergeF_returns {α : Type u} (le : α → α → Bool) : ∀ (n : Nat) (xs ys : List α),
    xs.length + ys.length < n → ∃ l, mergeF le n xs ys = some l
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], ys, _ => ⟨ys, by rw [mergeF]⟩
  | _ + 1, x :: xs, [], _ => ⟨x :: xs, by rw [mergeF]⟩
  | n + 1, x :: xs, y :: ys, h => by
    rw [mergeF]
    by_cases c : le x y = true
    · rw [if_pos c]
      obtain ⟨t, ht⟩ := mergeF_returns le n xs (y :: ys) (by
        simp only [List.length_cons] at h ⊢
        omega)
      exact ⟨x :: t, by rw [ht]; rfl⟩
    · rw [if_neg c]
      obtain ⟨t, ht⟩ := mergeF_returns le n (x :: xs) ys (by
        simp only [List.length_cons] at h ⊢
        omega)
      exact ⟨y :: t, by rw [ht]; rfl⟩

/-- The bounded `List.mergeSort` returns where the bound is above the length. -/
theorem sortF_returns {α : Type u} (le : α → α → Bool) : ∀ (n : Nat) (xs : List α),
    xs.length < n → ∃ l, sortF le n xs = some l
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _ => ⟨[], by rw [sortF]⟩
  | _ + 1, [a], _ => ⟨[a], by rw [sortF]⟩
  | n + 1, a :: b :: xs, h => by
    rw [sortF]
    obtain ⟨L, hL⟩ := sortF_returns le n
      (List.splitAt (((a :: b :: xs).length + 1) / 2) (a :: b :: xs)).1 (by
        rw [List.splitAt_eq]
        simp only [List.length_take, List.length_cons] at h ⊢
        omega)
    obtain ⟨R, hR⟩ := sortF_returns le n
      (List.splitAt (((a :: b :: xs).length + 1) / 2) (a :: b :: xs)).2 (by
        rw [List.splitAt_eq]
        simp only [List.length_drop, List.length_cons] at h ⊢
        omega)
    obtain ⟨l, hl⟩ := mergeF_returns le (L.length + R.length + 1) L R (Nat.lt_succ_self _)
    exact ⟨l, by rw [hL, hR]; exact hl⟩

/-- **`List.mergeSort` is the bounded text at a bound above the length**, at all lists and every
comparison `le`. -/
theorem mergeSort_eq {α : Type u} (le : α → α → Bool) (xs : List α) :
    xs.mergeSort le = (sortF le (xs.length + 1) xs).getD [] := by
  obtain ⟨l, hl⟩ := sortF_returns le (xs.length + 1) xs (Nat.lt_succ_self _)
  rw [hl, sortF_sound le _ _ _ hl, Option.getD_some]

/-- Sorts under a binder, decided whole behind one rewriting. -/
theorem sorts_under_a_binder :
    ([[3, 1, 2], [2, 1], [5, 4, 9, 0]] : List (List Nat)).map
      (fun l => l.mergeSort fun a b => decide (a ≤ b)) = [[1, 2, 3], [1, 2], [0, 4, 5, 9]] := by
  simp only [mergeSort_eq]
  decide +kernel

/-- The list at which the kernel's check of the library's routine failed. -/
theorem sort_three :
    ([3, 1, 2] : List Nat).mergeSort (fun a b => decide (a ≤ b)) = [1, 2, 3] :=
  sortF_sound _ 8 _ _ (by decide +kernel)

/-- With ties: members with one key keep their order. -/
theorem sort_ties :
    ([(1, 7), (0, 5), (1, 6), (0, 4)] : List (Nat × Nat)).mergeSort
      (fun a b => decide (a.1 ≤ b.1)) = [(0, 5), (0, 4), (1, 7), (1, 6)] :=
  sortF_sound _ 8 _ _ (by decide +kernel)

/-- A negative test, by the recipe of the head: the sorted list is no other list. -/
theorem sort_three_no :
    ([3, 1, 2] : List Nat).mergeSort (fun a b => decide (a ≤ b)) ≠ [1, 3, 2] := by
  simp only [mergeSort_eq]
  decide +kernel

end Johnson.Unfolds

#print axioms Johnson.Unfolds.mergeF_sound
#print axioms Johnson.Unfolds.sortF_sound
#print axioms Johnson.Unfolds.mergeF_returns
#print axioms Johnson.Unfolds.sortF_returns
#print axioms Johnson.Unfolds.mergeSort_eq
#print axioms Johnson.Unfolds.sorts_under_a_binder
#print axioms Johnson.Unfolds.sort_three
#print axioms Johnson.Unfolds.sort_ties
#print axioms Johnson.Unfolds.sort_three_no

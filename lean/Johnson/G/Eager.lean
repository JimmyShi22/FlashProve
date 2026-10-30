-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/Eager.lean: counting along a long list in a way that Lean's kernel can evaluate without
running out of stack.

The kernel evaluates lazily. A number that is carried along a list and grows at each step (a length,
a sum, an index) stays an unevaluated term as deep as the list is long; when it is asked for at
last, the kernel descends through all of it, and at some tens of thousands of steps it runs out of
stack. `force n k` makes the kernel evaluate n to a numeral before k gets it, so the carried term
stays shallow. Definitions and proofs.
Main names:
  `force n k`, `force_eq : force n k = k n`.
  `lenE a l`, `lenE_eq : lenE a l = a + l.length`, `length_of_lenE`: a list's length from an
    evaluation of `lenE 0 l`.
  `sumE a l`, `sumE_eq : sumE a l = a + l.sum`.
Limits: general; no value is treated. That the kernel gets through a given list is seen where a
theorem is checked, not shown here.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

/-- Hands n to k; the match makes the kernel evaluate n first. -/
def force {α : Type} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem force_eq {α : Type} (n : Nat) (k : Nat → α) : force n k = k n := by
  cases n <;> rfl

/-- a plus the length of the list. -/
def lenE {α : Type} : Nat → List α → Nat
  | a, [] => a
  | a, _ :: xs => force (a + 1) fun v => lenE v xs

theorem lenE_eq {α : Type} (l : List α) : ∀ a, lenE a l = a + l.length := by
  induction l with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    simp only [lenE, force_eq, ih, List.length_cons]
    omega

theorem length_of_lenE {α : Type} {l : List α} {n : Nat} (h : lenE 0 l = n) : l.length = n := by
  rw [lenE_eq] at h
  omega

/-- a plus the sum of the list. -/
def sumE : Nat → List Nat → Nat
  | a, [] => a
  | a, x :: xs => force (a + x) fun v => sumE v xs

theorem sumE_eq (l : List Nat) : ∀ a, sumE a l = a + l.sum := by
  induction l with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    simp only [sumE, force_eq, ih, List.sum_cons]
    omega

end Johnson.G

#print axioms Johnson.G.length_of_lenE
#print axioms Johnson.G.sumE_eq

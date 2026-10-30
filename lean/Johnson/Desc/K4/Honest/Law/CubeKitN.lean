-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/CubeKitN.lean: CONDITIONAL. Four definitions, and statements with their
proofs.

What is here. Tools for the law on `polyInY` (Johnson/Desc/K4/Honest/Law/CubeInY.lean): Newton's
forward differences over a field.

  `binomP k`   X (X - 1) .. (X - k + 1) / k!; the polynomial 0 where k! is 0 in the field
  `newtonP l k`   the sum of l's members times `binomP k`, `binomP (k + 1)`, ..
  `dseq n v`   the values at 0 of v and of its first n - 1 successive differences
  `newton_nodes`   at a number m below n the differences, under binomial coefficients, give v m
  `newton_eq`   **a polynomial of degree at most dY is `newtonP` of its own differences**
  Beside these, smaller steps: `chooseSum` (a definition), `choose_cast`, `binomP_eval`,
  `binomP_deg`, `newtonP_deg`, `newtonP_eval`, `chooseSum_zero`, `chooseSum_pascal`, `cast_inj_of`.

Limits. Nothing here speaks of the program. The numbers 1, .., dY are units of the field by a
hypothesis.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.CubeTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.K4.Honest.CubeLaw
open Polynomial

variable {K : Type} [Field K]

/-- X (X - 1) .. (X - k + 1) / k!; the polynomial 0 where k! is 0 in the field. -/
def binomP : ℕ → K[X]
  | 0 => 1
  | k + 1 => C ((k : K) + 1)⁻¹ * (binomP k * (X - C (k : K)))

/-- The members of l times `binomP k`, `binomP (k + 1)`, .., summed. -/
def newtonP : List K → ℕ → K[X]
  | [], _ => 0
  | d :: l, k => C d * binomP k + newtonP l (k + 1)

/-- The members of l times the binomial coefficients of m over k, k + 1, .., summed. -/
def chooseSum : List K → ℕ → ℕ → K
  | [], _, _ => 0
  | d :: l, m, k => d * (m.choose k : K) + chooseSum l m (k + 1)

/-- The values at 0 of v, of its differences, of their differences, ..: n members. -/
def dseq : ℕ → (ℕ → K) → List K
  | 0, _ => []
  | n + 1, v => v 0 :: dseq n (fun i => v (i + 1) - v i)

theorem choose_cast (m k : ℕ) :
    ((m.choose (k + 1) : ℕ) : K) * ((k : K) + 1) =
      ((m.choose k : ℕ) : K) * ((m : K) - (k : K)) := by
  rcases Nat.lt_or_ge m k with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_lt h)]
    simp
  · have c := congrArg (Nat.cast : ℕ → K) (Nat.choose_succ_right_eq m k)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h, Nat.cast_succ] at c
    exact c

theorem binomP_eval (B : ℕ) (hinv : ∀ i, i < B → ((i : K) + 1) ≠ 0) (m : ℕ) :
    ∀ k, k ≤ B → (binomP k : K[X]).eval (m : K) = (m.choose k : K)
  | 0, _ => by simp [binomP]
  | k + 1, hk => by
    rw [binomP, eval_mul, eval_C, eval_mul, eval_sub, eval_X, eval_C,
      binomP_eval B hinv m k (Nat.le_of_succ_le hk), ← choose_cast,
      mul_comm ((m.choose (k + 1) : ℕ) : K), ← mul_assoc, inv_mul_cancel₀ (hinv k hk), one_mul]

theorem binomP_deg : ∀ k, (binomP k : K[X]).natDegree ≤ k
  | 0 => by simp [binomP]
  | k + 1 => by
    have h1 : (binomP k : K[X]).natDegree ≤ k := binomP_deg k
    have h2 : (X - C (k : K)).natDegree ≤ 1 := natDegree_X_sub_C_le _
    rw [binomP]
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    omega

theorem newtonP_deg : ∀ (l : List K) (k : ℕ), (newtonP l k).natDegree ≤ k + l.length - 1
  | [], _ => by simp [newtonP]
  | d :: l, k => by
    have h1 : (C d * binomP k : K[X]).natDegree ≤ k :=
      (natDegree_C_mul_le _ _).trans (binomP_deg k)
    have h2 := newtonP_deg l (k + 1)
    rw [newtonP, List.length_cons]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_) <;> omega

theorem newtonP_eval (B : ℕ) (hinv : ∀ i, i < B → ((i : K) + 1) ≠ 0) (m : ℕ) :
    ∀ (l : List K) (k : ℕ), k + l.length ≤ B + 1 → (newtonP l k).eval (m : K) = chooseSum l m k
  | [], _, _ => by simp [newtonP, chooseSum]
  | d :: l, k, h => by
    rw [List.length_cons] at h
    rw [newtonP, chooseSum, eval_add, eval_mul, eval_C, binomP_eval B hinv m k (by omega),
      newtonP_eval B hinv m l (k + 1) (by omega)]

theorem chooseSum_zero : ∀ (l : List K) (k : ℕ), chooseSum l 0 (k + 1) = 0
  | [], _ => rfl
  | d :: l, k => by
    rw [chooseSum, chooseSum_zero l (k + 1), Nat.choose_zero_succ]
    simp

theorem chooseSum_pascal : ∀ (l : List K) (m k : ℕ),
    chooseSum l (m + 1) (k + 1) = chooseSum l m k + chooseSum l m (k + 1)
  | [], _, _ => by simp [chooseSum]
  | d :: l, m, k => by
    rw [chooseSum, chooseSum, chooseSum, chooseSum_pascal l m (k + 1), Nat.choose_succ_succ,
      Nat.cast_add]
    ring

/-- At a number m below n the differences, under binomial coefficients, give v m. -/
theorem newton_nodes : ∀ (m n : ℕ) (v : ℕ → K), m < n → chooseSum (dseq n v) m 0 = v m
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | 0, n + 1, v, _ => by
    rw [dseq, chooseSum, chooseSum_zero]
    simp
  | m + 1, n + 1, v, h => by
    have i1 := newton_nodes m (n + 1) v (by omega)
    have i2 := newton_nodes m n (fun i => v (i + 1) - v i) (by omega)
    rw [dseq, chooseSum, Nat.choose_zero_right, Nat.cast_one, mul_one] at i1 ⊢
    rw [chooseSum_pascal, i2]
    linear_combination i1

theorem cast_inj_of (dY : ℕ) (hinv : ∀ i, i < dY → ((i : K) + 1) ≠ 0) :
    ∀ a b : ℕ, a < b → b ≤ dY → (a : K) ≠ (b : K) := by
  intro a b hab hb h
  obtain ⟨i, rfl⟩ : ∃ i, b = a + (i + 1) := ⟨b - a - 1, by omega⟩
  apply hinv i (by omega)
  rw [Nat.cast_add, Nat.cast_succ] at h
  linear_combination -h

/-- **A polynomial of degree at most dY is `newtonP` of its own differences at 0, .., dY.** -/
theorem newton_eq (dY : ℕ) (hinv : ∀ i, i < dY → ((i : K) + 1) ≠ 0) (P : K[X])
    (hP : P.natDegree ≤ dY) : newtonP (dseq (dY + 1) fun k => P.eval (k : K)) 0 = P := by
  have hlen : ∀ (n : ℕ) (v : ℕ → K), (dseq n v).length = n := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih => intro v; rw [dseq, List.length_cons, ih]
  have hz : newtonP (dseq (dY + 1) fun k => P.eval (k : K)) 0 - P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (ι := Fin (dY + 1))
      (f := fun i => ((i.val : ℕ) : K)) ?_ ?_ ?_
    · intro a b hab
      by_contra hne
      have hv : a.val ≠ b.val := fun e => hne (Fin.ext e)
      rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
      · exact cast_inj_of dY hinv a.val b.val hlt (Nat.le_of_lt_succ b.isLt) hab
      · exact cast_inj_of dY hinv b.val a.val hgt (Nat.le_of_lt_succ a.isLt) hab.symm
    · intro i
      rw [eval_sub, newtonP_eval dY hinv i.val _ 0 (by rw [hlen]; omega),
        newton_nodes i.val (dY + 1) _ i.isLt, sub_self]
    · rw [Fintype.card_fin]
      have h1 := newtonP_deg (dseq (dY + 1) fun k => P.eval (k : K)) 0
      rw [hlen] at h1
      have h2 := natDegree_sub_le (newtonP (dseq (dY + 1) fun k => P.eval (k : K)) 0) P
      have h3 := max_le (a := (newtonP (dseq (dY + 1) fun k => P.eval (k : K)) 0).natDegree)
        (b := P.natDegree) (c := dY) (by omega) hP
      omega
  exact sub_eq_zero.mp hz

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.binomP
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.newtonP
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.chooseSum
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.dseq
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.choose_cast
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.binomP_eval
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.binomP_deg
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.newtonP_deg
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.newtonP_eval
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.chooseSum_zero
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.chooseSum_pascal
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.newton_nodes
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.cast_inj_of
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.newton_eq

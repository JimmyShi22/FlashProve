-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Unfolds/Count.lean: counting in one block of numbers, and so the layers' count of padding
keys at a tree. Statements with their proofs; nothing is evaluated.
  `sum_zero` | `in_block`: two tools. `block_le`: T summed over the numbers x below n with x / M = t
    of which the test Q says yes is at most T times the count of the numbers below n in that block.
    `block_lt`: with one T to spare, if Q says no of a number x₀ below n of that block.
  `pubOf_in` | `pubOf_out` | `pubOf_le` | `pubOf_lt`: so for OnBytes.Road.pubOf
    (Johnson/Road/FormsKeysPub.lean) at a call's own trees, outside them, and the two bounds.

Limits. Nothing on soundness.
-/
import Johnson.Road.FormsKeysPub

set_option autoImplicit false

namespace Johnson.Unfolds
open OnBytes OnBytes.Model OnBytes.Model.Layer

theorem sum_zero {α : Type} (f : α → Nat) : ∀ l : List α, (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, h a (List.mem_cons_self ..),
      sum_zero f l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem in_block {n M t : Nat} (hM : 0 < M) (h : n / M = t) : t * M ≤ n ∧ n < t * M + M := by
  subst h
  refine ⟨Nat.div_mul_le_self n M, ?_⟩
  have := Nat.lt_mul_div_succ n hM
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at this
  exact this

theorem block_le (Q : Nat → Bool) (T M t : Nat) (hM : 0 < M) : ∀ n,
    ((List.range n).map fun x => if Q x = true ∧ x / M = t then T else 0).sum ≤
      (min n (t * M + M) - min n (t * M)) * T
  | 0 => by simp
  | n + 1 => by
    have ih := block_le Q T M t hM n
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hc : Q n = true ∧ n / M = t
    · rw [if_pos hc]
      obtain ⟨h1, h2⟩ := in_block hM hc.2
      generalize t * M = a at *
      have e : min (n + 1) (a + M) - min (n + 1) a = (min n (a + M) - min n a) + 1 := by omega
      rw [e, Nat.add_mul, Nat.one_mul]
      omega
    · rw [if_neg hc, Nat.add_zero]
      generalize t * M = a at *
      exact Nat.le_trans ih (Nat.mul_le_mul_right _ (by omega))

theorem block_lt (Q : Nat → Bool) (T M t x₀ : Nat) (hM : 0 < M) (h0 : Q x₀ = false)
    (ht : x₀ / M = t) : ∀ n,
    ((List.range n).map fun x => if Q x = true ∧ x / M = t then T else 0).sum +
        (if x₀ < n then T else 0) ≤ (min n (t * M + M) - min n (t * M)) * T
  | 0 => by simp
  | n + 1 => by
    have ih := block_lt Q T M t x₀ hM h0 ht n
    obtain ⟨w1, w2⟩ := in_block hM ht
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hc : Q n = true ∧ n / M = t
    · rw [if_pos hc]
      have hne : x₀ ≠ n := fun e => by rw [e, hc.1] at h0; exact absurd h0 (by decide)
      obtain ⟨h1, h2⟩ := in_block hM hc.2
      generalize t * M = a at *
      have e : min (n + 1) (a + M) - min (n + 1) a = (min n (a + M) - min n a) + 1 := by omega
      rw [e, Nat.add_mul, Nat.one_mul]
      by_cases hx : x₀ < n
      · rw [if_pos hx] at ih
        rw [if_pos (by omega)]
        omega
      · rw [if_neg hx] at ih
        rw [if_neg (by omega)]
        omega
    · rw [if_neg hc, Nat.add_zero]
      generalize t * M = a at *
      by_cases hx : x₀ < n
      · rw [if_pos hx] at ih
        rw [if_pos (by omega)]
        exact Nat.le_trans ih (Nat.mul_le_mul_right _ (by omega))
      · rw [if_neg hx] at ih
        by_cases hx' : x₀ < n + 1
        · rw [if_pos hx']
          have en : x₀ = n := by omega
          subst en
          have e : min (x₀ + 1) (a + M) - min (x₀ + 1) a = (min x₀ (a + M) - min x₀ a) + 1 := by
            omega
          rw [e, Nat.add_mul, Nat.one_mul]
          omega
        · rw [if_neg hx']
          exact Nat.le_trans ih (Nat.mul_le_mul_right _ (by omega))

variable (y : Layer.Lay) (first dT : Nat) (cd : CallD)

theorem pubOf_in (t : Nat) : OnBytes.Road.pubOf y first dT cd (first + t) =
    ((List.range (y.Lam * cd.J)).map fun x =>
      if (cd.padding (x / cd.J) (x % cd.J)) = true ∧ x / 2 ^ (dT - y.h.lt) = t then y.T else 0).sum
      := by
  unfold OnBytes.Road.pubOf
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Nat.add_left_cancel_iff]

theorem pubOf_out {A θ : Nat} (hfit : y.Lam * cd.J ≤ 2 ^ (dT - y.h.lt) * A)
    (hθ : θ < first ∨ first + A ≤ θ) : OnBytes.Road.pubOf y first dT cd θ = 0 := by
  unfold OnBytes.Road.pubOf
  refine sum_zero _ _ fun x hx => ?_
  have hx' : x < y.Lam * cd.J := List.mem_range.1 hx
  have hd : x / 2 ^ (dT - y.h.lt) < A :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hx' hfit)
  rw [if_neg]
  rintro ⟨_, e⟩
  generalize x / 2 ^ (dT - y.h.lt) = d at hd e
  omega

theorem pubOf_le (t : Nat) :
    OnBytes.Road.pubOf y first dT cd (first + t) ≤ 2 ^ (dT - y.h.lt) * y.T := by
  rw [pubOf_in]
  refine Nat.le_trans (block_le (fun x => cd.padding (x / cd.J) (x % cd.J)) y.T
    (2 ^ (dT - y.h.lt)) t (Nat.two_pow_pos _) _) (Nat.mul_le_mul_right _ ?_)
  generalize 2 ^ (dT - y.h.lt) = M
  generalize t * M = a
  omega

theorem pubOf_lt {x₀ : Nat} (hx : x₀ < y.Lam * cd.J)
    (h0 : cd.padding (x₀ / cd.J) (x₀ % cd.J) = false) :
    OnBytes.Road.pubOf y first dT cd (first + x₀ / 2 ^ (dT - y.h.lt)) + y.T ≤
      2 ^ (dT - y.h.lt) * y.T := by
  rw [pubOf_in]
  have k := block_lt (fun x => cd.padding (x / cd.J) (x % cd.J)) y.T (2 ^ (dT - y.h.lt))
    (x₀ / 2 ^ (dT - y.h.lt)) x₀ (Nat.two_pow_pos _) h0 rfl (y.Lam * cd.J)
  rw [if_pos hx] at k
  refine Nat.le_trans k (Nat.mul_le_mul_right _ ?_)
  generalize 2 ^ (dT - y.h.lt) = M
  generalize x₀ / M * M = a
  omega

end Johnson.Unfolds

#print axioms Johnson.Unfolds.sum_zero
#print axioms Johnson.Unfolds.in_block
#print axioms Johnson.Unfolds.block_le
#print axioms Johnson.Unfolds.block_lt
#print axioms Johnson.Unfolds.pubOf_in
#print axioms Johnson.Unfolds.pubOf_out
#print axioms Johnson.Unfolds.pubOf_le
#print axioms Johnson.Unfolds.pubOf_lt

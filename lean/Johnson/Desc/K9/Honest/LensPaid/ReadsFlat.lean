-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensPaid/ReadsFlat.lean (kind K9): the library's count of reads `readsB`
(Johnson/Desc/First/Link/K9RowsAsk.lean) adds, matrix by matrix, what each table of that matrix reads. Where every table
names a matrix below the number of matrices, that is the sum over the tables. Three lemmas; no definition.

  `foldl_sum`     a fold that adds f x to a number is that number plus the sum of the f x (the library's `foldl_add`,
                   Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean, typed again: this file imports the definitions alone)
  `sum_pick`      of the numbers below NM the one that is i is picked once
  **`readsB_flat`**   every table's matrix below NM: `readsB NM mats ps` is the sum over ps of (the matrix's m) / (the
                   table's length)

Limits. A table whose matrix is not below NM is counted by no matrix: there the two sides can part, so the premise is
needed. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.First.Link.K9RowsAsk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9Asks (readsB)

/-- A fold that adds f x to a number is that number plus the sum of the f x. -/
theorem foldl_sum {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : ℕ),
    l.foldl (fun n x => n + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_sum f l, List.map_cons, List.sum_cons]
    omega

/-- Of the numbers below NM the one that is i is picked once. -/
theorem sum_pick (g : ℕ → ℕ) (i : ℕ) : ∀ NM : ℕ, i < NM →
    ((List.range NM).map fun mu => if i = mu then g mu else 0).sum = g i
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases e : i = n
    · subst e
      have z : ((List.range i).map fun mu => if i = mu then g mu else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨mu, hm, rfl⟩ := List.mem_map.1 hx
        have := List.mem_range.1 hm
        rw [if_neg (by omega)]
      rw [z]
      simp
    · rw [sum_pick g i n (by omega)]
      simp [e]

/-- **The count of reads is the sum over the tables**, where every table names a matrix below NM. -/
theorem readsB_flat (NM : ℕ) (mats : Array TMat) (ps : List (ℕ × ℕ)) (h : ∀ t ∈ ps, t.1 < NM) :
    readsB NM mats ps = (ps.map fun t => (mats.getD t.1 {}).m / t.2).sum := by
  have e : ∀ mu : ℕ, ps.foldl (fun k t => k + if t.1 = mu then (mats.getD mu {}).m / t.2 else 0) 0 =
      (ps.map fun t : ℕ × ℕ => if t.1 = mu then (mats.getD mu {}).m / t.2 else 0).sum := fun mu => by
    rw [foldl_sum (fun t : ℕ × ℕ => if t.1 = mu then (mats.getD mu {}).m / t.2 else 0), Nat.zero_add]
  unfold readsB
  rw [foldl_sum (fun mu => ps.foldl
    (fun k t => k + if t.1 = mu then (mats.getD mu {}).m / t.2 else 0) 0), Nat.zero_add,
    List.map_congr_left (fun mu _ => e mu)]
  clear e
  induction ps with
  | nil => simp
  | cons t ps ih =>
    have ht : t.1 < NM := h t (List.mem_cons.2 (Or.inl rfl))
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_add, ih (fun t' h' => h t' (List.mem_cons.2 (Or.inr h')))]
    congr 1
    exact sum_pick (fun mu => (mats.getD mu {}).m / t.2) t.1 NM ht

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.foldl_sum
#print axioms ProofFile.Honest.K9.sum_pick
#print axioms ProofFile.Honest.K9.readsB_flat

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules6Laws.lean: the list of the drawn positions (`listOf`) is what the rule (R6.6) says: the
set of the draws, strictly increasing.

The draws are the positions in a round's verifier message, in the order drawn, repeats kept. Merkle
openings go by the list, which has each drawn position once, in increasing order. Fmt/Rules6.lean
defines `listOf`: by `insertIntoIncreasingList`, each draw is put into its place in an increasing list, and a repeat
is dropped.

Sources. R6.6 of the format page (docs/format/FORMAT.md); this file has not been held against the
page as it ships, and may differ from it. No Mathlib.


1. What the file contains. Statements (three on `listOf`, each a `Prop` in `Fmt.Spec`; three on
`insertIntoIncreasingList`, stated outright) and proofs.

2. What is checked when the file compiles. Only the proofs.

3. Theorems.
   `listOf_mem`: a number is in the list if and only if it occurs among the draws.
   `listOf_incr`: the list is strictly increasing (so no number occurs in it twice).
   `listOf_len`: the list is no longer than the draws.
   The first two fix the list: a strictly increasing list is determined by its members (a remark; no
   theorem here). A walk over pruned openings (`walkW`, Fmt/Rules7.lean) goes, at each depth
   (`walkLevelW`), through the places in order and joins neighbours. It relies on "strictly
   increasing".
   Tools of the proofs: `mem_insertN`, `incr_insertN`, `len_insertN`.

4. What is not claimed. Nothing on openings.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules6

namespace Fmt

theorem mem_insertN (x y : Nat) : ∀ l : List Nat, y ∈ insertIntoIncreasingList x l ↔ y = x ∨ y ∈ l
  | [] => by simp [insertIntoIncreasingList]
  | z :: l => by
    unfold insertIntoIncreasingList
    by_cases h1 : x < z
    · rw [if_pos h1]
      simp
    · rw [if_neg h1]
      by_cases h2 : x = z
      · rw [if_pos h2]
        subst h2
        simp
      · rw [if_neg h2, List.mem_cons, mem_insertN x y l, List.mem_cons]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

theorem incr_insertN (x : Nat) : ∀ l : List Nat, l.Pairwise (· < ·) → (insertIntoIncreasingList x l).Pairwise (· < ·)
  | [], _ => by simp [insertIntoIncreasingList]
  | z :: l, h => by
    have hz := (List.pairwise_cons.1 h).1
    have hl := (List.pairwise_cons.1 h).2
    unfold insertIntoIncreasingList
    by_cases h1 : x < z
    · rw [if_pos h1]
      refine List.pairwise_cons.2 ⟨fun a ha => ?_, h⟩
      rcases List.mem_cons.1 ha with rfl | ha
      · exact h1
      · exact Nat.lt_trans h1 (hz a ha)
    · rw [if_neg h1]
      by_cases h2 : x = z
      · rw [if_pos h2]
        exact h
      · rw [if_neg h2]
        refine List.pairwise_cons.2 ⟨fun a ha => ?_, incr_insertN x l hl⟩
        rcases (mem_insertN x a l).1 ha with rfl | ha
        · omega
        · exact hz a ha

theorem len_insertN (x : Nat) : ∀ l : List Nat, (insertIntoIncreasingList x l).length ≤ l.length + 1
  | [] => Nat.le_refl _
  | z :: l => by
    unfold insertIntoIncreasingList
    by_cases h1 : x < z
    · rw [if_pos h1]
      exact Nat.le_refl _
    · rw [if_neg h1]
      by_cases h2 : x = z
      · rw [if_pos h2]
        exact Nat.le_succ _
      · rw [if_neg h2]
        exact Nat.succ_le_succ (len_insertN x l)

/-- States: the list holds the draws and nothing else. -/
def Spec.listOf_mem : Prop := ∀ (l : List Nat) (x : Nat), x ∈ listOf l ↔ x ∈ l

/-- States: the list is strictly increasing. -/
def Spec.listOf_incr : Prop := ∀ l : List Nat, (listOf l).Pairwise (· < ·)

def Spec.listOf_len : Prop := ∀ l : List Nat, (listOf l).length ≤ l.length

theorem listOf_mem : Spec.listOf_mem := by
  intro l x
  induction l with
  | nil => exact Iff.rfl
  | cons a l ih =>
    show x ∈ insertIntoIncreasingList a (listOf l) ↔ _
    rw [mem_insertN, ih, List.mem_cons]

theorem listOf_incr : Spec.listOf_incr := by
  intro l
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih => exact incr_insertN a _ ih

theorem listOf_len : Spec.listOf_len := by
  intro l
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih => exact Nat.le_trans (len_insertN a _) (Nat.succ_le_succ ih)

end Fmt

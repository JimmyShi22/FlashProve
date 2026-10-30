-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BookTestsLaw.lean: EACH OF THE FIVE TESTS ON A BOOK
(Johnson/Desc/Sound/BookTests.lean) SAYS YES
JUST WHERE ITS CONDITION HOLDS. Theorems with their proofs: five "iff".

  `bookFitsB_iff` (`BookFits`, Johnson/Desc/Book/BookFits.lean) · `placedB_iff` · `tenantB_iff` (the
  two clauses of `BookedLast`,
  WordsAt.lean, in their letters) · `numberedBookB_iff`, `numberedLastB_iff` (SeamAt.lean).
  `placedB_of_fits`: the first test's yes gives the second's.

Both directions: a filling of a table's book-keeping wants the Bool back from "the block's yes gives
the condition".
Limits. Book-keeping on plain data: nothing on soundness. THE TESTS' VALUES AT ANY RECORD OF A RIDE:
not
here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BookTests
import Johnson.Desc.Sound.SeamAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Third (SharedOut)

theorem bookFitsB_iff (B : TreeBook) : bookFitsB B = true ↔ BookFits B := by
  constructor
  · intro h i q hq
    have hi : i < B.place.size := (Array.getElem?_eq_some_iff.1 hq).1
    have h₁ := List.all_eq_true.1 h i (List.mem_range.2 hi)
    rw [hq] at h₁
    have h₂ : (match B.trees[q.1]? with
      | some t => decide (t.parts[q.2]? = some i)
      | none => false) = true := h₁
    cases ht : B.trees[q.1]? with
    | none =>
      rw [ht] at h₂
      cases h₂
    | some t =>
      rw [ht] at h₂
      exact ⟨t, rfl, of_decide_eq_true h₂⟩
  · intro h
    refine List.all_eq_true.2 fun i _ => ?_
    cases hq : B.place[i]? with
    | none => rfl
    | some q =>
      obtain ⟨t, ht, hp⟩ := h i q hq
      show (match B.trees[q.1]? with
        | some t => decide (t.parts[q.2]? = some i)
        | none => false) = true
      rw [ht]
      exact decide_eq_true hp

theorem placedB_iff (B : TreeBook) :
    placedB B = true ↔ ∀ (i : ℕ) (q : ℕ × ℕ), B.place[i]? = some q → q.1 < B.trees.size := by
  constructor
  · intro h i q hq
    have hi : i < B.place.size := (Array.getElem?_eq_some_iff.1 hq).1
    have h₁ := List.all_eq_true.1 h i (List.mem_range.2 hi)
    rw [hq] at h₁
    exact of_decide_eq_true h₁
  · intro h
    refine List.all_eq_true.2 fun i _ => ?_
    cases hq : B.place[i]? with
    | none => rfl
    | some q => exact decide_eq_true (h i q hq)

theorem placedB_of_fits (B : TreeBook) (h : bookFitsB B = true) : placedB B = true :=
  (placedB_iff B).2 fun i q hq => Book.placed_of_fits ((bookFitsB_iff B).1 h) i q hq

theorem tenantB_iff (o : SharedOut) :
    tenantB o = true ↔ ∀ q : ℕ × ℕ, o.book.place[o.omega]? = some q → q.2 = 0 := by
  unfold tenantB
  cases hq : o.book.place[o.omega]? with
  | none =>
    constructor
    · intro _ q h
      cases h
    · intro _
      rfl
  | some q =>
    constructor
    · intro h q' e
      obtain rfl := Option.some.inj e
      exact eq_of_beq h
    · intro h
      exact beq_iff_eq.2 (h q rfl)

theorem numberedBookB_iff (ft : ℕ) (B : TreeBook) :
    numberedBookB ft B = true ↔ NumberedBook ft B := by
  constructor
  · intro h j t ht
    have hj : j < B.trees.size := (Array.getElem?_eq_some_iff.1 ht).1
    have h₁ := List.all_eq_true.1 h j (List.mem_range.2 hj)
    rw [ht] at h₁
    exact eq_of_beq h₁
  · intro h
    refine List.all_eq_true.2 fun j _ => ?_
    cases ht : B.trees[j]? with
    | none => rfl
    | some t => exact beq_iff_eq.2 (h j t ht)

theorem numberedLastB_iff (t₁ t₂ ft : ℕ) (B : TreeBook) :
    numberedLastB t₁ t₂ ft B = true ↔ NumberedLast t₁ t₂ ft B := by
  unfold numberedLastB
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hf, h⟩
    have key : ∀ z T, B.trees[z]? = some T →
        (if z + 1 = ft then decide (T.number < t₂) else T.number == z) = true := by
      intro z T hT
      have hz : z < B.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
      have h₁ := List.all_eq_true.1 h z (List.mem_range.2 hz)
      rw [hT] at h₁
      exact h₁
    refine ⟨of_decide_eq_true hf, ?_, ?_, ?_⟩
    · intro z T hT hz
      have := key z T hT
      rw [if_neg (by omega)] at this
      exact eq_of_beq this
    · intro z T hT hz
      have := key z T hT
      rw [if_pos hz] at this
      exact of_decide_eq_true this
    · intro z T hT hz
      have := key z T hT
      rw [if_neg (by omega)] at this
      exact eq_of_beq this
  · intro h
    refine ⟨decide_eq_true h.few, List.all_eq_true.2 fun z _ => ?_⟩
    cases hT : B.trees[z]? with
    | none => rfl
    | some T =>
      show (if z + 1 = ft then decide (T.number < t₂) else T.number == z) = true
      by_cases hz : z + 1 = ft
      · rw [if_pos hz]
        exact decide_eq_true (h.taken z T hT hz)
      · rw [if_neg hz]
        by_cases hz' : z + 1 < ft
        · exact beq_iff_eq.2 (h.front z T hT hz')
        · exact beq_iff_eq.2 (h.own z T hT (by omega))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.bookFitsB_iff
#print axioms VerifiableInference.Desc.Sound.placedB_iff
#print axioms VerifiableInference.Desc.Sound.tenantB_iff
#print axioms VerifiableInference.Desc.Sound.numberedBookB_iff
#print axioms VerifiableInference.Desc.Sound.numberedLastB_iff

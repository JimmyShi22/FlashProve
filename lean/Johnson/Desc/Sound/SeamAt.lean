-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamAt.lean: TWO MESSAGES HAVE TWO SEATS; AND THE SEAM "A TREE's NUMBER = ITS
PLACE IN THE
BOOK". Definitions of Prop, and theorems with their proofs, on `seatBy`
(Johnson/Desc/Sound/TabAt.lean).

WHY. Two points on the term "words": (B3)
that `seatBy` is one-to-one on a statement's messages is said nowhere: two messages on one seat
share
one pad: then no honest witness meets both pins: emptiness · (B4) the term takes a tree's number
through the file from `Tree.number`, other files' tables take the tree's PLACE in the book. Typed:
`places_inj` (under `BookFits` two messages have two places) and `Numbered ft d` (a
tree's
number is ft + its place; kept by the receiving; broken by the adopting): Johnson/Desc/Book/.

  `seatBy_inv`. `NoInj no B`: no gives two trees of the book two numbers.
  **`seatBy_inj`**: `BookFits B`, `NoInj no B`: two messages with one seat are one. (B3)
  `NumberedBook ft B`: the book's half of `Numbered` (Book/BookNumbers.lean; `numberedBook_of`).
  `noInj_first`, `noInj_shared`. **`seatFirst_is`**: the seat is (ft + the tree's place, the part);
    **`seatFirst_place`**: at ft = 0 it IS the book's place. (B4) `number_at`: for a caller that
    reads
    the number with a default.
  `NumberedLast t₁ t₂ ft B`: four clauses on the last chain's book. `noInj_last`: so the natural
    subtraction in `noLast`'s third arm loses nothing.
  `seatFirst_inj`, `seatShared_inj`, `seatLast_inj`: at the three readings.

Limits. Book-keeping on plain data: nothing on soundness. THAT ANY CHAIN's BOOK IS `BookFits`,
`NumberedBook` OR `NumberedLast` IS SHOWN NOWHERE: the walks are
nobody's; `NumberedLast` is a reading of
"behind K14's second part the book is numbered up to Omega's tree and no further":
its
four clauses are held against no text. ft, t₁, t₂: letters. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TabAt
import Johnson.Desc.Book.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes
open VerifiableInference.Desc.Book (BookFits places_inj Numbered)

/-! ## 1 A seat, read back; one-to-one in general -/

theorem seatBy_inv (no : ℕ → Tree → ℕ) (B : TreeBook) (o : ℕ) (x : ℕ × ℕ)
    (h : seatBy no B o = some x) :
    ∃ q T, B.place[o]? = some q ∧ B.trees[q.1]? = some T ∧ x = (no q.1 T, q.2) := by
  unfold seatBy at h
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨q, T, hq, hT, rfl⟩

/-- no gives two trees of the book two numbers. -/
def NoInj (no : ℕ → Tree → ℕ) (B : TreeBook) : Prop :=
  ∀ z z' T T', B.trees[z]? = some T → B.trees[z']? = some T' → no z T = no z' T' → z = z'

/-- **TWO MESSAGES HAVE TWO SEATS**: under the book's invariant `BookFits`, where no gives two trees
two
numbers. -/
theorem seatBy_inj (no : ℕ → Tree → ℕ) (B : TreeBook) (hF : BookFits B) (hN : NoInj no B)
    (o o' : ℕ) (x : ℕ × ℕ) (h : seatBy no B o = some x) (h' : seatBy no B o' = some x) :
    o = o' := by
  obtain ⟨q, T, hq, hT, rfl⟩ := seatBy_inv no B o x h
  obtain ⟨q', T', hq', hT', e⟩ := seatBy_inv no B o' _ h'
  obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
  have e₃ : q = q' := Prod.ext (hN _ _ _ _ hT hT' e₁) e₂
  subst e₃
  exact places_inj hF hq hq'

/-! ## 2 A book whose trees are numbered by their places -/

/-- A tree's number is ft + its place in the book. -/
def NumberedBook (ft : ℕ) (B : TreeBook) : Prop :=
  ∀ (j : ℕ) (t : Tree), B.trees[j]? = some t → t.number = ft + j

/-- It is the book's half of `Numbered` (Johnson/Desc/Book/BookNumbers.lean). -/
theorem numberedBook_of {L : Type} (ft : ℕ) (d : _root_.Desc.Plain.DState L) (h : Numbered ft d) :
    NumberedBook ft d.book := fun j t ht => (h.2 j t ht).1

theorem noInj_first (ft : ℕ) (B : TreeBook) (hN : NumberedBook ft B) : NoInj noFirst B := by
  intro z z' T T' hT hT' e
  have e' : T.number = T'.number := e
  rw [hN z T hT, hN z' T' hT'] at e'
  omega

theorem noInj_shared (t₁ ft : ℕ) (B : TreeBook) (hN : NumberedBook ft B) :
    NoInj (noShared t₁) B := by
  intro z z' T T' hT hT' e
  have e' : t₁ + T.number = t₁ + T'.number := e
  rw [hN z T hT, hN z' T' hT'] at e'
  omega

/-- **THE SEAM "NUMBER = PLACE"**: at a numbered book that fits, the seat of a message through the
first
chain's reading is (ft + the place of its tree in the book, its part). -/
theorem seatFirst_is (ft : ℕ) (B : TreeBook) (hN : NumberedBook ft B) (hF : BookFits B) (o : ℕ)
    (q : ℕ × ℕ) (hq : B.place[o]? = some q) : seatBy noFirst B o = some (ft + q.1, q.2) := by
  obtain ⟨t, ht, _⟩ := hF o q hq
  rw [seatBy_some noFirst B o q t hq ht]
  show some (t.number, q.2) = _
  rw [hN q.1 t ht]

/-- At ft = 0 it is the book's own place. -/
theorem seatFirst_place (B : TreeBook) (hN : NumberedBook 0 B) (hF : BookFits B) (o : ℕ)
    (q : ℕ × ℕ) (hq : B.place[o]? = some q) : seatBy noFirst B o = some q := by
  rw [seatFirst_is 0 B hN hF o q hq, Nat.zero_add]

/-- For a caller that reads a tree's number with a default: at ft = 0 it is the place. -/
theorem number_at (B : TreeBook) (hN : NumberedBook 0 B) (z : ℕ) (hz : z < B.trees.size) :
    ((B.trees[z]?).map (·.number)).getD 0 = z := by
  rw [Array.getElem?_eq_getElem hz, Option.map_some, Option.getD_some,
    hN z _ (Array.getElem?_eq_getElem hz), Nat.zero_add]

/-! ## 3 The last chain's book -/

/-- The last chain's book: in front of place ft - 1 the first chain's trees, numbered by their
places,
at most t₁ of them; at it the one that is taken over, whose number is below t₂; behind it the
chain's
own, numbered by their places. -/
structure NumberedLast (t₁ t₂ ft : ℕ) (B : TreeBook) : Prop where
  few : ft ≤ t₁ + 1
  front : ∀ z T, B.trees[z]? = some T → z + 1 < ft → T.number = z
  taken : ∀ z T, B.trees[z]? = some T → z + 1 = ft → T.number < t₂
  own : ∀ z T, B.trees[z]? = some T → ft < z + 1 → T.number = z

theorem noInj_last (t₁ t₂ ft : ℕ) (B : TreeBook) (hN : NumberedLast t₁ t₂ ft B) :
    NoInj (noLast t₁ t₂ ft) B := by
  intro z z' T T' hT hT' e
  have hf := hN.few
  unfold noLast at e
  by_cases h₁ : z + 1 < ft
  · have a := hN.front z T hT h₁
    by_cases h₁' : z' + 1 < ft
    · have a' := hN.front z' T' hT' h₁'
      rw [if_pos h₁, if_pos h₁'] at e
      omega
    · by_cases h₂' : z' + 1 = ft
      · rw [if_pos h₁, if_neg h₁', if_pos h₂'] at e
        omega
      · rw [if_pos h₁, if_neg h₁', if_neg h₂'] at e
        omega
  · by_cases h₂ : z + 1 = ft
    · have a := hN.taken z T hT h₂
      by_cases h₁' : z' + 1 < ft
      · have a' := hN.front z' T' hT' h₁'
        rw [if_neg h₁, if_pos h₂, if_pos h₁'] at e
        omega
      · by_cases h₂' : z' + 1 = ft
        · omega
        · rw [if_neg h₁, if_pos h₂, if_neg h₁', if_neg h₂'] at e
          omega
    · have a := hN.own z T hT (by omega)
      by_cases h₁' : z' + 1 < ft
      · have a' := hN.front z' T' hT' h₁'
        rw [if_neg h₁, if_neg h₂, if_pos h₁'] at e
        omega
      · by_cases h₂' : z' + 1 = ft
        · have a' := hN.taken z' T' hT' h₂'
          rw [if_neg h₁, if_neg h₂, if_neg h₁', if_pos h₂'] at e
          omega
        · have a' := hN.own z' T' hT' (by omega)
          rw [if_neg h₁, if_neg h₂, if_neg h₁', if_neg h₂'] at e
          omega

/-! ## 4 At the three readings of the term "words" -/

theorem seatFirst_inj (ft : ℕ) (B : TreeBook) (hF : BookFits B) (hN : NumberedBook ft B)
    (o o' : ℕ) (x : ℕ × ℕ) (h : seatBy noFirst B o = some x) (h' : seatBy noFirst B o' = some x) :
    o = o' := seatBy_inj _ B hF (noInj_first ft B hN) o o' x h h'

theorem seatShared_inj (t₁ ft : ℕ) (B : TreeBook) (hF : BookFits B) (hN : NumberedBook ft B)
    (o o' : ℕ) (x : ℕ × ℕ) (h : seatBy (noShared t₁) B o = some x)
    (h' : seatBy (noShared t₁) B o' = some x) : o = o' :=
  seatBy_inj _ B hF (noInj_shared t₁ ft B hN) o o' x h h'

theorem seatLast_inj (t₁ t₂ ft : ℕ) (B : TreeBook) (hF : BookFits B)
    (hN : NumberedLast t₁ t₂ ft B) (o o' : ℕ) (x : ℕ × ℕ)
    (h : seatBy (noLast t₁ t₂ ft) B o = some x) (h' : seatBy (noLast t₁ t₂ ft) B o' = some x) :
    o = o' := seatBy_inj _ B hF (noInj_last t₁ t₂ ft B hN) o o' x h h'

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.number_at
#print axioms VerifiableInference.Desc.Sound.seatLast_inj
#print axioms VerifiableInference.Desc.Sound.seatBy_inj
#print axioms VerifiableInference.Desc.Sound.seatFirst_is
#print axioms VerifiableInference.Desc.Sound.seatFirst_place
#print axioms VerifiableInference.Desc.Sound.noInj_first
#print axioms VerifiableInference.Desc.Sound.noInj_shared
#print axioms VerifiableInference.Desc.Sound.noInj_last

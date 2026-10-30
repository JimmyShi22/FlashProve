-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/StartBook.lean: the last chain's first record holds the very book of trees
that the start is handed as the first chain's. Theorems.

Why. `start₃E_st` (Johnson/Desc/Third/Law/Start.lean) says it of the statement. `start₃_inv` and
`firstOutFrom_inv` (Johnson/Desc/Third/Law/AtDoor.lean) together say nothing of the book or of the
count of roots: the first gives the book of an inner record, the second does not say that this is
the book handed in. `BookSays` (Johnson/Desc/Third/Law/Book.lean) keeps every older place and tree
of the book of the record in front of K14's second part. Without the tie stated here that frame
does not reach the first chain's book.

Main names:
  `firstOutFrom_book`: the inner record holds the book and the count of roots that were handed in.
  `start₃E_book`: a yes of the start: the first record's book is the one handed in; it has received
    no root; the number of its first own tree is the count handed in and one.
  `book_carried`: behind the start's and K14's second part's yes, in a row, every place and every
    tree of the book handed in stands in the record's book as it was.

Limits. That the book handed in is the first chain's last is the caller's (`firstOfS`,
Johnson/Desc/Third/Border.lean: no law says that it reads the right field). Nothing on the new tree
beyond `BookSays`. Nothing on what a place or a tree means. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.AtDoor
import Johnson.Desc.Third.Law.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Later

namespace VerifiableInference.Desc.Third.Law

/-- The inner record holds the book and the count of roots that were handed in. -/
theorem firstOutFrom_book (S : Params.LinShape) (st : Statement) (book : TreeBook)
    (roots w own : Nat) (mask : Option Nat) (pile : List TensorRow) (f : FirstOut)
    (h : firstOutFrom S st book roots w own mask pile = some f) :
    f.book = book ∧ f.roots = roots := by
  unfold firstOutFrom at h
  split at h
  · try dsimp only at h
    repeat' (split at h)
    all_goals first
      | (cases h; exact ⟨rfl, rfl⟩)
      | (cases h)
  · cases h

/-- **The third chain begins at the very book that the start is handed as the first chain's.** -/
theorem start₃E_book (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.book = book₁ ∧ s₀.roots = 0 ∧ s₀.loc.firstTree = roots₁ + 1 := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨eb, er⟩ := firstOutFrom_book _ _ _ _ _ _ _ _ _ hf
  obtain ⟨_, _, e0⟩ := start₃_inv _ _ _ _ hst
  subst e0
  subst eb
  subst er
  exact ⟨rfl, rfl, rfl⟩

/-- **Behind K14's second part every place and tree of the book handed in is as it was.** -/
theorem book_carried {Cl : Type} (p : P₁₄) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut)
    (s₀ s₁ : S₃) (r₀ : List Fmt.RoundView) (g₀ : List (List (Nat × List UInt64)))
    (hs : start₃E p.codes p.S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h₀ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ r₀ g₀ = .ok s₁) :
    (∀ i : Nat, i < book₁.place.size → s₁.book.place[i]? = book₁.place[i]?) ∧
      ∀ i : Nat, i < book₁.trees.size → s₁.book.trees[i]? = book₁.trees[i]? := by
  obtain ⟨eb, _, _⟩ := start₃E_book _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, fp, ft⟩ := bookSays_k14Second p s₀ s₁ r₀ g₀ h₀
  rw [eb] at fp ft
  exact ⟨fp, ft⟩

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.firstOutFrom_book
#print axioms VerifiableInference.Desc.Third.Law.start₃E_book
#print axioms VerifiableInference.Desc.Third.Law.book_carried

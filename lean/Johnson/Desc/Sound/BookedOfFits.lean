-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BookedOfFits.lean: THE FENCE's TWO NAMED CLAUSES ON THE BOOKS, BROUGHT DOWN TO
THE
INVARIANT `BookFits` (Johnson/Desc/Book/BookFits.lean). Theorems with their proofs.

`AtStart` (Johnson/Desc/Sound/ReadsAt.lean), the closed Ok at which `Reads`
(Johnson/Desc/Third/Law/Row0Words.lean) is proved
of `wordsLast`, had two clauses that nobody paid: placed (every place of the first chain's last book
names a tree that is there) and tenant (in the shared chain's book Omega is part 0 of its tree).
`BookFits` is typed in Johnson/Desc/Book/BookFits.lean: every place of a book names a
tree that is there and a part of it that is the message; `placed_of_fits`; `tenant_of_fits`, where
the
tree has one part. That Omega's tree has one part IS A TEST OF THE BLOCK ITSELF (`takeOver`: "Omega:
it
has a tree to itself").

  `aloneOfTakeOver`, `aloneOfYes`: the taking-over's yes, and the block's: Omega's tree in the
  shared chain's book has one part. (`takeOver_inv`, Johnson/Desc/Third/Law/Keeps.lean, drops this
    test.)

  `tenantOfYes`: `BookFits o.book` and the block's yes: tenant.
  **`atStart_of_fits`**: the start's yes, the block's yes, `BookFits book₁`, `BookFits o.book`:
    `AtStart st₁ book₁ s.loc.w o s s'`.
  `frontOk_of_fits` is NOT typed: tenant needs the block's yes: so in a promise in front of the
  block
    stand `BookFits` of the two books, not `FrontOk`.

Limits. Nothing on soundness or on hiding. THAT ANY CHAIN's BOOK HAS `BookFits` IS SHOWN NOWHERE:
by report:
it is true of the empty book and kept by both routines of the plain ground that write the book; the
first chain's walk and the shared chain's (which copies a book back out of `verify-on-bytes`'s
routines) are nobody's. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsUsers
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes
open Desc.Plain (DState)
open VerifiableInference.Desc.Book (BookFits placed_of_fits tenant_of_fits)
open VerifiableInference.Desc.Third (S₃ SharedOut Border P₁₄ batchLinearConstraintsSecondPart start₃E takeOver Loc₃)
open VerifiableInference.Desc.Third.Law (k14Second_inv ok_of_bind some_of_named)

/-- The taking-over's yes: Omega's tree in the shared chain's book has one part. -/
theorem aloneOfTakeOver (S : Params.LinShape) (own : ℕ) (o : SharedOut) (d : DState Loc₃)
    (r : ℕ × DState Loc₃) (h : takeOver S own o d = .ok r) (q : ℕ × ℕ) (t : Tree)
    (hq : o.book.place[o.omega]? = some q) (ht : o.book.trees[q.1]? = some t) :
    t.parts.size = 1 := by
  unfold takeOver at h
  obtain ⟨q', hq', h⟩ := ok_of_bind h
  obtain ⟨t', ht', h⟩ := ok_of_bind h
  obtain ⟨_, hn, _⟩ := ok_of_bind h
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans (some_of_named hq'))
  obtain rfl : t = t' := Option.some.inj (ht.symm.trans (some_of_named ht'))
  unfold need at hn
  split at hn
  · rename_i hb
    exact eq_of_beq hb
  · cases hn

/-- The block's yes: the like, at the end that the border holds. -/
theorem aloneOfYes {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (g : List Tensor) (o : SharedOut) (hb : s.loc.border = some ⟨g, o⟩) (q : ℕ × ℕ) (t : Tree)
    (hq : o.book.place[o.omega]? = some q) (ht : o.book.trees[q.1]? = some t) :
    t.parts.size = 1 := by
  obtain ⟨x, a, _, _, hx, ha, _⟩ := k14Second_inv p s s' rs gs h
  obtain rfl : (⟨g, o⟩ : Border) = x := Option.some.inj (hb.symm.trans hx)
  exact aloneOfTakeOver _ _ _ _ _ ha q t hq ht

/-- **tenant**, from the invariant at the shared chain's book and the block's yes. -/
theorem tenantOfYes {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (g : List Tensor) (o : SharedOut) (hb : s.loc.border = some ⟨g, o⟩) (f₂ : BookFits o.book)
    (q : ℕ × ℕ) (hq : o.book.place[o.omega]? = some q) : q.2 = 0 := by
  obtain ⟨t, ht, _⟩ := f₂ _ q hq
  exact (tenant_of_fits f₂ hq ht (aloneOfYes p s s' rs gs h g o hb q t hq ht)).1

/-- **THE FENCE, FROM THE TWO YESES AND THE INVARIANT AT THE TWO BOOKS.** -/
theorem atStart_of_fits {Cl : Type} (p : P₁₄) (codes : Codes) (S : Params.LinShape)
    (st₁ : Statement) (book₁ : TreeBook) (roots₁ w₁ own₁ : ℕ) (mask₁ : Option ℕ)
    (pile₁ : List TensorRow) (o : SharedOut) (s s' : S₃)
    (h₀ : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (f₁ : BookFits book₁) (f₂ : BookFits o.book) : AtStart st₁ book₁ s.loc.w o s s' := by
  obtain ⟨g, hb⟩ := (startIs codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s h₀).2.2.1
  exact atStart_of_yes p codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s s' h₀ rs gs h
    (fun i q hq => placed_of_fits f₁ i q hq) (fun q hq => tenantOfYes p s s' rs gs h g o hb f₂ q hq)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.aloneOfTakeOver
#print axioms VerifiableInference.Desc.Sound.aloneOfYes
#print axioms VerifiableInference.Desc.Sound.tenantOfYes
#print axioms VerifiableInference.Desc.Sound.atStart_of_fits

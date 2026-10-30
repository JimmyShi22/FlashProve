-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/BookTreesA.lean: a helper of AtFullSide/K2/BookTrees.lean: behind the sending inside a
yes of the code switch the book is the book in front with new places and trees laid behind: every
older place and every older tree is as it was. One theorem with its proof; no definition.
-/
import Johnson.Top.H0.K2Hears.Whole
import Johnson.Top.H0.Tw.K2C.BookKept
import Johnson.Desc.Book.BookFitsGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes)

/-- **The sending inside a yes of the code switch leaves every older place and every older tree of
the book as it was**: from the book of the state at which the decision stands to the book of what
the sending returns. -/
theorem sending_keeps_at_yes {s₁ t : S} {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    (∀ j, j < s₁.book.place.size → z.book.place[j]? = s₁.book.place[j]?) ∧
      ∀ j, j < s₁.book.trees.size → z.book.trees[j]? = s₁.book.trees[j]? := by
  obtain ⟨ids, took, d', hs, rfl⟩ :=
    (VerifiableInference.Desc.First.K2.sendByL8_iff _ _ _ _ _ _ _ _ _).1 A.sentBy
  obtain ⟨_, _, sd, an, hx⟩ :=
    (VerifiableInference.Desc.First.K2.sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
  obtain ⟨d₁, h1, b, _⟩ := VerifiableInference.Desc.First.K2.sendP_book hx
  obtain ⟨_, lay, _, St⟩ := VerifiableInference.Desc.Book.recvP_seat _ _ _ _ _ h1
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · show d'.book.place[j]? = _
    rw [b]
    exact St.places j hj
  · show d'.book.trees[j]? = _
    rw [b]
    exact St.trees j hj

end AtFullSide.K2

#print axioms AtFullSide.K2.sending_keeps_at_yes

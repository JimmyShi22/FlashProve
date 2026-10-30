-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.BookWHand
import Johnson.Desc.K12.Seat.Own
/-
Johnson/Desc/K12/Law/BookWDoor.lean: «THE BOOK IS IN ORDER» (BookOrdW) BEHIND THE DOOR OF THE LAST CHAIN's OWN PROXIMITY TEST's SEAT: at the record that the kind's block itself reads. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  enterOwn_reads   the seat's door in (Seat.enterOwn, Johnson/Desc/K12/Seat/Own.lean): the record behind it has the chain's record's statement, book, roots, mask and own group
  door_W           the start's, K14's second part's and the sources' block's yeses in a row · every tree of the book handed in bears its place's number · the door's yes ⇒ BookOrdW roots₁ ω t.book ∧ t.book.trees.size = roots₁ + 1 ∧ t.roots = 0, ω the number of Omega's tree in the shared chain's book
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.First
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The last chain's seat's door in. -/
theorem enterOwn_reads (s : Third.S₃) (t : T12) (h : Seat.enterOwn s = .ok t) :
    t.st = s.st ∧ t.book = s.book ∧ t.roots = s.roots ∧ t.mask = s.loc.mask ∧ t.g = s.loc.own := by
  obtain rfl := Except.ok.inj h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem door_W {Cl : Type} (p : Third.P₁₄) (own : Block Third.S₃ Cl) (st₁ : Statement)
    (book₁ : TreeBook) (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow)
    (o : Third.SharedOut) (s₀ s₁ s₂ : Third.S₃) (r₀ r₁ : List Fmt.RoundView)
    (g₀ g₁ : List (List (Nat × List UInt64)))
    (hs : Third.start₃E p.codes p.S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h₀ : (Third.batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ r₀ g₀ = .ok s₁)
    (h₁ : (Third.takenSources own).decide s₁ r₁ g₁ = .ok s₂)
    (hB : ∀ (z : Nat) (T : Tree), book₁.trees[z]? = some T → T.number = z) (t : T12)
    (ht : Seat.enterOwn s₂ = .ok t) :
    ∃ (q : Nat × Nat) (tO : Tree), o.book.place[o.omega]? = some q ∧ o.book.trees[q.1]? = some tO ∧
      BookOrdW roots₁ tO.number t.book ∧ t.book.trees.size = roots₁ + 1 ∧ t.roots = 0 := by
  obtain ⟨q, tO, a1, a2, a3, a4, _, a6⟩ :=
    bookOrdW_door p own st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s₀ s₁ s₂ r₀ r₁ g₀ g₁ hs h₀ h₁
      hB
  obtain ⟨_, e2, e3, _, _⟩ := enterOwn_reads s₂ t ht
  rw [← e2] at a3 a4
  rw [← e3] at a6
  exact ⟨q, tO, a1, a2, a3, a4, a6⟩

end H2K.First

#print axioms H2K.First.enterOwn_reads
#print axioms H2K.First.door_W

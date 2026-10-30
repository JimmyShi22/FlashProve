-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyBookStep.lean: «THE BOOK IS IN ORDER» (BookStep: Johnson/Desc/Sound/BookOrder.lean; its iff to the Bool: BookInOrder.lean) ACROSS A SENDING, FROM WHAT Seated SAYS OF THE BOOK BEHIND (Johnson/Desc/Book/Seated.lean) AND THE NEW COUNT OF ROOTS (SendLaid.roots, Johnson/Desc/Key/Laid/SendLaid.lean). The sendings EARN the tables' Bool by this one lemma.
OBJECT: BookStep first B' roots' · USER: rows 1.0 | 1.1 | 1.17 (and 2.2 | 2.5) · LETTERS: all.
  bookStep_of_seated   PROVED. KIN: recvP_numbered (Johnson/Desc/Book/BookNumbers.lean): the same proof, said of recvP's yes and of Numbered (= BookStep AND the sources): the rows named above hold a bare Seated out of SendLaid.book, not a yes of recvP: hence this form · bookStep_recv | bookStep_received (BookInOrder.lean: off the ground's written book).
Nothing on soundness.
-/
import Johnson.Desc.Sound.BookInOrder
import Johnson.Desc.Book.Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes
open VerifiableInference.Desc.Sound (BookStep)
open VerifiableInference.Desc.Book (Seated)

theorem bookStep_of_seated (first : Nat) (B B' : TreeBook) (n n0 : Nat) (lay : TreeLay) (src : Nat → Fmt.Src) (roots roots' : Nat)
    (h : BookStep first B roots) (S : Seated B B' n n0 lay (fun τ => first + (roots + τ)) src) (hr : roots' = roots + lay.shapes.size) :
    BookStep first B' roots' := by
  obtain ⟨e, ho⟩ := h
  refine ⟨by rw [hr, S.size, e], fun z T hT => ?_⟩
  have hz : z < B.trees.size + lay.shapes.size := by
    rw [← S.size]
    exact (Array.getElem?_eq_some_iff.1 hT).1
  by_cases hlt : z < B.trees.size
  · rw [S.trees z hlt] at hT
    exact ho z T hT
  · obtain ⟨τ, rfl⟩ : ∃ τ, z = B.trees.size + τ := ⟨z - B.trees.size, by omega⟩
    obtain ⟨t, ht, -, hn, -⟩ := S.made τ (by omega)
    rw [ht] at hT
    cases hT
    rw [hn, e]

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.bookStep_of_seated

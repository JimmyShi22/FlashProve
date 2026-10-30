-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/BookThere.lean: «THE BOOK BEHIND THE CODE SWITCH's SENDING IS THERE»
(`K2.bookAt … = some B`: the first of the four facts on the front that `hF_of_door` asks: hFr,
HFOfDoor.lean) FROM THE RECEIVING's OWN CLAUSES: the sent shapes fit the codes · the trees can be
laid · statement and book are in step. By `recvP_iff`
(Johnson/Desc/K1/Law/Writes3.lean). A theorem. No text already in the library turns.

  `bookAt_of`: **the receiving's clauses say yes at the statement S, the book Bk and the notices n ·
    the trees' layout is there ⊢ ∃ B, K2.bookAt ft S Bk roots n = some B.**
Limits. The two premises are on the front's statement, the state's book and the switch's notices
(public numbers of the plan): not paid here. Nothing on soundness.
-/
import Johnson.Top.H0.K2Hears.LongOne
import Johnson.Desc.K1.Law.Writes3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model Desc.Plain

theorem bookAt_of (ft : ℕ) (S : Statement) (Bk : TreeBook) (roots : ℕ)
    (n : Array OracleNotice) (h1 : Ground.ok (Ground.recvL S Bk n) = true)
    (h2 : ∃ lay, layTrees S.codes n = some lay) :
    ∃ B, First.K2.bookAt ft S Bk roots n = some B := by
  obtain ⟨lay, hl⟩ := h2
  have h := (K1.recvP_iff ft (⟨S, Bk, roots, [], ()⟩ : DState Unit) _ n _).2
    ⟨h1, lay, hl, rfl, rfl⟩
  unfold First.K2.bookAt
  rw [h]
  exact ⟨_, rfl⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.bookAt_of

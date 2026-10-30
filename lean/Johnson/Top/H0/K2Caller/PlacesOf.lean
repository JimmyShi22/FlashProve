-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PlacesOf.lean: the code switch: «THE BOOK HAS A PLACE FOR EVERY
MESSAGE OF THE STATEMENT» STANDS IN THE TABLE OF JOINTS' PROMISE ITSELF (by report:
the second clause of Johnson/Desc/First/Borders.lean's bookAt).
  places_of_promise  at a verifier's state without a mark inside the promise at a border: the book
               has as many places as the statement has oracle messages
  hold_of_promise    so a message that the statement has is below the book's places: the hypothesis
               hold of KeptSeatOf.lean's keptSeat_of_fold, at the border's state
LIMITS. At the state at the border: where the way in of the seated sub-protocol is not the identity
one step lies between. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.TiesFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)

variable {A P W : Type} {F : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (get : A → P × First.S) (k : ℕ)

theorem places_of_promise (a : A × F.E.Str) (ha : onQ N Mg links ps get k a)
    (hm : ¬ (get a.1).2.failed ≠ none) :
    (get a.1).2.book.place.size = (get a.1).2.st.oracles.size := by
  obtain ⟨-, h⟩ := ha
  rcases h with h | ⟨hb, -⟩
  · exact absurd h hm
  · simp only [Bool.and_eq_true] at hb
    have hh := hb.2
    unfold VerifiableInference.Desc.First.bookAt at hh
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1.2

theorem hold_of_promise (a : A × F.E.Str) (ha : onQ N Mg links ps get k a)
    (hm : ¬ (get a.1).2.failed ≠ none) (old : ℕ) (xo : OnBytes.Oracle)
    (hx : (get a.1).2.st.oracles[old]? = some xo) : old < (get a.1).2.book.place.size := by
  rw [places_of_promise N Mg links ps get k a ha hm]
  exact (Array.getElem?_eq_some_iff.1 hx).1

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hold_of_promise

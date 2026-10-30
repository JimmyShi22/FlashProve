-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05SeatKeepsPin.lean: kind K5: the hearing's seat keeps what a pin by a
decoder with a sample reads of the carried record: the statement's oracle messages and the book of
trees.

Main names:
  `readsRest_pair`, `readsRest_comp`: two readings with ReadsRest (Att/K05SeatKeeps.lean) side by
    side are one; so is whatever is read off one.
  `rest_oracles_book`: **ReadsRest fun s => (s.st.oracles, s.book)**.
  `seatSO_keeps_oracles_book`: so where seatSO.lay returns s' at s: (s'.st.oracles, s'.book) =
    (s.st.oracles, s.book): the field "lay" of a PinItemP (Att/K05PinP.lean) at rc := that reading.
Why it holds: seatSO.lay turns three places of the record alone: rowsOwed, and in an open attention
segment its ledger F and heard5 (seatSO_rest): neither st nor book.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05SeatKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

theorem readsRest_pair {A B : Type} {f : First.S → A} {g : First.S → B} (hf : ReadsRest f)
    (hg : ReadsRest g) : ReadsRest fun s => (f s, g s) :=
  fun s t e => by
    show (f s, g s) = (f t, g t)
    rw [hf s t e, hg s t e]

theorem readsRest_comp {A B : Type} {f : First.S → A} (hf : ReadsRest f) (k : A → B) :
    ReadsRest fun s => k (f s) :=
  fun s t e => congrArg k (hf s t e)

/-- **The statement's oracle messages and the book.** -/
theorem rest_oracles_book : ReadsRest fun s : First.S => (s.st.oracles, s.book) :=
  readsRest_pair (readsRest_comp rest_st (·.oracles)) rest_book

/-- The field "lay" of an item that reads these two. -/
theorem seatSO_keeps_oracles_book (s : First.S) (h : Heard) (G : Fork) (s' : First.S)
    (hl : seatSO.lay s h G = some s') : (s'.st.oracles, s'.book) = (s.st.oracles, s.book) :=
  seatSO_keeps _ rest_oracles_book s h G s' hl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.readsRest_pair
#print axioms VerifiableInference.Desc.First.Att.P.readsRest_comp
#print axioms VerifiableInference.Desc.First.Att.P.rest_oracles_book
#print axioms VerifiableInference.Desc.First.Att.P.seatSO_keeps_oracles_book

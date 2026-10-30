-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SmpPlaces.lean: A TEST ON A RECORD's STATEMENT AND BOOK: THE BOOK PLACES MESSAGE
NUMBER k AT THE PLAN's k-TH SEAT. A definition alone; nothing is proved here.

Why. The named reader of samples (`smpNamed`, Johnson/Desc/Sound/SmpNamed.lean) finds a member's
message by a FIXED number: the place of the member's seat in the plan's list of seats. The table's
field "held" (`smpHeld`, Johnson/Desc/SmpRows.lean) finds it through THE RECORD's BOOK (`oracleNo`:
the first number whose place is that seat). The two are one number just where the book follows the
plan.
  `placesAre seats st book`: a Bool: the book has no more places than the plan has seats; the
    statement has as many messages as the book has places; and for every k below the book's places:
    book.place[k] is seats[k].
Limits. A definition. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- The record's book follows the plan's list of seats. -/
def placesAre (seats : List (Nat × Nat)) (st : OnBytes.Statement) (book : OnBytes.TreeBook) :
    Bool :=
  decide (book.place.size ≤ seats.length) && st.oracles.size == book.place.size &&
    (List.range book.place.size).all fun k => book.place[k]? == seats[k]?

end VerifiableInference.Desc

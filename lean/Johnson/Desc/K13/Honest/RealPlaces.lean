--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/RealPlaces.lean: where the message length of W's code is a power of two,
every place of W's table is a place of W's message. Statements with their proofs.

A row of W's table has 2^placeBits places, placeBits being the least a with ell ≤ 2^a for the code's
message length ell. Where ell is no power of two, the places from ell on are no entries of the
message, and the test on the shape counts them as room (Johnson/Desc/Own/RoomPlaces.lean says so of
`roomOf`). So "W's table holds the vector" says that the committed message holds it only where ell
is a power of two. That is a test on the codes; for W's code it is also asked by the test on the
stages of the own group's proximity test.
Main names:
  `table_places`: where the message length of W's code is a power of two: every index of W's table
    has a place's number below the message length. So the table has no place from the message length
    on, at which a sender would owe the value 0.
  `shape_places`: where moreover the test on the shape passes: so has each of the first 2^kCol
    entries; stated apart, by `room_places` (Johnson/Desc/Own/RoomPlaces.lean). With `shape_rows`
    (Johnson/Desc/K13/Honest/FromShape.lean): at a real place of a real row.

What is not claimed. That the tests pass at any codes and shape. Anything where the message length
is no power of two. Nothing on W's encoding. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.FromShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Own (linFits)

/-- A row of W's table has as many places as the message has entries. -/
theorem places_eq {codes : Codes} {Sh : LinShape}
    (hp : powerOfTwo (codes.base.getD Sh.w.code default).ell = true) :
    2 ^ (vectorLay codes Sh.w Sh.wRowsHigh).placeBits =
      (codes.base.getD Sh.w.code default).ell := by
  simp only [powerOfTwo, Bool.and_eq_true, beq_iff_eq] at hp
  exact hp.2

/-- **Every index of W's table has a place's number below the message length.** -/
theorem table_places {codes : Codes} {Sh : LinShape}
    (hp : powerOfTwo (codes.base.getD Sh.w.code default).ell = true) :
    ∀ idx < 2 ^ (linLayW codes Sh).bits,
      idx / 2 ^ (linLayW codes Sh).rowBits < (codes.base.getD Sh.w.code default).ell := by
  intro idx hi
  have hb : 2 ^ (linLayW codes Sh).bits =
      2 ^ (linLayW codes Sh).rowBits * 2 ^ (vectorLay codes Sh.w Sh.wRowsHigh).placeBits :=
    Nat.pow_add _ _ _
  rw [hb, places_eq hp] at hi
  exact Nat.div_lt_of_lt_mul hi

/-- **Each of the first 2^kCol entries lies at a real place of its row.** -/
theorem shape_places {codes : Codes} {Sh : LinShape} (h : linFits codes Sh = true)
    (hp : powerOfTwo (codes.base.getD Sh.w.code default).ell = true) :
    ∀ e < 2 ^ Sh.kCol,
      (linLayW codes Sh).index e / 2 ^ (linLayW codes Sh).rowBits <
        (codes.base.getD Sh.w.code default).ell := by
  obtain ⟨_, _, _, _, _, _, _, hr⟩ := (VerifiableInference.Desc.Own.linFits_iff codes Sh).1 h
  exact fun e he => VerifiableInference.Desc.Own.room_places codes Sh.w Sh.wRowsHigh (2 ^ Sh.kCol)
    Nat.one_le_two_pow hr e he (places_eq hp)

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.places_eq
#print axioms VerifiableInference.Desc.K13.Honest.table_places
#print axioms VerifiableInference.Desc.K13.Honest.shape_places

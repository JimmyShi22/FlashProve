-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SeatsRideK1.lean: "THE SEATS ARE CARRIED" (`K12.Coin.SeatsPrefix`,
Johnson/Desc/K12/Coin/BookRides.lean) RIDES THROUGH A SENDING OF KIND K1, where the
plan's lists go on with what the place lays. One term: that file's `seatsPrefix_append` at our two
appendings (`SeatedBy.places`, `SeatedBy.shapes`, Johnson/Desc/K1/Law/SeatedAppends.lean); and its
calls at the kind's three blocks at the first chain's record. It proves nothing of its own.
  `SeatedBy.seatsRide`: the term. `sendAtS_seats`, `commitAtS_seats`, `firstAtS_seats`: the blocks.
What is not claimed. That the plan's lists go on so at a block's place. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.SeatedAppends
import Johnson.Desc.K12.Coin.BookRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Coin (SeatsPrefix seatsPrefix_append)

variable {Cl : Type}

/-- **The term.** -/
theorem SeatedBy.seatsRide {P : Par} {bk bk' : TreeBook} {n r n' r' : Nat} {L : K12.Coin.Laid}
    (h : SeatedBy P bk n r bk' n' r') (h0 : SeatsPrefix L bk)
    (hp : (L.places.drop bk.place.size).take P.sent.size =
      K12.Coin.placesOf bk.trees.size P.sent.size (layOf P))
    (hs : (L.shapes.drop bk.trees.size).take (layOf P).shapes.size = (layOf P).shapes.toList) :
    SeatsPrefix L bk' :=
  seatsPrefix_append L bk bk' (K12.Coin.placesOf bk.trees.size P.sent.size (layOf P))
    (layOf P).shapes.toList h0 h.places h.shapes (by simpa [K12.Coin.placesOf] using hp)
    (by rw [Array.length_toList]; exact hs)

theorem sendAtS_seats (P : Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') {L : K12.Coin.Laid}
    (h0 : SeatsPrefix L s.book)
    (hp : (L.places.drop s.book.place.size).take P.sent.size =
      K12.Coin.placesOf s.book.trees.size P.sent.size (layOf P))
    (hs : (L.shapes.drop s.book.trees.size).take (layOf P).shapes.size =
      (layOf P).shapes.toList) : SeatsPrefix L s'.book :=
  (sendAtS_seated P s s' r₁ r₂ gs h).seatsRide h0 hp hs

theorem commitAtS_seats (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s')
    {L : K12.Coin.Laid} (h0 : SeatsPrefix L s.book)
    (hp : (L.places.drop s.book.place.size).take P.sent.size =
      K12.Coin.placesOf s.book.trees.size P.sent.size (layOf P))
    (hs : (L.shapes.drop s.book.trees.size).take (layOf P).shapes.size =
      (layOf P).shapes.toList) : SeatsPrefix L s'.book :=
  (commitAtS_seated P link moment arrays s s' r₁ r₂ gs h).seatsRide h0 hp hs

theorem firstAtS_seats (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') {L : K12.Coin.Laid}
    (h0 : SeatsPrefix L s.book)
    (hp : (L.places.drop s.book.place.size).take (firstPar q gp).sent.size =
      K12.Coin.placesOf s.book.trees.size (firstPar q gp).sent.size (layOf (firstPar q gp)))
    (hs : (L.shapes.drop s.book.trees.size).take (layOf (firstPar q gp)).shapes.size =
      (layOf (firstPar q gp)).shapes.toList) : SeatsPrefix L s'.book :=
  (firstAtS_seated q gp s s' r₁ r₂ gs h).seatsRide h0 hp hs

end VerifiableInference.Desc.K1

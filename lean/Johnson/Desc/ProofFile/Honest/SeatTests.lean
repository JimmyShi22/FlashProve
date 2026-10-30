-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SeatTests.lean: TWO SMALL THINGS FOR WHOEVER SEATS PARTS, of public
data alone. Definitions with code, and tests at made-up lists; no theorem.

  1  `readsInFront`   A TEST AT THE SEAT: the challenges that a part reads by their numbers
     (`heardFrom`, Honest/ForKinds.lean) have all been heard when the part begins
  2  `quietCuts`, `ProverCoinCounts.withQuiet`   THE EMPTY CUTS: for members without a round at which an empty
     row stands

Why the first. `heardFrom t i n` yields fewer than n challenges, without a word, where fewer have
been heard. A MOVE SHOULD NOT REFUSE THERE (so `heardJust` is for toys, prints and test programs,
AGAINST THE ADVICE IN ITS OWN DOCSTRING): `Good.exact` (Honest/Side.lean) is asked at every stand,
one with a short list of heard challenges among them, and a part that is at fault there shows
nothing while its simulator yields something. So a part's functions stay total, and the guard stands
at the seat: the numbers are public data, and so is the number of rounds in front of a place.

Why the second. A member without a round can have a side: an empty row (`Side.seated bs place []
fs`): `Good`'s `plays` and `acc` then speak of its step alone, and a fall has its seat. `chainSteps`
(Honest/Frame.lean) asks the book for a cut wherever a half stands; the maker's `cutsIn`
(Honest/BookOf.lean) lists the members that have a round.

Limits. `readsInFront` counts in one chain's list; `base` is for the second chain, where what is
heard begins with the first chain's and the shared chain's challenges. It holds no number against
what the part means by it: a wrong number in front of the place passes. This file proves nothing
about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.BookOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type}

/-! ## 1 The numbers that a part reads -/

/-- **The n challenges from number i on have been heard when the part begins.** bs: the chain's own
list. a: the part's place. inRow: the rounds of the parts in front of it in its row. base: how many
challenges have been heard when the chain begins. `false` where no member stands at a. -/
def readsInFront (bs : List (Block S Cl)) (a : Place) (i n : Nat) (inRow : Nat := 0)
    (base : Nat := 0) : Bool :=
  match roundsInFront bs a with
  | some r => decide (i + n ≤ base + r + inRow)
  | none => false

/-! ## 2 The empty cuts -/

/-- **The empty cut at each of the named places at which a member without a round stands.** -/
def quietCuts (bs : List (Block S Cl)) (places : List Place) : List (Place × List Nat) :=
  (bs.filter fun b => b.rounds.isEmpty && places.contains b.place).map fun b => (b.place, [])

/-- A book with cuts more. -/
def ProverCoinCounts.withQuiet (B : ProverCoinCounts) (l : List (Place × List Nat)) : ProverCoinCounts := { B with cuts := B.cuts ++ l }

/-! ### Tests at made-up lists -/

/-- A sub-protocol with n rounds. -/
def seatToy (piece n : Nat) : Block Unit Unit :=
  { name := "toy", place := ⟨1, none, piece, .frame⟩, planOk := true
    rounds := List.replicate n { entry := { name := "BAT-sigma" } }
    oracles := List.replicate n [], before := [], decide := fun s _ _ => .ok s
    claims := [], after := [] }

/-- Two rounds; none; three. -/
def seatList : List (Block Unit Unit) := [seatToy 0 2, seatToy 1 0, seatToy 2 3]

def seatAt (piece : Nat) : Place := ⟨1, none, piece, .frame⟩

-- two rounds stand in front of the third member: the numbers 0 and 1 have been heard; 2 has not
#guard readsInFront seatList (seatAt 2) 0 2 && readsInFront seatList (seatAt 2) 1 1
#guard !readsInFront seatList (seatAt 2) 2 1 && !readsInFront seatList (seatAt 2) 1 2
-- behind one round of its own row it has; with four heard when the chain begins too
#guard readsInFront seatList (seatAt 2) 2 1 (inRow := 1) &&
  readsInFront seatList (seatAt 2) 5 1 (base := 4)
-- at no member's place: no
#guard !readsInFront seatList (seatAt 9) 0 0
-- the empty cut: at the member without a round alone, and only if it is named
#guard quietCuts seatList [seatAt 1, seatAt 2] == [(seatAt 1, [])]
#guard quietCuts seatList [] == []
-- beside the maker's cuts: every member has one
#guard ((cutsIn seatList ++ quietCuts seatList (seatList.map (·.place))).map (·.1)).length == 3

end ProofFile.Honest

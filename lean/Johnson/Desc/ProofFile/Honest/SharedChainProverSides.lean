-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SharedChainProverSides.lean: THE SHARED CHAIN's HALVES THAT ARE WRITTEN HERE, AT
THE PROOF FILE's OWN PUBLIC PART: the kind K14's quiet rounds and its round "SPLIT", and the two
sendings of the folded row and of Omega. THEY STAND APART FROM Honest/AtPureSixKinds.lean, so that a
file on the shared chain alone need not import the first chain's kinds' halves:
Honest/AtPureSixKinds.lean imports this file. Definitions with code; no theorem.

  `IndexCommitterCoins`          the index committer's coins: a `TableRand` for each item of the statement
  `p14At`          the shared chain's own parameters: by the call by which the library's own seat of
                  that chain makes them (`Desc.K14.sharedSeatAt`,
                  Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean)
  `sharedInFront`  how many rounds of the shared chain stand in front of a place: `roundsInFront` at
                  that seat's own flat list: for the numbers of "LIN point" and "LIN zeta"
  `nowShared`      the shared chain's halves, or a word on what could not be made
  `nowWord`        that word at a public part

Limits. As Honest/AtPureSixKinds.lean's on these names: the kind K14's own structure of the index
committer's coins has the frame's two fields and is laid of those of the item that the shared
chain's own parameters name (`P14.item`). Nothing here says that a half's counts and names are the
book's. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.ProofFile.Lot.K14SeatAtZ
import Johnson.Desc.ProofFile.OnlineDescriptionBlocks
import Johnson.Desc.K12.Plan.PlaceOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-- The index committer's coins: for each item of the statement. -/
abbrev IndexCommitterCoins : Type := Nat → TableRand

/-- **The shared chain's own parameters.** -/
def p14At (Z : Pub) : Option Desc.K14.P14 :=
  match H2U.placesOfMade Z.made with
  | .ok N => some (Desc.K14.p14Of Z.p.chains (Desc.K14.beforePointOf N))
  | .error _ => none

/-- **How many rounds of the shared chain stand in front of a place.** -/
def sharedInFront (Z : Pub) (a : Place) : Option Nat :=
  (onlineSharedChain Z).bind fun s => roundsInFront s.chain.blocksInOrder a

/-- **The shared chain's halves**, or a word on what could not be made. -/
def nowShared (Z : Pub) :
    Except String (List (Placed Empty (Common Weights IndexCommitterCoins OnBytes.TableKey) Unit)) :=
  (due? "the shared chain's own parameters" (p14At Z)).bind fun P =>
  (due? "the round \"LIN point\" in the shared chain" (sharedInFront Z (K14.place 1))).bind fun a =>
  (due? "the round \"LIN zeta\" in the shared chain" (sharedInFront Z (K14.place 7))).bind fun z =>
    .ok (K14.proverSidesOfSharedRounds ⟨P.S, a, z⟩ id ++
      K14.proverSidesOfSharedSendings ⟨P, a⟩ id fun rc => ⟨(rc P.item).pad, (rc P.item).tail⟩)

/-- The word of `nowShared`. -/
def nowWord (Z : Pub) : Option String :=
  match nowShared Z with
  | .ok _ => none
  | .error e => some e

end ProofFile.Honest

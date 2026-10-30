-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureSixKinds.lean: A FILLING OF THE HONEST PROVER (`OnlineProverParts`,
Honest/AtPure.lean) WITH THESE OF THE KINDS' HALVES LAID IN: the next
token (K7) · the merge of the claims on the weights (K11) · the members' batching (K13) · the
lookups (K3) · the attention segments' own rounds (K5) · the output head's own rounds (K6) · in the
shared chain the kind K14's quiet rounds and its round "SPLIT", and the two sendings of the folded
row and of Omega. Definitions with code; no theorem.

THE TYPES. The index is its reader and the trace is its reader: W₀ := `Weights`, Tr := `Cells`; each
half takes its readers (of the trace, and of the index where it reads it) as parameters: the
identity here. So the filling types at every size.
The index committer's coins: a `TableRand` for each item of the statement.

WHAT IS FILLED BY THE LIBRARY's AND THE FRAME's OWN FUNCTIONS (these two, `IndexCommitterCoins`, `nowShared` and
`nowWord` stand in Honest/SharedChainProverSides.lean, which this file imports).
  `p14At`          the shared chain's own parameters: by the call by which the library's own seat of
                  that chain makes them (`Desc.K14.sharedSeatAt`,
                  Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean)
  `sharedInFront`  how many rounds of the shared chain stand in front of a place: `roundsInFront` at
                  that seat's own flat list: for the numbers of "LIN point" and "LIN zeta"

WHAT IS NOT, BY NAME: `OnlineProverArguments`'s fields.
  `claims`   K11's: how the claims on the weights are made of the instance and the challenges in
             front
  `pile`     K13's: the rows on the pile: each row's weights and column point
  `req`      K3's: the covered positions and the token that is checked at each, of the instance
  `keyOf`    K5's: the key points' reader at a segment
  `cells`    the witness's cells, of the index and the instance
  `enc`      the encoded index's columns
The index and the index committer's coins are the run's arguments.

  `nowShared`   the shared chain's halves, or a word on what could not be made
  `nowFill`     the filling
  `nowWord`     the word of `nowShared` at a public part: `OnlineProverParts.shared` cannot reject, so WHERE THE
               SHARED CHAIN's PARAMETERS CANNOT BE MADE `nowFill` LAYS NO HALF THERE: a caller asks
               `nowWord` first

Limits. Which halves are laid is a written list. The output head's lot lays its half only where its
own public test on the numbers says yes (`K6.headFitsB`, Honest/K6/Wit.lean); where it says no, no
half stands at that place. `claims` and `pile` are typed as functions of the public part, the
ground, the instance and the challenges alone: no text here fills them (`openHonest`,
Honest/OpenHonest.lean, does). The kind K14's own structure of the
index committer's coins has the frame's two fields and is laid of those of the item that the shared
chain's own parameters name (`P14.item`: the statement's item that holds the index's root:
Johnson/Desc/K14/Blocks.lean). `nowShared` asks none of the three public tests of `K14.sixOf`
(Honest/K14/Six.lean). Nothing here says that a half's counts and names are the book's: the
player's tests do, at a run. This file proves nothing about soundness, completeness, hiding or any
other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPure
import Johnson.Desc.ProofFile.Honest.K7
import Johnson.Desc.ProofFile.Honest.K11.Part
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.SharedChainProverSides
import Johnson.Desc.ProofFile.Honest.K3.LotFilled
import Johnson.Desc.ProofFile.Honest.K5.KeysFit
import Johnson.Desc.ProofFile.Honest.K6.Part
import Johnson.Desc.ProofFile.Honest.K6.Wit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-- **What the filling takes as an argument.** -/
structure OnlineProverArguments where
  /-- K11's: the claims on the weights, of the public part, the ground, the instance and the
  challenges in front of the place -/
  claims : Pub → Ground → Inst → List Fmt.Drawn → List OnBytes.Model.WsClaim
  /-- K13's: the rows on the pile, of the public part, the ground, the instance and the challenges
  in front of the part -/
  pile : Pub → Ground → K13.PileOf Inst
  /-- K3's: of the instance, the covered positions and the token that is checked at each -/
  req : Inst → OnBytes.Model.Head.Covered × Array Nat
  /-- K5's: the key points' reader at a segment, of the challenges in front -/
  keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)
  /-- the witness's cells; `none` where the request has no trace -/
  cells : Pub → Weights → Inst → Option Cells
  /-- the encoded index's column: by the statement's item and the position -/
  enc : Pub → Weights → IndexCommitterCoins → Nat → Nat → Option (List Cb.Gl.F)

/-- **The filling.** FIVE SILENT DEFAULTS. `rows` is `RowData.empty`: no message has data of its
main rows. `inRange` is true of every index: the run's test on the range never refuses one. `dummy`
is the matrix that is 0 everywhere. `shared` is the empty list where `nowShared Z` returns an
error: whoever speaks of the shared chain's sides names `nowShared Z = .ok l`, a premise on the
public part alone (`nowFill_shared_ok`, `nowFill_shared_error`, Honest/AtPureSharedOk.lean).
`second` is the empty list always, though by reading the second chain has a
sub-protocol that sends (its proximity test): so a sender is then without a side here, and no
sentence on an honest prover reaches that chain. -/
def nowFill (O : OnlineProverArguments) : OnlineProverParts Weights IndexCommitterCoins Cells Unit Unit :=
  { trace := O.cells
    readers := fun _ w rc T => ⟨T, w, rc⟩
    rows := fun _ _ _ => RowData.empty
    inRange := fun _ => true, dummy := ⟨fun _ _ => OnBytes.Slice.toF 0⟩, enc := O.enc
    own₀ := (), ownShared₀ := (), meet := fun x _ => x
    lots := [replyLot, K11.headMergeLot O.claims id, K13.k13Lot id O.pile,
      K3.theLot id id O.req, K5.k5LotK id O.keyOf, K6.headLot K6.headFitsB (K6.headWit' id id)]
    shared := fun Z _ => (nowShared Z).toOption.getD []
    second := fun _ _ => [] }

end ProofFile.Honest

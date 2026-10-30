-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/InFrontStatement.lean: THE ROUNDS IN FRONT OF A PLACE ARE THOSE OF
THE SUB-PROTOCOLS IN FRONT OF IT; AND AT WHICH NUMBERS TWO PLACES OF THE OUTPUT HEAD's LINK STAND AT
THE FULL SIZE: STATEMENTS ALONE: three definitions of propositions. NOTHING IS PROVED IN THIS FILE,
and none is one of the library's goals: they are lemmas' statements.

  `RoundsInFrontIs`     at every list of blocks: where the place a stands first at number j of the
                        list of places, the frame's `roundsInFront` (Honest/ForKinds.lean) at a is
                        the count of rounds of the first j blocks (`roundsAhead`,
                        Johnson/Desc/K13/Honest/FoldCut.lean)
  `CallsPlaceAtFull`    in the written list of places of the full size (`P5J.At.ps`), piece 3 (the
                        kind K3: the lookup on the calls) of link 24 stands first at number 340
  `HeadOwnPlaceAtFull`  there, piece 4 (the kind K6: the head's own sub-protocol) of link 24 stands
                        first at number 341

Why. A text that finds a count of rounds by place, and an elder text that is written at a member's
number, are joined by these three. The file is light: over the frame's ForKinds.lean, FoldCut.lean
and the library.

Limits. THE FIRST IS GENERAL IN THE LIST AND ASKS THAT THE PLACE STANDS IN IT, FIRST AT NUMBER j.
THE OTHER TWO ARE CLOSED FACTS ON THE WRITTEN LIST OF THE FULL SIZE: THAT A CHAIN's PLACES ARE THAT
LIST IS NOT SAID HERE (under the library's head: `P5J.At.places_paid`). NEAR THE FIRST: the frame's
authors' `roundsTo_inFront` (Honest/Thread/HeardLaw.lean, a file that is not in this library): where
`roundsInFront` returns a number, it is their `roundsTo` at their `borderNo`: it does not say that
`roundsInFront` returns. NEAR THE SECOND: the library's `IM.head_two_there`
(Johnson/IMR/SortHead.lean): number 340 of a written list has that kind, piece and link: not that it
is the first such. NEAR THE THIRD: the library's `place_341` (Johnson/P4R/Head342.lean): number 341
of the driver's list of places at the full chain is that place: not that it is the first such.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.K13.Honest.FoldCut
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K13.Honest (roundsAhead)

/-- The statement on the two counts of rounds. Not proved here; a lemma's statement, none of the
library's goals. -/
def RoundsInFrontIs : Prop :=
  ∀ (S Cl : Type) (bs : List (Block S Cl)) (a : Place) (j : ℕ),
    (bs.map (·.place)).idxOf a = j → j < bs.length →
    roundsInFront bs a = some (roundsAhead bs j)

/-- The statement on the place of the lookup on the head's calls. Not proved here; a lemma's
statement, none of the library's goals. -/
def CallsPlaceAtFull : Prop := P5J.At.ps.idxOf ⟨1, some 24, 3, .K3⟩ = 340

/-- The statement on the place of the head's own sub-protocol. Not proved here; a lemma's statement,
none of the library's goals. -/
def HeadOwnPlaceAtFull : Prop := P5J.At.ps.idxOf ⟨1, some 24, 4, .K6⟩ = 341

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.RoundsInFrontIs
#print axioms ProofFile.Honest.K11.CallsPlaceAtFull
#print axioms ProofFile.Honest.K11.HeadOwnPlaceAtFull

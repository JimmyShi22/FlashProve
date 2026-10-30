-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Half.lean: the honest side of the kind "the closing of a segment"
(K10), in the form of Honest/Frame.lean: its place, its cut, the names and counts of the runs of
coins that it is handed, and its half. The kind's own text says: "SENDS. Not yet written"
(Johnson/Desc/First/Close/Closing.lean). This file defines part of the honest prover. Definitions
with code; no theorem.

The rounds (Johnson/Desc/First/Close/Kind.lean, `entries`): "BAT", in which nothing is sent;
"FOLD epsilon", in which one element is sent; k times "FOLD round", in which two are sent. No table
is sent: at a closing the fold's fresh mask came with the segment's first message.

The cut. By Honest/BookOf.lean's rule a "BAT" right in front of a "FOLD epsilon" belongs to the
fold: the row has one part of 2 + k rounds.

The fold is a parameter here. The rounds from "FOLD epsilon" on are a sub-protocol that other kinds
share, and its prover's side is written elsewhere. So the half takes that part as a parameter, `fold`.
The parameter comes without the round "BAT": it has 1 + k moves, and `closePart` lays "BAT" in front
of it by `Part.andThen`. For a part that already begins with a move for "BAT" (2 + k moves) there is
`closeHalfWhole`. `foldDue` and `wholeDue` are the tests on the parameter. Neither maker of a half asks
them: whoever lists a half asks them. Names, counts and the cut are also held by the frame when a
chain is laid (`lend`, `chainSteps`); the stated shares by nothing else.

  `closePlace`, `closeAddr`   the place of the kind's block; the address of its one part
  `Borne`                     one oracle message whose coins the part carries
  `ClosePub`                  the kind's public data: the block's numbers; the messages carried
  `closeSpends`               the one run that is spent: the 2 k + 1 coefficients of the fold's
                              hiding polynomial, which are coins of the fresh mask's sender
  `closeCarries`              the runs that are carried: one for each message of the list
  `closeBatPart`              the round "BAT": nothing is sent
  `foldDue`                   the parameter has no coin of its own, these runs, 1 + k moves, and
                              states the shares 0 of 1
  `closePart`, `closeHalf`    the part; the kind's half
  `wholeDue`, `closeHalfWhole`   the like for a parameter that begins with a move for "BAT"

The stops. The round "BAT" has none. The block's decision tests no equation, and none of its guards
was found to hang on a challenge (by one reading of the text, guard by guard): so the kind adds no
stop to the parameter's, and `foldDue` asks that the parameter states 0 of 1 twice.

Limits. Nothing here holds the list of carried messages against a description or a book: it is public data that a caller
lays. `foldDue` cannot ask that the parameter's stops never stop: it reads the stated shares. No property of the
protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.First.Close.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.Close (Par)

variable {V W X : Type}

/-- The place of the kind's block (`Close.kind`, Johnson/Desc/First/Close/Kind.lean). -/
def closePlace (P : Par) : Place := ⟨1, some P.link, P.piece, .K10⟩

/-- The address of the row's one part. -/
def closeAddr (P : Par) : Addr := ⟨closePlace P, 0⟩

/-- **An oracle message whose coins the part carries**: the part that holds its sending; its number
in that sending, from 0; how many coins it has. -/
structure Borne where
  sender : Addr
  msg : Nat
  count : Due
  deriving DecidableEq, Repr

/-- **The kind's public data**: the numbers of the block's place; the oracle messages that the part
carries, in the book's order. -/
structure ClosePub where
  par : Par
  borne : List Borne

/-- **The run that is spent**: the coefficients of the fold's hiding polynomial. -/
def closeSpends (P : Par) : List (String × Due) :=
  [(runName foldMaskRun (closeAddr P) "fold", ⟨0, 2 * P.k + 1⟩)]

/-- **The runs that are carried**: all coins of each message of the list. -/
def closeCarries (Z : ClosePub) : List (String × Due) :=
  Z.borne.map fun m => (carriedName m.sender m.msg (closeAddr Z.par), m.count)

/-- The round "BAT": nothing is sent. -/
def closeBatPart : Part V W X :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun _ _ _ => .ok ⟨[], []⟩, fun t => t.own⟩] }

/-- **The test on the parameter**: no coin of its own; the runs as this file names and counts them;
a move for "FOLD epsilon" and one for each "FOLD round"; the stated shares 0 of 1. -/
def foldDue (Z : ClosePub) (fold : Part V W X) : Bool :=
  fold.takes == ⟨0, 0⟩ && fold.spends == closeSpends Z.par && fold.carries == closeCarries Z &&
    fold.moves.length == 1 + Z.par.k && fold.badShare == ⟨0, 1⟩ && fold.hidShare == ⟨0, 1⟩

/-- The like for a part that begins with a move for "BAT". -/
def wholeDue (Z : ClosePub) (whole : Part V W X) : Bool :=
  whole.takes == ⟨0, 0⟩ && whole.spends == closeSpends Z.par && whole.carries == closeCarries Z &&
    whole.moves.length == 2 + Z.par.k && whole.badShare == ⟨0, 1⟩ && whole.hidShare == ⟨0, 1⟩

/-- **The part**: the round "BAT", then the fold. -/
def closePart (fold : Part V W X) : Part V W X := closeBatPart.andThen fold

/-- **The kind's half.** fold: the prover's side of the rounds from "FOLD epsilon" on, of the kind's
public data. -/
def closeHalf (fold : ClosePub → Part V W X) : KindHalf ClosePub V W X :=
  fun Z => ⟨closePlace Z.par, [closePart (fold Z)]⟩

/-- The kind's half, of a part that holds all 2 + k rounds. -/
def closeHalfWhole (whole : ClosePub → Part V W X) : KindHalf ClosePub V W X :=
  fun Z => ⟨closePlace Z.par, [whole Z]⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closePlace
#print axioms ProofFile.Honest.K10.closeAddr
#print axioms ProofFile.Honest.K10.Borne
#print axioms ProofFile.Honest.K10.ClosePub
#print axioms ProofFile.Honest.K10.closeSpends
#print axioms ProofFile.Honest.K10.closeCarries
#print axioms ProofFile.Honest.K10.closeBatPart
#print axioms ProofFile.Honest.K10.foldDue
#print axioms ProofFile.Honest.K10.wholeDue
#print axioms ProofFile.Honest.K10.closePart
#print axioms ProofFile.Honest.K10.closeHalf
#print axioms ProofFile.Honest.K10.closeHalfWhole

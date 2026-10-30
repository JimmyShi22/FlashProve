-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Marks.lean: A MARK: an event of the challenges at which the
verifier refuses nothing, and which has to be counted all the same: because a fall behind it can be
bounded only where the mark has not spoken. A fall (`Fall`, Honest/Side.lean) is a test on the
verifier's state in front of a member and on that member's challenges. A mark is a test on
challenges alone: ALL THOSE IN FRONT OF A MEMBER, THOSE IN FRONT OF ITS CHAIN FIRST, and that
member's own. It has a stated share of its own, so that it is paid ONCE, however many falls lean on
it. Definitions; no theorem.

  `Mark`, `markOf`, `Marks.sharesOk`

Limits. A list of marks is a letter of whoever covers a file's falls by gates
(Honest/Law/SharesFalls.lean): no field of `Sides` holds one yet. Nothing holds a mark's share
against its test here; nothing says which falls lean on it. WHICH CHALLENGES STAND IN FRONT OF A
CHAIN is said by whoever lays the gates (Honest/Law/CoverFile.lean: none in front of the first and
the shared chain; the first two chains' typed ones in front of the second). As a letter at one input
and one run's coins a mark may be made of these; as a field of a record that knows neither it could
not. `Mark.share` is spent by `markDebt_of_held` (Honest/Law/CoverSeat.lean) and read by `hq0_val`
and `hq0_num` (Honest/Law/CoverMarksJoin.lean). No law spends `Marks.sharesOk` yet. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Shares

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-- **A mark.** place: the member at whose rounds its chance lies. test: of all challenges in front
of that member, those in front of its chain first, and of the member's own; what it says is for a
print. share: A STATED NUMBER, NO BOUND. -/
structure Mark where
  place : Place
  test : List Fmt.Drawn → List Fmt.Drawn → Option String
  share : Odds

/-- The first mark at a place that says something. -/
def markOf (ms : List Mark) (a : Place) (fr own : List Fmt.Drawn) : Option String :=
  (ms.filter fun m => m.place == a).findSome? fun m => m.test fr own

/-- No stated share of a mark has the denominator 0. -/
def Marks.sharesOk (ms : List Mark) : Bool := ms.all (·.share.ok)

end ProofFile.Honest

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FramePin.lean: THE TWO TESTS OF FrameOne.lean: their text
alone. Definitions with code; no theorem.

Why this form. The text's frame numbers the messages by the statement's own numbers (g is the
number of all messages sent so far); a written front numbers them by their place in the old group's
list. So a record's front and a written front never have "the shapes of all messages in front, one
by one" in common. So `pinB` asks only what the maker of
frames and the clauses on the statement in front read, BY PLACE, and no number; `numsB` asks the
numbers.

  `pinB x₀ x` READS, ONE BY ONE, of each of the two fronts:
     1 the codes (st.codes)
     2 the shapes of the kept old messages, in the order of sending, each as the statement has it
       at that number, or nothing (so also: how many kept old messages there are)
     3 that every kept old message's number is below the number of messages in front
     4 the target's shape, 5 its cut for the main row's message, 6 its cut for the rest
     7 the shapes of the target's messages for the kept rows, in order
     8 the carried rows' main code's number, 9 mask code's number, 10 number of mask rows,
    11 count of kept rows.
   WITHIN each front it uses the kept old messages' numbers, to look their shapes up, and holds
   them against the number of messages in front (3). BETWEEN the two fronts it compares no number
   of a message and not how many messages stand in front.
   IT DOES NOT READ: the other announcements; a class of leaves; "kept again"; any other message's
   shape; a row, a form, a claim's target, a challenge or a sample.
  `numsB grp rows n0 olds x`: the number of the group that the switch leads into; how many rows that
     group has; how many messages stand in front; THE KEPT OLD MESSAGES' OWN NUMBERS, in order.
  `headLinkB s`: a test on the RECORD, not on the front: at the head's link the head's copy of the
     frame stands at the link at which the chain's frame stands.
Each of the three can fail.

-/
import Johnson.Top.H0.K2Hands.FrameOfFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes

/-- The shapes of the kept old messages of a front, in the order of sending: each as the statement
in front has it at that number, or nothing. -/
def keptShapes (x : _root_.Tw.K2.Front) : List (Option OracleShape) :=
  (switchKept x.f.rows).toList.map fun o => (x.st.oracles[o]?).map (·.shape)

/-- Every kept old message's number is below the number of messages in front. -/
def keptBelowB (x : _root_.Tw.K2.Front) : Bool :=
  (switchKept x.f.rows).all fun o => decide (o < x.st.oracles.size)

/-- **A TEST WITH CODE: THE FRONT x HAS THE PUBLIC SIDE OF THE FRONT x₀, BY PLACE.** -/
def pinB (x₀ x : _root_.Tw.K2.Front) : Bool :=
  decide (x.st.codes = x₀.st.codes) && decide (keptShapes x = keptShapes x₀) &&
    keptBelowB x && keptBelowB x₀ &&
    decide (x.T.shape = x₀.T.shape) && decide (x.T.main = x₀.T.main) &&
    decide (x.T.rest = x₀.T.rest) &&
    decide (x.T.kept.toList.map (·.shape) = x₀.T.kept.toList.map (·.shape)) &&
    x.f.rows.code == x₀.f.rows.code && x.f.rows.maskCode == x₀.f.rows.maskCode &&
    x.f.rows.masks == x₀.f.rows.masks && x.f.rows.keptRows == x₀.f.rows.keptRows

/-- **A test with code on a front's numbers**: the group that the switch leads into; how many rows
that group has; how many messages stand in front; the kept old messages' own numbers. -/
def numsB (grp rows n0 : ℕ) (olds : List ℕ) (x : _root_.Tw.K2.Front) : Bool :=
  x.f.group == grp && (x.st.groups[x.f.group]?).any (fun G => G.rows.size == rows) &&
    x.st.oracles.size == n0 && (switchKept x.f.rows).toList == olds

/-- **A test with code on the record**: at the head's link the head's copy of the frame stands at
the chain's frame's link. Elsewhere: yes. -/
def headLinkB (s : S) : Bool :=
  match s.here with
  | .head a => a.fr.link == s.check.frame.link
  | _ => true

end VerifiableInference.Desc.First.K2Hands

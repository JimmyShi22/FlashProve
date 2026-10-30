-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Seat.lean: the proximity test's block (the kind K12) seated at the shared chain's
two places: the test on the folded row's group G_u, and the test on G_omega.

This file holds definitions only; no theorem is stated.

The kind's block runs at a record of its own, T12 (Johnson/Desc/K12/Join.lean), which is made when
the block begins and is dropped when it ends (Block.inside, Johnson/Desc/Block.lean). This file says
how T12 is made of the shared chain's carried state (St, Johnson/Desc/K14/Text.lean) and what is
laid back.
  enter reads   the statement; the book of trees; the count of roots received; the number of the
                group under test; the number of the message that holds the first fold's mask, if
                it went out earlier (at G_u: with the folded row; at G_omega: none: the first fold
                sends its own).
  enter asks    nothing. The front of the test (Johnson/Desc/K12/Front.lean: the schedule as it lies
                in the record, and the eight clauses on every claim that lies open on the group)
                stands inside the kind, as the first of its parts (frontJ,
                Johnson/Desc/K12/Join.lean; the joining guardedProximityTestParts calls it too): so it is asked
                wherever a block of these parts is seated. This file takes any block at T12.
  leave writes  the statement, the book of trees and the count of roots. Nothing else of the carried
                state is read or written by a test. Nothing is asked of what else T12 holds at the
                end.
Rounds and columns reach the block by Block.step, not through the state.

What is not here. The kind's text (its frame and the joining of its parts) and the numbers of the
two places (P12). Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Text
import Johnson.Desc.K12.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Seat
open OnBytes OnBytes.Params Desc.Plain Desc.K14
open VerifiableInference.Desc (Block)

/-- READS. g: which of the carried record's groups is under test; mask: which message holds the
first fold's mask. -/
def enter (g : Lin → Nat) (mask : Lin → Option Nat) (d : St) : Except String T12 :=
  .ok { st := d.st, book := d.book, roots := d.roots, g := g d.loc, pass := .nothing
        mask := mask d.loc }

/-- WRITES. -/
def leave (d : St) (t : T12) : Except String St :=
  .ok { d with st := t.st, book := t.book, roots := t.roots }

/-- **The test on G_u**: b: the kind's block at that place's numbers. -/
def onGu (b : Block T12 Unit) : Block St Unit := Block.inside (enter (·.gU) (·.firstMask)) b leave

/-- **The test on G_omega.** -/
def onGomega (b : Block T12 Unit) : Block St Unit :=
  Block.inside (enter (·.gOmega) fun _ => none) b leave

end VerifiableInference.Desc.K12.Seat

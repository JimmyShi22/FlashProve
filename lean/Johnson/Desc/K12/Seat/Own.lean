-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Seat/Own.lean: the proximity test's block (the kind K12) seated at the request's
own test, on the proof file's last chain.

This file holds definitions only; no theorem is stated.

The kind's block runs at a record of its own, T12 (Johnson/Desc/K12/Join.lean), which is made when
the block begins and is dropped when it ends (Block.inside, Johnson/Desc/Block.lean). This file says
how T12 is made of the last chain's carried state (S₃, Johnson/Desc/Third/State.lean) and what is
laid back. The like for the shared chain: Johnson/Desc/K12/Seat.lean.
  enterOwn reads   the statement; the book of trees; the count of roots received on this chain; the
                   own group's number; the number of the message that holds the first fold's mask.
  enterOwn asks    nothing. The front of the test (Johnson/Desc/K12/Front.lean) stands inside the
                   kind, as the first of its parts (frontJ, Johnson/Desc/K12/Join.lean; the joining
                   guardedProximityTestParts calls it too): so it is asked wherever a block of these parts is
                   seated. This file takes any block at T12.
  leaveOwn writes  the statement, the book of trees and the count of roots. Nothing is asked of what
                   else T12 holds at the end.
Not here: the test that ties the book's tree for Omega to the source that the block's own rounds
declare ("taken from the shared chain, number n"). The last chain lays it in a block of its own,
without a round, in front of this place, and reads the declared rounds off this very block.

What is not here. The kind's text; the numbers of the place (P12: its rounds must name W's and the
index masks' trees as taken from the first chain and Omega's as taken from the shared chain); the
last chain's state. The number in the leaves' hashes of this chain's own tree number 0 (the first
chain's trees and one) reaches the block by P12's numbers (nums.firstTree), not by T12: the count of
roots is 0 at this place while the book holds the earlier chains' trees. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Desc.Third.State
import Johnson.Desc.K12.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Seat
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃)

/-- READS. -/
def enterOwn (s : S₃) : Except String T12 :=
  .ok { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
        mask := s.loc.mask }

/-- WRITES. -/
def leaveOwn (s : S₃) (t : T12) : Except String S₃ :=
  .ok { s with st := t.st, book := t.book, roots := t.roots }

/-- **The request's own test**: b: the kind's block at that place's numbers. -/
def onOwn {Cl : Type} (b : Block T12 Cl) : Block S₃ Cl := Block.inside enterOwn b leaveOwn

end VerifiableInference.Desc.K12.Seat

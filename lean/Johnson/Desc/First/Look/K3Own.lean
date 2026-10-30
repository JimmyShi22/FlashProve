-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Own.lean: the blocks of the kind "lookup" on the proof file's first chain,
by address: from the public record and a place to the block there, at the state that the first chain
carries (Johnson/Desc/First/State.lean). Definitions with code. No theorem.

A link of the first chain has two lookups: one on its calls, one on the digits of its smallness
test. A fold over blocks asks for the block at an address (`Place`, Johnson/Desc/Block.lean: chain,
link, piece, kind). Here the address is answered from the public record alone: the place's
parameters are `placeAt`'s (Johnson/Desc/First/Look/LookKind.lean), the seat is `seatCalls` or
`seatDigits` (Johnson/Desc/First/Look/K3Seat.lean), the block is `Law.blockVia`
(Johnson/Desc/First/Look/Via/Via.lean): the kind's block with the hearing on a view's rounds over
the parts' own texts (`hearV`, Via/Rounds.lean), whose test on the plan asks `fitsVia` besides.

Main names:
  `isHead X i`: link i is the head's, the last.
  `pieceAt X i digits`: the number inside link i at which that lookup stands.
  `theOwn claim runs X codes shape a`: **the block at the address a**, or nothing where no lookup
    stands or where `placeAt`, `beforeAt`, `laidAt` or `padKeyAt` gives nothing.

Limits: the four numbers of pieces (2 and 7; at the head 3 and 8) are literals: they are the table
of places' of whoever folds, and nothing here holds them against it. `laid`, the calling kind's own
count of padding places, is `laidAt`'s (Johnson/Desc/First/Look/Laid.lean: laid among the lookups'
files for the calling kinds' files, which own these counts): made of the lists of columns, apart
from the place's `pub`: that clause of the test on the plan is not idle; at a layers' link and
the head both come of the same lists, so a fault in a list is not seen; the calling kinds' test that
a call's padding key is 0 before the shift (`padKeyAt`, the same file: the verifier program asks it
at the digits and at attention) is a conjunct of the block's test on the plan here, at all four
kinds of place alike (true where the program has none). `before` is the list of
Johnson/Desc/First/Look/Before.lean: at the calls the roots of the link's first send; at the digits
these and the roots of its last moment's send: that these roots hold the arrays that the keys read
is not shown; the grain is a tree. No guest is handed: the run "guests" makes no claim. With `runs
:= false` the block has no run of claims at all: for a fold whose batching does not call them and
whose links' orders do not name them; what was heard then reaches no claim. The limits of the files
named above hold here too. Nothing has been shown of it.
(Where this and lean/THEOREM.md differ, the page
holds.)

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Seat
import Johnson.Desc.First.Look.Before
import Johnson.Desc.First.Look.Laid
import Johnson.Desc.First.Look.Via.Via

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Aff)

/-- Link i is the head's: the last of the chain, behind the groups' links. -/
def isHead (X : Model.Verify.Public) (i : Nat) : Bool := i == (if X.p4 then 2 else 1) * X.NGr

/-- The number inside link i at which the lookup on the calls, or on the digits, stands. -/
def pieceAt (X : Model.Verify.Public) (i : Nat) (digits : Bool) : Nat :=
  if isHead X i then (if digits then 8 else 3) else (if digits then 7 else 2)

/-- **The block of the kind "lookup" at an address.** claim: a linear form, claimed to be 0, as a
claim. runs: with its named runs of claims ("objects", "guests"); else without any. Nothing unless
the address says chain 1, a link, the kind K3 and one of that link's two pieces, the public record
has such a place and gives the host's count of padding places (`laidAt`: made apart from the
place's own `pub`, against which `planOk` holds it) and the test on the padding key (`padKeyAt`: a
conjunct of `planOk`), and the first chain's codes and shape give the list of what must have been
sent.
codes, shape: the first chain's (the parameter bytes' items): the public record does not hold them.
-/
def theOwn {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) : Option (Block First.S Cl) :=
  if a.chain != 1 || a.kind != .K3 then none else
  a.link.bind fun i =>
    [false, true].findSome? fun digits =>
      if a.piece != pieceAt X i digits then none else
      (First.Look.placeAt X i digits).bind fun p =>
        (First.Look.beforeAt codes shape i digits).bind fun sent =>
          (First.Look.laidAt X i digits).bind fun laid =>
            (First.Look.padKeyAt X i digits).map fun key =>
              let seat := if digits then seatDigits claim else seatCalls claim
              let b₀ := Law.blockVia seat a.piece laid sent p []
              let b := { b₀ with planOk := b₀.planOk && key }
              if runs then b else { b with claims := [] }

end VerifiableInference.Desc.K3

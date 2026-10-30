-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Seat.lean: where the state that the proof file's first chain carries
(Johnson/Desc/First/State.lean) keeps what the kind "lookup" reads and writes
(Johnson/Desc/First/Look/K3Lookup.lean). Definitions with code. No theorem.

A link has two places of the kind. Each seat is meant to find and leave the carried state as the
verifier program's routine at that place finds and leaves it.

Main names:
  `seatCalls claim`: at the lookup on a link's calls: what was heard goes where the kind of link
    keeps it, and into a field of its own that is empty until then (`S.hearLook`, `S.lookHeard?`).
  `seatDigits claim`: at the lookup on the smallness test's digits: what was heard goes into that
    test's record, with the three numbers that the program lays there
    (OnBytes/Model/Tail.lean:725-726): its count of draws; the ledger's next free slot in front of
    the lookup and behind it.

Limits: where no link is open `fork` gives nothing and the kind refuses; `mark` then changes
nothing; `put` at the digits then marks the state (the smallness test's record is there wherever the
ledger is: so no run of the kind's block reaches that arm). At both seats `heard` is nothing until
the hearing: so the kind's run of claims refuses in front of it. At the calls a second hearing in
one link leaves the state as it is, with a mark (`S.hearLook`); the kind's `decide` refuses one in
front of that, by its own test that nothing is heard yet (K3Lookup.lean), and by the ledger's count, which
the first has moved. What `heard` reads behind `put`: Johnson/Desc/First/Look/K3SeatLaw.lean. A step
of the same link that lays a value by `S.putLook` behind the hearing turns what other texts read by
`S.look?`, not what this seat reads. At the digits the place's calls, padding numbers and lid are
told twice: in the kind's parameters and in the smallness test's record, from which that test's
later claims take them: nobody compares the two. The three numbers at the digits belong to the
smallness test's kind; they stand here so that the state behind the place is the program's. The slot
in front is read off the ledger in front of the lookup; the program takes it earlier
(Tail.lean:720), and the state carries that number too; that nothing between takes a slot is a
reading. Nothing has been shown of it.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.State
import Johnson.Desc.First.Look.K3Lookup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Aff)

/-- At the lookup on a link's calls. -/
def seatCalls {Cl : Type} (claim : Aff → Cl) : Seat First.S Cl where
  fork := fun s => s.fork?
  owed := fun s => s.rowsOwed
  put := fun s g G => (s.putFork G).hearLook g
  mark := fun s G => s.putFork G
  heard := fun s => s.lookHeard?
  claim := claim

/-- At the lookup on the smallness test's digits. -/
def seatDigits {Cl : Type} (claim : Aff → Cl) : Seat First.S Cl where
  fork := fun s => s.fork?
  owed := fun s => s.rowsOwed
  put := fun s g G =>
    match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test"
  mark := fun s G => s.putFork G
  heard := fun s => s.tl?.bind (·.heard)
  claim := claim

end VerifiableInference.Desc.K3

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Stored/HeadRidesB.lean: TWO TESTS WITH CODE ON A CARRIED RECORD, for two public items that
ride through the output head's first blocks: definitions alone; no Mathlib.

  noTablesB s        the record stands in the head's link, and the tables of reads are not laid.
  readsWideB iU3 n s the open ledger holds the array number iU3, and it has at least n columns.

WHY. What the kind's law on the head's own block asks of the record behind that block's yes (that
the readers' second hole speaks there; that each table of reads ends inside the array) follows from
these two; both are MEANT to be made in front of that block and kept by the blocks between (of
these keepings some are proved in their kinds' files, some are owed); neither stood in the promise.
WHAT IT IS NOT. No law. Which blocks make, keep, ask and drop them is the table's door's to book.
What they say: Johnson/Desc/Kinds/Law/HeadRidesSays.lean.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open VerifiableInference.Desc.First (S)

/-- The record stands in the head's link, and the tables of reads are not laid. -/
def noTablesB (s : S) : Bool :=
  match s.here with
  | .head o => o.t.isNone
  | _ => false

/-- The open ledger holds the array number iU3, and it has at least n columns. -/
def readsWideB (iU3 n : Nat) (s : S) : Bool :=
  match s.fork? with
  | some F =>
    match F.trees[iU3]? with
    | some tr => Decidable.decide (n ≤ tr.K)
    | none => false
  | none => false

end VerifiableInference.Desc.Kinds.Head

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameEntriesDefs.lean: the free entries of the index-mask message's ledger: THE
DEFINITIONS WITH CODE ALONE, over FrameLaw.lean (no Mathlib beneath): for a layer of the table of
joints' filling that lays the public item "pile.room". The lemmas: FrameEntries.lean.

  freeOf s           the free entries of that ledger, in the verifier's state s: 0 where there is
                     no such ledger or it is closed
  endTakes fvs kCol  what the end of the request takes beside the rows: roomOf's second summand
  rowsFrom fvs m     how many links from link m on leave a row
  roomB fvs e m s    a Bool on the state: rowsFrom fvs m + e is at most freeOf s (a bound)
  leftIsB n s        a Bool: the ledger is there, not closed, and has just n entries left
  rowsBefore fvs m   how many links in front of link m leave a row
  roomIsB free0 fvs m s   THE ITEM "pile.room" at segment m: leftIsB at free0 - rowsBefore fvs m

No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc.First (S)

/-- The free entries of the index-mask message's ledger, in the verifier's state. -/
def freeOf (s : S) : Nat :=
  match Law.ledgerAt s with
  | some l => if l.closed then 0 else l.left
  | none => 0

/-- What the end of the request takes beside the rows: roomOf's second summand. -/
def endTakes (fvs : List Bool) (kCol : Nat) : Nat :=
  if (fvs.filter id).length > 1 then 1 + 2 * kCol else 0

/-- How many links from link m on leave a row. -/
def rowsFrom (fvs : List Bool) (m : Nat) : Nat := ((fvs.drop m).filter id).length

/-- A Bool on the verifier's state: the rows from link m on, and e more, find free entries. -/
def roomB (fvs : List Bool) (e m : Nat) (s : S) : Bool := decide (rowsFrom fvs m + e ≤ freeOf s)

/-- A Bool on the verifier's state: the index masks' ledger is there, is not closed, and has JUST n
entries left. -/
def leftIsB (n : Nat) (s : S) : Bool := (Law.ledgerAt s).any fun l => !l.closed && l.left == n

/-- How many links in front of link m leave a row. -/
def rowsBefore (fvs : List Bool) (m : Nat) : Nat := ((fvs.take m).filter id).length

/-- **The public item "pile.room" at segment m**, as it was settled for the table: not closed, and
left is the fresh ledger's free count less the bearing segments in front of m. -/
def roomIsB (free0 : Nat) (fvs : List Bool) (m : Nat) (s : S) : Bool :=
  leftIsB (free0 - rowsBefore fvs m) s

end Johnson.Desc.First.Walk.Tied

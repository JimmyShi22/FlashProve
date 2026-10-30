-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Opened.lean: the opened columns of a view, by the place of their opening.

A view (`Fmt.View`) holds all opened columns of a chain in one list. Each stands under a key that
is made from its tree's number. The key does not tell a tree that the chain has taken over from
an earlier chain apart from the chain's own trees. The order of the list does: round by round; in
a round the stored trees first, then the trees of `Fmt.Round.opens` in their order; in an opening
the positions of its list, increasing. The list of each opening follows from the description and
from the positions that the round drew. So the one list can be cut again into its openings.
With the cut a column can be read by three numbers: the round, the place of the opening in that
round, and the position. The program's decisions do not use the cut: they read the view's list in
its order (OnBytes/Iop/Ground.lean). Only OnBytes/Chain/OpenedLaws.lean and a test import this file.

Main definitions: `Opening`, `listsOf`, `openedByPlace`, `openingAt`, `Opening.column`.
That the cut succeeds on every view that the reader returns is proved in
OnBytes/Chain/OpenedLaws.lean.
-/
import OnBytes.Base
import OnBytes.Chain.Lists
import OnBytes.Chain.Draws

namespace OnBytes

/-- One opening of a tree, as a decision sees it: the positions of its list, increasing, each
with the column that was opened there. -/
abbrev Opening : Type := List (Nat × List F)

/-- The lists at which the openings of one round stand, in the order of the file. r is the round,
ts are the stored trees that it opens, poss are the positions as the round drew them.
A stored tree is opened at its own part of the draws. A tree of depth a is opened at the draws
modulo 2 ^ a. Each list is a set: increasing, each position once. -/
def listsOf (r : Fmt.Round) (ts : List Fmt.Stored) (poss : List Nat) : List (List Nat) :=
  ts.map (fun t => listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) ++
    r.opens.map fun o => listOfT (poss.map (· % 2 ^ o.1.a))

/-- Takes one opening for each of the given lists off the front of l. Returns the openings and
what is left of l. Returns nothing if the positions in l are not those of the lists. -/
def takeOpenings : List (List Nat) → List (Nat × Nat × List F) →
    Option (List Opening × List (Nat × Nat × List F))
  | [], l => some ([], l)
  | xs :: ls, l =>
    if (l.take xs.length).map (·.2.1) == xs then
      match takeOpenings ls (l.drop xs.length) with
      | none => none
      | some (os, rest) => some ((l.take xs.length).map (·.2) :: os, rest)
    else none

/-- Takes the openings of all rounds off l and appends them to acc, one entry for each round.
Returns nothing if the description and the view differ in their number of rounds, if positions
do not fit, or if something of l is left. -/
def takeRounds : List (Fmt.Round × List Fmt.Stored) → List Fmt.RoundView →
    List (Nat × Nat × List F) → Array (Array Opening) → Option (Array (Array Opening))
  | [], [], [], acc => some acc
  | r :: rs, v :: vs, l, acc =>
    match takeOpenings (listsOf r.1 r.2 v.drawn.poss) l with
    | none => none
    | some (os, rest) => takeRounds rs vs rest (acc.push os.toArray)
  | _, _, _, _ => none

/-- The opened columns of the view v of a chain with the description S, by place. The outer array
has one entry for each round, from 0. The inner array has one entry for each opening of that
round, in the order of the file: the stored trees first, then the trees of `Fmt.Round.opens`.
Returns nothing if v is not the view of a chain with this description. -/
def openedByPlace (S : Fmt.SpecX) (v : Fmt.View) : Option (Array (Array Opening)) :=
  takeRounds (zipT S.base.rounds S.stored) v.rounds v.opened #[]

/-- The opening at the given place of the given round, both counted from 0. -/
def openingAt (a : Array (Array Opening)) (round place : Nat) : Option Opening :=
  a[round]?.bind fun r => r[place]?

/-- The column at the position pos. For a tree of depth a below a draw x from a longer range,
pos is x % 2 ^ a. -/
def Opening.column (o : Opening) (pos : Nat) : Option (List F) :=
  (o.find? fun p => p.1 == pos).map fun p => p.2

end OnBytes

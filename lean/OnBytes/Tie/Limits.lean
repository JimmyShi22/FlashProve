-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Limits.lean: which chains the theorems of OnBytes/Tie/OneChain.lean cover, as a test
that runs.

These theorems tie an accepted chain to the compiled verifier of the library's theory. They hold for
descriptions within certain limits. This file names each limit and gives a function that lists the
limits that a description breaks. A chain that breaks `storedTable` alone can still be covered: the
test is then `withinX` (OnBytes/Tie/StoredMain.lean).

Main definitions: `Limit`, `inFile`, `limitsOf`, `limitsOfX`; beside them the test `eachOnce`.
That an empty list means "covered" is a theorem of OnBytes/Tie/OneChain.lean (`within_iff`).
"Covered" does not mean that the chain opens all its trees: for that see `eachOnce`.
It claims nothing on what a chain proves.
-/
import Fmt.Rules8X

set_option autoImplicit false

namespace OnBytes.Tie

/-- A limit of OneChain.lean's theorems, named by how a chain breaks it. -/
inductive Limit where
  /-- `inFile S` is not in order (`Fmt.Spec.ok`) -/
  | notInOrder
  /-- some round sends more than one root -/
  | severalRoots
  /-- the chain opens a tree that it has taken over from another chain -/
  | takenOver
  /-- some tree that the chain sends is opened more than once -/
  | notOnce
  /-- the chain has no random bytes -/
  | noRandomBytes
  /-- some round opens a stored table; for such a chain the test is `withinX`
  (OnBytes/Tie/StoredMain.lean) -/
  | storedTable
  deriving DecidableEq, Repr, Inhabited

/-- The same description, with the chain's random bytes in the file. The protocol that the library
makes from a description does not depend on where these bytes are. -/
def inFile (S : Fmt.Spec) : Fmt.Spec := { S with rand := .inFile }

/-- The number by which an opening names a tree of the chain's own; nothing for a tree that was
taken over. -/
def ownNumber (o : Fmt.Shape × Fmt.Src) : Option Nat :=
  match o.2 with
  | .own n => some n
  | .given _ _ => none

/-- All openings of a chain's own and taken-over trees, in the order of the rounds. -/
def opensOf (S : Fmt.Spec) : List (Fmt.Shape × Fmt.Src) := S.rounds.flatMap (·.opens)

/-- No round sends more than one root. -/
def oneRoot (S : Fmt.Spec) : Bool := S.rounds.all (·.entry.roots ≤ 1)

/-- No opened tree is one taken over from another chain (each opening names a tree by its own
number; that this number is below the count of trees the chain sends is not tested here).
`Fmt.Spec.ok`, which `notInOrder` tests, asks more than that bound: the number is below the count of
roots sent up to and with the opening's round. -/
def ownOnly (S : Fmt.Spec) : Bool := (opensOf S).all fun o => (ownNumber o).isSome

/-- Every tree that the chain sends is opened exactly once. This is no limit. It is a test for a
description that is meant to open all its trees: it notices an opening that was left out by
mistake, which `atMostOnce` does not. -/
def eachOnce (S : Fmt.Spec) : Bool :=
  (List.range ((S.rounds.map (·.entry.roots)).sum)).all fun n =>
    ((opensOf S).filter fun o => ownNumber o == some n).length == 1

/-- Every tree that the chain sends is opened at most once. -/
def atMostOnce (S : Fmt.Spec) : Bool :=
  (List.range ((S.rounds.map (·.entry.roots)).sum)).all fun n =>
    decide (((opensOf S).filter fun o => ownNumber o == some n).length ≤ 1)

/-- The limits that a description without stored tables breaks. Empty: the chain is covered. -/
def limitsOf (S : Fmt.Spec) : List Limit :=
  (if (inFile S).ok then [] else [.notInOrder]) ++
  (if oneRoot S then [] else [.severalRoots]) ++
  (if ownOnly S then [] else [.takenOver]) ++
  (if atMostOnce S then [] else [.notOnce]) ++
  (if S.rand.isNone then [.noRandomBytes] else [])

/-- The same for a description that may open stored tables. Empty: the chain opens none and is
covered by the theorems of OnBytes/Tie/OneChain.lean. -/
def limitsOfX (S : Fmt.SpecX) : List Limit :=
  limitsOf S.base ++ (if S.stored.all (·.isEmpty) then [] else [.storedTable])

end OnBytes.Tie

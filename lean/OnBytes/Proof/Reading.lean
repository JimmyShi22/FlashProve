-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/Reading.lean: readings of a file that say where they refuse.

The check of a file goes through many steps. A person who looks at a refused file wants to know at
which step it failed. The names that are made here say so. They come from a fixed, finite list and
hold nothing that was read from a file. Whether a file is accepted depends on no name; whether a
whole call ends as a no or as not checked does (`Model.Verify.refusalName`).
The words chain, block, view and strict reader are explained in OnBytes/Iop/Ground.lean.

A refusal of the strict reader is named `<front>reader-<kind>`. `front` says which chain it was, and
the kind is one of description, form, work, listed-positions, opening, one-value-at-a-vertex
(OnBytes/Chain/Why.lean). The kind comes from a second pass over the chain. If that pass finds no
check that fails, which Why.lean does not claim to exclude, the name is `<front>reader`. A refusal
of a decision is named `<front>decision`. If the block has run to its end and the first named test
that failed is one of three, `-linear-claim`, `-symbols-at-positions` or `-reply` follows. A block
that stops early at a condition without a name gives the plain name, also after a named test has
failed. A name that a caller's part of the block gives to a failure is passed on unchanged.

Main definitions: `Reading`, `need`, `readNamed`, `refusalName`, `judge`, `namesOf`.

What is not claimed: no theorem says that the lists of names hold every name that can come out.
-/
import OnBytes.Chain.Session
import OnBytes.Chain.Why
import OnBytes.Iop.Ground

namespace OnBytes.Proof

/-- A reading within a session that names the step at which it refuses. A session is all that one
verdict reads, here one file: it keeps the tree vertices that were met, so that a second value at a
vertex under one root is refused (OnBytes/Chain/Session.lean). -/
abbrev Reading : Type → Type := StateT Session (Except String)

/-- Turns a reading that refuses without a word (`InSession`) into one that refuses under the name
`why`. -/
def step {α : Type} (why : String) (x : InSession α) : Reading α := fun s =>
  match x s with
  | none => .error why
  | some y => .ok y

/-- The value of x, or a refusal under the name `why`. -/
def need {α : Type} (why : String) (x : Option α) : Reading α := fun s =>
  match x with
  | none => .error why
  | some a => .ok (a, s)

/-- Runs a reading from the empty record of vertices. -/
def Reading.fromStart {α : Type} (w : Reading α) : Except String α :=
  (w Session.start).map (·.1)

/-- The name of a refusal by the strict reader. `front` says which chain it was; it is empty or
ends in a hyphen. -/
def readerName (front : String) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    String :=
  match whyRefused S seen b i with
  | some (k, _) => front ++ "reader-" ++ k.name
  | none => front ++ "reader"

/-- Reads the chain with the description S that begins at byte i of b. A refusal says which chain
it was and which kind of check fails first in a second pass over the chain
(OnBytes/Chain/Why.lean). -/
def readNamed (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) : Reading ChainRead :=
  fun s =>
    match readIn S b i s with
    | some y => .ok y
    | none => .error (readerName front S s.seen b i)

/-- The name under which the comparison of the reply is made. -/
def replyCheck : String := "the reply"

/-- The names of a failed run that no named test has given (OnBytes/Iop/Ground.lean): a condition
without a name failed; the view lacks an item, a round or an opened column that the block asks for,
or has one left over; the block's rounds are not those of the chain's plan; a code's message length
is no power of two. -/
def plainFailures : List String := [unnamed, shapeName, planName, Blk.codesName]

/-- The name of a refusal by a chain's decision. `first` is the name under which the block's run has
failed. Three names of tests become `<front>decision` followed by a word, and the names in
`plainFailures` become `<front>decision` alone. Any other name was given by the caller's part of the
block (a sub-proof, for example) and is returned as it is, so that the caller can tell it from the
names that are made here (`namesOf`). The two names that begin with BASE are made in
OnBytes/Iop/Prox.lean; a test holds them equal (OnBytes/Proof/TestFile.lean). -/
def refusalName (front : String) (first : String) : String :=
  if first == "BASE: the linear claim" then front ++ "decision-linear-claim"
  else if first == "BASE: the symbols at the positions" then
    front ++ "decision-symbols-at-positions"
  else if first == replyCheck then front ++ "decision-reply"
  else if plainFailures.contains first then front ++ "decision"
  else first

/-- The decision of a chain: one run of the block b, started from s, on the view v. Returns the
value with which the block ends, or the name of the refusal. When a run is refused is said at
`Blk.runOn` (OnBytes/Iop/Ground.lean). -/
def judge {α : Type} (front : String) (b : Blk α) (s : Start) (v : Fmt.View) : Except String α :=
  match b.runOn s v with
  | .ok a => .ok a
  | .error f => .error (refusalName front f.name)

/-- The names that `readNamed` and `judge` make themselves for one chain. `judge` can also return a
name that a caller's part of the block has given (`refusalName`). Such a name is not listed. -/
def namesOf (front : String) : List String :=
  ([front ++ "reader"] ++
    ([ReaderCheck.description, .form, .work, .listed, .opening, .vertex].map fun k =>
      front ++ "reader-" ++ k.name)) ++
  (["", "-linear-claim", "-symbols-at-positions", "-reply"].map fun x => front ++ "decision" ++ x)

end OnBytes.Proof

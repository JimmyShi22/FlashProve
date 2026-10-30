-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8XPieces.lean: what lies where in the bytes of a chain, and of a file of several chains, as
a list that is computed from the chains' descriptions.

A chain in a file has no length, count or offset of its own (docs/format/FORMAT.md, 7.1): a reader
knows from the description alone what comes next. The strict reader of Fmt/Rules8X.lean follows the
description as it reads. This file says the same order as data: the list of a chain's pieces, each
with its length. A piece is the chain's random bytes, an item of a prover's message, a nonce, a
round's listed positions, or an opening. The length of the first three follows from the
description. The length of a list and of an opening also depends on the positions that the round
has drawn, so it is a function of these draws. The list is made of the very description under which
the strict reader reads.

Sources. The definitions were written from the strict reader's own text, clause by clause:
`roundX`, `readStored` (Fmt/Rules8X.lean), `readOpens`, `readNonce`, `readList` (Fmt/Rules8.lean)
and `rdOpening` (Fmt/Rules7.lean). These render the format page (docs/format/FORMAT.md, which comes
with the programs, the C++ implementation that comes with this Lean code): R8.1, R8.2 (the items of
a chain in a file), R8.7 (after a round that draws positions: the nonce, the list, the stored
trees' openings, the chain's own), R7.8, R7.9 (an opening: the columns with their salts, then the
given digests), R7.19 (a stored tree's part of the draws). No Mathlib.

1. What the file contains.
   `TreeOf`: Whose tree is opened: a stored tree, by the number of the statement's item that has
     its root; a tree of the chain's own, by its place in the order of sending; a tree given from
     outside.
   `Opens`, `Opens.ofStored`, `Opens.ofOwn`: An opening as the description places it: whose tree;
     the tree's number; the depth; the elements of the base field in a column; the bytes of a
     leaf's salt; its part of the round's draws.
   `Opens.column`, `Opens.list`, `Opens.bytes`: The bytes of a column with its salt; the list at
     which the tree is opened, and the opening's length in bytes, from the round's draws.
   `Piece`, `Piece.bytes`, `Piece.fixed`: A piece; its length at given draws; its length if that
     does not depend on the draws.
   `roundPieces`, `SpecX.pieces`: The pieces of one round, and of the chain, in the file's order.
   `placesLoop`, `placesFrom`, `SpecX.places`: Each piece with its first byte and the byte behind
     it.
   `SpecX.endAt`: The byte behind the chain.
   `SpecX.fixedBytes`: The bytes before the first piece whose length depends on the draws.
   `drawsOf`: The draws of each round of a chain that was read.
   `FilePart`, `partsEnd`, `partsFixed`: A file as a list of parts, each a number of bytes outside
     every chain or a chain; the byte behind the last part; the bytes before the first piece whose
     length depends on the draws.
   Sums over the pieces are loops: a chain can have many thousands of pieces.

2. What is checked when the file compiles. Nothing. The tests are in Fmt/Rules8XPiecesKnown.lean
[not in this library]; so here read: not tested in this library.

3. Theorems. None in this file. Fmt/Rules8XPiecesLaws.lean [not in this library] proves, for every
description, every file and every hash function: where the strict reader reads a chain, it ends at
`SpecX.endAt`, taken at the draws that it has read; so here read: not proved in this library.

4. What is not claimed. Nothing is said on what an item means, nor on which oracle message lies
where in a column or in a message. The theorem speaks of the sum of the lengths; that each single
piece lies where `SpecX.places` says is tested alone. This library has a reader that only cuts a
file (Run/ParseLaxX.lean: `cutChainX`, `laxWholeX`). It cuts as it reads and has no list of
lengths. Nothing here is tied to it.

Terms: lean/GLOSSARY.md.

-/
import Fmt.Rules8X

namespace Fmt

/-- Whose tree an opening is of. -/
inductive TreeOf where
  /-- a stored tree: the number, from 0, of the statement's item that holds its root -/
  | stored (item : Nat)
  /-- a tree of the chain's own: its place, from 0, in the order of sending -/
  | own (n : Nat)
  /-- a tree whose root and start come from outside the chain -/
  | given
  deriving DecidableEq, Repr, Inhabited

/-- An opening as a description places it. -/
structure Opens where
  /-- whose tree it is -/
  tree   : TreeOf
  /-- the tree's number (R7.13), which enters every leaf's hash call -/
  number : Nat
  /-- the tree's depth -/
  a      : Nat
  /-- the elements of the base field in a column -/
  W      : Nat
  /-- the bytes of a leaf's salt -/
  salt   : Nat
  /-- its part of the round's draws: from the draw number lo on, count of them -/
  lo     : Nat
  count  : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Opens

/-- a stored tree's opening -/
def ofStored (t : Stored) : Opens :=
  ⟨.stored t.item, t.sh.tree, t.sh.a, t.sh.W, t.salt, t.lo, t.count⟩

/-- The opening of a tree that is not stored: under the plan's salt, at all the round's draws. poss:
how many positions the round draws, by its entry of the plan. -/
def ofOwn (P : Plan) (poss : Nat) (x : Shape × Src) : Opens :=
  ⟨match x.2 with
    | .own n => .own n
    | .given _ _ => .given, x.1.tree, x.1.a, x.1.W, P.salt, 0, poss⟩

/-- the bytes of a column with its salt -/
def column (o : Opens) : Nat := 8 * o.W + o.salt

/-- The list at which the tree is opened: its part of the draws, modulo 2 ^ a, each position once,
increasing. -/
def list (o : Opens) (draws : List Nat) : List Nat :=
  listOf (((draws.drop o.lo).take o.count).map (· % 2 ^ o.a))

/-- R7.8: the columns with their salts, then the given digests. -/
def bytes (o : Opens) (draws : List Nat) : Nat :=
  (o.list draws).length * o.column + 32 * (walkPlaces o.a (o.list draws)).length

end Opens

/-- A piece of a chain in a file. Rounds are counted from 1 (R5.1). -/
inductive Piece where
  /-- the chain's 32 random bytes -/
  | rand
  /-- an item of the round's message -/
  | item (round : Nat) (i : Item)
  /-- the round's nonce, of so many bytes -/
  | nonce (round bytes : Nat)
  /-- the round's listed positions, so many bytes each -/
  | listed (round each : Nat)
  /-- an opening after the round -/
  | opening (round : Nat) (o : Opens)
  deriving DecidableEq, Repr, Inhabited

namespace Piece

/-- The piece's length; draws n are the positions that round n has drawn, as they were drawn. -/
def bytes (draws : Nat → List Nat) : Piece → Nat
  | .rand => 32
  | .item _ i => i.bytes
  | .nonce _ b => b
  | .listed n each => each * (listOf (draws n)).length
  | .opening n o => o.bytes (draws n)

/-- The piece's length, if it does not depend on the draws. -/
def fixed : Piece → Option Nat
  | .rand => some 32
  | .item _ i => some i.bytes
  | .nonce _ b => some b
  | .listed _ _ => none
  | .opening _ _ => none

end Piece

/-- The pieces of round n, in the file's order: the message's items; the nonce, where the round has
work; the list, where the plan lists positions and the round draws some; the stored trees' openings;
the other trees'. -/
def roundPieces (P : Plan) (n : Nat) (r : Round) (ts : List Stored) : List Piece :=
  r.items.map (.item n) ++ (if r.entry.work == 0 then [] else [.nonce n P.nonce]) ++
    (if P.posB == 0 || r.entry.poss == 0 then [] else [.listed n P.posB]) ++
    ts.map (fun t => .opening n (.ofStored t)) ++
    r.opens.map fun x => .opening n (.ofOwn P r.entry.poss x)

/-- The pieces of a chain, in the file's order. -/
def SpecX.pieces (S : SpecX) : List Piece :=
  (match S.base.rand with
    | .inFile => [.rand]
    | _ => []) ++
    (S.base.rounds.zip S.stored).zipIdx.flatMap fun x =>
      roundPieces S.base.plan (x.2 + 1) x.1.1 x.1.2

/-- the loop of `placesFrom` -/
def placesLoop (draws : Nat → List Nat) :
    List Piece → Nat → Array (Piece × Nat × Nat) → Array (Piece × Nat × Nat)
  | [], _, acc => acc
  | p :: l, i, acc => placesLoop draws l (i + p.bytes draws) (acc.push (p, i, i + p.bytes draws))

/-- each piece with its first byte and the byte behind it, from byte i on -/
def placesFrom (draws : Nat → List Nat) (i : Nat) (l : List Piece) : List (Piece × Nat × Nat) :=
  (placesLoop draws l i #[]).toList

/-- The chain's pieces in a file in which the chain begins at byte i. -/
def SpecX.places (S : SpecX) (draws : Nat → List Nat) (i : Nat := 0) : List (Piece × Nat × Nat) :=
  placesFrom draws i S.pieces

/-- The byte behind the chain, if the chain begins at byte i. -/
def SpecX.endAt (S : SpecX) (draws : Nat → List Nat) (i : Nat := 0) : Nat :=
  S.pieces.foldl (fun a p => a + p.bytes draws) i

/-- The bytes of the pieces before the first one whose length depends on the draws. -/
def SpecX.fixedBytes (S : SpecX) : Nat :=
  (S.pieces.takeWhile fun p => p.fixed.isSome).foldl (fun a p => a + p.fixed.getD 0) 0

/-- The draws of each round of a chain that was read; rounds are counted from 1. -/
def drawsOf (o : ChainOut) (n : Nat) : List Nat :=
  if n == 0 then [] else ((o.rounds[n - 1]?).map (·.drawn.poss)).getD []

/-! ## A file of several chains -/

/-- A part of a file: bytes outside every chain, whose number the public data fix, or a chain. -/
inductive FilePart where
  | outside (what : String) (bytes : Nat)
  | chain (what : String) (S : SpecX)

/-- The byte behind the last part, if the first begins at byte i. draws k n are the positions that
round n of the file's chain number k, from 0, has drawn. -/
def partsEnd (draws : Nat → Nat → List Nat) : List FilePart → (k i : Nat) → Nat
  | [], _, i => i
  | .outside _ n :: l, k, i => partsEnd draws l k (i + n)
  | .chain _ S :: l, k, i => partsEnd draws l (k + 1) (S.endAt (draws k) i)

/-- The bytes of a file before the first piece whose length depends on the draws. -/
def partsFixed : List FilePart → Nat
  | [] => 0
  | .outside _ n :: l => n + partsFixed l
  | .chain _ S :: l =>
    if S.pieces.all (·.fixed.isSome) then S.fixedBytes + partsFixed l else S.fixedBytes

end Fmt

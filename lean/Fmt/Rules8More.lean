-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8More.lean: a larger example of this library's own, for cases that the reader of
Fmt/Rules8.lean can meet and the other tests do not exercise.

Sources. The format page (docs/format/FORMAT.md);
this file has not been held against the page as it ships, and may differ from it,
for instance at R7.4, R7.14 and R8.7 of the rules cited below.
No known answer of the page stands here, and
no other program has made these files. Writer and reader are both this library's own. So the tests
show that the two fit and that altered copies are refused, not that either is the page's. No
Mathlib.


1. What the file contains. An example prover that writes a file.
   The example. Field 2; label 9; four rounds; salts of 48 bytes; a nonce of two bytes in the file;
   listed positions of one byte (R8.2); the chain's first tree has the number 3 (R7.13: a chain that
   goes on after another).
    Round 1, elements. The message is two roots, in the order of their trees' numbers (R8.6): tree 3
    (depth 4, two elements a column), tree 4 (depth 2, one element a column: a tree of mask rows
    alone, R7.5).
    Round 2, positions. The message is a word; 4 proof-of-work bits; three positions below 16. After
    the nonce: the list; then three openings: tree 3 at the list; tree 4 at the set of the short
    positions (R7.15); a stored tree (leaves under the number 174, started from a digest that is
    given with its root: R7.4).
    Round 3, positions. The message is an element of the extension field; two positions below 16;
    the list; tree 3 opened a second time, at another list (R7.14).
    Round 4, nothing. The message is an element of the base field.
    And the same chain with its random bytes given, not in the file (case (b) of R4.5).
   In this example the stored tree is opened after the chain's own trees. As this file reads the
   page, it does not say where a stored tree's opening stands; the page as it ships may instead
   ask that stored trees
   be opened first (R8.7). The reader that follows that order is Fmt/Rules8X.lean.
   R7.14 and a hash made to collide. Two openings that end in one root can give one vertex two
   values only at a collision of the hash. The reader is generic in the hash. So the example is also
   run at `weak`, which is the format's hash except that, under the number of a vertex, it does not
   look at the first byte of the left child. There a given digest can be altered without moving the
   root, and the opening by itself is still accepted; the store of met vertices alone refuses. (The
   weak hash is a device of this test. It is no claim about BLAKE2b.)

2. What is checked when the file compiles. 26 tests (#guard) on the descriptions, on these files, on
altered copies and on altered descriptions.

3. Theorems. None.

4. What is not claimed. Anything about the programs' files.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules8

namespace Fmt
namespace Toy8M

abbrev HashId : Type := Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray

/-- The format's hash. -/
def good : HashId := fun n t i s b => formatHash n t i s b

/-- The same, but a vertex does not look at the first byte of its left child. -/
def weak : HashId := fun n t i s b =>
  if n == 166 then formatHash n t i s (zeroBytes 1 ++ b.extract 1 b.size) else formatHash n t i s b

/-- The configuration's digest of this example: the start of every vertex, and of the stored tree's
leaves. -/
def cfg0 : ByteArray := pattern 32 13 5

def upH (h : HashId) : List ByteArray → List ByteArray
  | l :: r :: tl => Id.run (vertexW h cfg0 l r) :: upH h tl
  | _ => []

/-- All values of a tree: the first list is the root alone, the last the leaves. -/
def buildH (h : HashId) : Nat → List ByteArray → List (List ByteArray)
  | 0, leaves => [leaves]
  | d + 1, leaves => buildH h d (upH h leaves) ++ [leaves]

def plan : Plan where
  field := .two
  salt := 48
  nonce := 2
  posB := 1
  samples := 0
  saved := 1
  entries := [
    { name := "more: roots", msg := 64, roots := 2, drawE := 1 },
    { name := "more: first positions", work := 4, msg := 8, poss := 3, logN := 4 },
    { name := "more: second positions", msg := 24, poss := 2, logN := 4 },
    { name := "more: nothing", msg := 8 } ]

def ent (i : Nat) : Entry := plan.entries.getD i default
def params : ByteArray := paramsBytes plan cfg0 []
def statement : ByteArray := items [("more: claim", u64n 11)]
/-- The chain's random bytes: chosen so that, at both hashes, the second opening of tree 3 is given
a left child that the first has met (`common` below). -/
def rnd : ByteArray := pattern 32 5 2
def cfg : ByteArray := cfg0

def shA : Shape := { a := 4, W := 2, tree := 3 }
def shB : Shape := { a := 2, W := 1, tree := 4 }
def shC : Shape := { a := 4, W := 3, stored := true, tree := 0 }
def colA (x : Nat) : List UInt64 := [UInt64.ofNat (10 + x), UInt64.ofNat (20 + 3 * x)]
def colB (x : Nat) : List UInt64 := [UInt64.ofNat (70 + x)]
def colC (x : Nat) : List UInt64 := [UInt64.ofNat (x * x), 1, UInt64.ofNat (5 * x)]
def saltOf (t x : Nat) : ByteArray := pattern 48 (t + 2) (x + 1)

def valuesOf (h : HashId) (sh : Shape) (start : ByteArray) (col : Nat → List UInt64) :
    List (List ByteArray) :=
  buildH h sh.a
    ((List.range (2 ^ sh.a)).map fun x =>
      Id.run (leafW h (leafNo sh.stored) sh.tree sh.a x start (col x) (saltOf sh.tree x)))

def openOf (sh : Shape) (col : Nat → List UInt64) (values : List (List ByteArray)) (xs : List Nat) :
    ByteArray :=
  openingBytes sh.a col (saltOf sh.tree) values xs

def valuesC (h : HashId) : List (List ByteArray) := valuesOf h shC cfg colC

def spec (h : HashId) (rand : Rand) : Spec where
  label := 9
  plan := plan
  params := params
  statement := statement
  rand := rand
  firstTree := 3
  cfg := cfg
  rounds := [
    { entry := ent 0, kind := .elems, items := [.root, .root] },
    { entry := ent 1, kind := .positions, items := [.word],
      opens := [(shA, .own 0), (shB, .own 1), (shC, .given (rootOf (valuesC h)) cfg)] },
    { entry := ent 2, kind := .positions, items := [.e], opens := [(shA, .own 0)] },
    { entry := ent 3, kind := .nothing, items := [.f] } ]

def ask (h : HashId) (c : Chain) (msg : ByteArray) (i : Nat) (k : Kind) (nonce : Nat) :
    Option (Chain × Drawn) :=
  (Id.run (Chain.queryW h c msg k (ent i).work nonce (blocksFor (wordsAtMost (ent i) k)))).map
    fun x => (x.1, drawRound .two (ent i) k (rowOf x.2))

def bytes1 (l : List Nat) : ByteArray := ⟨(l.map UInt8.ofNat).toArray⟩

/-- What the example prover makes: the pieces of the file, and the two lists. -/
structure Made where
  head  : ByteArray
  list2 : List Nat
  open2 : ByteArray
  mid   : ByteArray
  list3 : List Nat
  open3 : ByteArray
  tail  : ByteArray

def Made.file (x : Made) : ByteArray :=
  x.head ++ bytes1 x.list2 ++ x.open2 ++ x.mid ++ bytes1 x.list3 ++ x.open3 ++ x.tail

/-- The example prover. -/
def make (h : HashId) (inFile : Bool) : Option Made := do
  let hd ← Id.run (startChainW h 9 (Id.run (paramsDigestW h params)) statement (some rnd))
  let run ← hd.run
  let vA := valuesOf h shA run colA
  let vB := valuesOf h shB run colB
  let msg1 := rootOf vA ++ rootOf vB
  let (c1, _) ← ask h ⟨9, hd.rho0, 0⟩ msg1 0 .elems 0
  let msg2 := u64n 5
  let nonce ← (List.range 4096).find? fun n => (ask h c1 msg2 1 .positions n).isSome
  let (c2, d2) ← ask h c1 msg2 1 .positions nonce
  let l2 := listOf d2.poss
  let msg3 := ext (1, 2, 3)
  let (_, d3) ← ask h c2 msg3 2 .positions 0
  let l3 := listOf d3.poss
  pure {
    head := (if inFile then rnd else ByteArray.empty) ++ msg1 ++ msg2 ++ (u64n nonce).extract 0 2
    list2 := l2
    open2 := openOf shA colA vA l2 ++
      openOf shB colB vB (listOf (l2.map (· % 4))) ++ openOf shC colC (valuesC h) l2
    mid := msg3
    list3 := l3
    open3 := openOf shA colA vA l3
    tail := u64n 8 }

def read (h : HashId) (rand : Rand) (b : ByteArray) : Option ChainOut :=
  Id.run (wholeChain h (spec h rand) b)

/-- The honest file. -/
def honest (h : HashId) : ByteArray := ((make h true).map Made.file).getD ByteArray.empty

/-- The honest file with one piece replaced. -/
def withPiece (h : HashId) (f : Made → Made) : ByteArray :=
  ((make h true).map fun x => (f x).file).getD ByteArray.empty

/-- In the second opening of tree 3: the number, among the given digests, of one that is a left
child and that the first opening has met too. -/
def common (x : Made) : Option Nat :=
  let met := (walkPlaces 4 x.list2) ++
    (List.range 5).flatMap fun d => (x.list2.map fun p => (d, p / 2 ^ (4 - d)))
  (walkPlaces 4 x.list3).findIdx? fun v => v.2 % 2 == 0 && met.contains v

/-- The byte, in the second opening, at which given digest number j begins. -/
def givenAt (x : Made) (j : Nat) : Nat := x.list3.length * (16 + 48) + 32 * j

/-- The honest file with the first byte of that given digest altered. -/
def twoValues (h : HashId) : Option ByteArray :=
  (make h true).bind fun x =>
    (common x).map fun j => ({ x with open3 := flipAt x.open3 (givenAt x j) } : Made).file

end Toy8M

open Toy8M in
#guard (spec good .inFile).ok && (spec good (.given rnd)).ok && (spec weak .inFile).ok
open Toy8M in
#guard (make good true).isSome && (make weak true).isSome

-- The honest file is read; the reader's two lists are the prover's; the three openings of round 2
-- stand at the lists that are meant
open Toy8M in
#guard (read good .inFile (honest good)).isSome
open Toy8M in
#guard ((read good .inFile (honest good)).map fun o => (o.rounds.toList.map (·.list))) = (make good true).map fun x => [[], x.list2, x.list3, []]
open Toy8M in
#guard ((read good .inFile (honest good)).bind fun o => o.rounds[1]?.map fun r => r.opens.map fun x => (x.1.tree, x.1.stored, x.2.1)) =
  (make good true).map fun x => [(3, false, x.list2), (4, false, listOf (x.list2.map (· % 4))), (0, true, x.list2)]
open Toy8M in
#guard ((read good .inFile (honest good)).bind fun o => o.rounds[1]?.map fun r => r.opens.map fun x => x.2.2.cols) =
  (make good true).map fun x => [x.list2.map colA, (listOf (x.list2.map (· % 4))).map colB, x.list2.map colC]
-- three roots were met: tree 3's (twice), tree 4's, the stored tree's: three entries in the store
open Toy8M in
#guard ((read good .inFile (honest good)).map fun o => o.seen.length) = some 3

-- CASE (b): the random bytes given: the same file without its first 32 bytes; each form is refused under the other case
open Toy8M in
#guard (read good (.given rnd) (((make good false).map Made.file).getD ByteArray.empty)).isSome
open Toy8M in
#guard ((make good false).map Made.file) = some ((honest good).extract 32 (honest good).size)
open Toy8M in
#guard (read good (.given rnd) (honest good)).isNone && (read good .inFile ((honest good).extract 32 (honest good).size)).isNone

-- Listed positions: another list, a list in another order, a list left out: refused
open Toy8M in
#guard (read good .inFile (withPiece good fun x => { x with list2 := x.list2.map (· + 1) })).isNone
open Toy8M in
#guard ((make good true).map fun x => decide (2 ≤ x.list2.length)) = some true && (read good .inFile (withPiece good fun x => { x with list2 := x.list2.reverse })).isNone
open Toy8M in
#guard (read good .inFile (withPiece good fun x => { x with list2 := [] })).isNone

-- Openings: a byte altered in tree 3's first opening, in the stored tree's and in tree 3's second;
-- an own tree under another number
open Toy8M in
#guard (read good .inFile (withPiece good fun x => { x with open2 := flipAt x.open2 0 })).isNone
open Toy8M in
#guard (read good .inFile (withPiece good fun x => { x with open2 := flipAt x.open2 (x.open2.size - 1) })).isNone
open Toy8M in
#guard (read good .inFile (withPiece good fun x => { x with open3 := flipAt x.open3 20 })).isNone
open Toy8M in
#guard !({ spec good .inFile with firstTree := 0 } : Spec).ok
-- the shapes of the chain's own trees, looked up by the roots' places; a tree opened under two shapes is not in order
open Toy8M in
#guard (spec good .inFile).shapeOf 0 = some shA && (spec good .inFile).shapeOf 1 = some shB && (spec good .inFile).shapeOf 2 = none
open Toy8M in
#guard !({ spec good .inFile with rounds := (spec good .inFile).rounds.map fun r => if r.entry.name == "more: second positions" then { r with opens := [({ shA with W := 3 }, .own 0)] } else r } : Spec).ok

-- the same file under another configuration's digest: refused (the parameters hold it, and every vertex starts from it)
open Toy8M in
#guard (Id.run (wholeChain good { spec good .inFile with cfg := zero32 } (honest good))).isNone
-- The vertices alone: the fold itself, from the honest chain's head, at the example's
-- configuration's digest and at another: the chain's values, draws and leaves are the same, only
-- the vertices' start differs: read; refused
open Toy8M in
#guard ((Id.run (startChainW good 9 (Id.run (paramsDigestW good params)) statement (some rnd))).map fun hd =>
  ((Id.run (foldRounds good cfg plan hd.run (honest good) (spec good .inFile).rounds ⟨32, ⟨9, hd.rho0, 0⟩, #[], [], #[]⟩)).isSome,
   (Id.run (foldRounds good zero32 plan hd.run (honest good) (spec good .inFile).rounds ⟨32, ⟨9, hd.rho0, 0⟩, #[], [], #[]⟩)).isSome)) = some (true, false)
-- R8.7: a chain's own trees are opened in the order of their numbers: the other order is not in order
open Toy8M in
#guard !({ spec good .inFile with rounds := (spec good .inFile).rounds.map fun r => if r.entry.name == "more: first positions" then { r with opens := [(shB, .own 1), (shA, .own 0)] } else r } : Spec).ok

-- R7.14. At the format's hash, with a given digest altered: refused
open Toy8M in
#guard ((twoValues good).map fun b => (read good .inFile b).isNone) = some true
-- at the hash made to collide: the honest file is read
open Toy8M in
#guard (read weak .inFile (honest weak)).isSome
-- the altered second opening by itself is accepted and ends in the same root
open Toy8M in
#guard ((make weak true).bind fun x => (common x).bind fun j => (Id.run (startChainW weak 9 (Id.run (paramsDigestW weak params)) statement (some rnd))).bind fun hd => hd.run.bind fun run =>
  (Id.run (readOpeningW weak cfg .two 48 shA run x.list3 (flipAt x.open3 (givenAt x j)) 0)).map fun o => o.root == rootOf (valuesOf weak shA run colA)) = some true
-- and the file is refused: one vertex has two values under one root
open Toy8M in
#guard ((twoValues weak).map fun b => (read weak .inFile b).isNone) = some true

end Fmt

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryLayout.lean: the layout of an entry file as one value, computed from the public
files.

An entry file (the format's leaf file) holds a further stored table's root and stored answers and
the chain of the link. What a reader must know before it sees such a file is public: how many
answers follow the root; the chain's rounds, each with the items of its message, its bits of work
and its draws; which trees are opened after which round, how deep and how wide they are, and at
which part of the draws; which oracle message lies in which places of a column. This file says it
in two steps, and each of these numbers is read off one value. No number of an example is written
here.

Step 1, without a hash: `entryShape`. By the format page (docs/format/FORMAT.md, section 18, a part
of R4.9) what is fixed before the hash function is chosen is the text of the public files, and
whatever follows from that text without a hash. The shape follows from the first 32 lines of the
parameter file alone: they are read (`readLines`), the table and the link are sized and the chain's
rounds planned (`entrySized`), and the link's block is run dry (a run on zeros that only notes the
rounds), at two keys of zeros of the sizes that the tables' shape says. The tables themselves are
no argument: roots, answers and seeds are no layout.

Step 2, with the hash's answer as an argument: `EntryShape.params`, `EntryShape.linkAt`,
`EntryShape.spec` take the digest c of the public files. The chain's parameter bytes are spelled
from the shape's plan, c and the shape's items. The plan whose words are hashed is the plan whose
rounds the description runs: a shape is returned only if the dry run's rounds are, entry for entry,
the plan's. `entryLayout` puts the two steps together at the digest of three given files.

THIS IS NO ADMISSION OF THE PUBLIC FILES. A shape is returned for public files that the programs
refuse. Asked here: the tests of the parameter file's first 32 lines (`readLines`); that the table's
and the link's sizes exist; that every round of the entry's plan holds at the file's own target;
the public tests of the link's block; the tests of `EntryShape.ok`. NOT asked, though the C++
verifier and this program ask it before they say yes (docs/format/08-parameters.md, 8.3 and 8.4,
item 23):
 - that the file's target is at least the bits that a caller asks for. (This program asks it in
   its stages; its routine `Model.Verify.planned`, which makes the seven chains' parameter bytes,
   does not ask it either.)
 - that no value of work is above 32, that there are at most 256 slots, that the shared point has 1
   to 20 coordinates;
 - anything of the parameter file's later lines, of the layout file or of the scale file, which are
   hashed and never parsed here;
 - that a key's and a proof's sizes exist; the conditions of OnBytes/Params/Gate.lean.
That, where the program's `configure` returns a value, its parameter bytes of the entry's chain are
`entryBytes` is not shown in this library.

What is written here anew, and what holds it to the program's own text.
 - The parts of the file before its chain (`EntryShape.parts`, `EntryShape.before`: R13.1, R13.3).
   That their sum is what the program's reader takes is not shown in this library; their order and
   cut are
   held by nothing.
 - The order of the tables' six words (`shapeWords`: R4.10). `EntryShape.ok` compares them with the
   first six words of the item "the link" as it is spelled.
 - The four parts of the last message (`baseParts`: R12.9): the numbers, in the order, in which
   `baseVerify` (OnBytes/Iop/Prox.lean) receives them where the last stage has one mask row.
   `EntryShape.ok` compares their sum with the
   number of the message's items; order and cut are held by nothing.
 - The places of an oracle message in a column (`mainSkip`, `maskSkip`): the two expressions in the
   text of `Blk.symbolsOf` (OnBytes/Iop/Ground.lean), under names. OnBytes/Slice/BlkOpenN.lean has
   them under the same two names, on a tree, in a file of theorems. That the three agree is not
   shown in this library.
 - Seven definitions repeat one that lies in a file of theorems or inside a function's text:
   `chainDryWith`, `sizeKey`, `entryStart`, `EntryShape.answers`, `EntryShape.spec`,
   `EntryShape.blocks`, `entryBytes`. That each is its original is not shown in this library; of
   `chainDryWith` two fields have no original: those that it keeps beside the rounds and the block's
   value.
Not rendered: the eight bytes of the head themselves; the order of the stored answers (by row, and
within a row by answer); the rows in a stored table's column; what each item of a message means.

Main definitions: `ConfigurationFiles`, `ConfigurationFiles.digest`; `ChainDry`, `chainDryWith`, `chainDry`,
`sizeKey`; `mainSkip`, `maskSkip`, `Lane`, `Lane.count`, `lanesOfOracle`, `lanesOf`, `lanesFill`;
`EntryShape` with `table`, `shapeWords`, `answers`, `items`, `params`, `linkAt`, `spec`,
`blankTable`, `blankSpec`, `parts`, `pieces`, `before`, `fileBytes`, `fixedBytes`, `blocks`,
`baseParts`, `ok`; `entryStart`, `entryShapeOf`, `entryShapeOfLines`, `entryShape`; `EntryLayout`
with `link`, `spec`; `entryLayout`, `entryBytes`.
What is not claimed: no theorem is stated here, and neither the laws on these definitions nor the
tests of them are in this library.

-/
import OnBytes.Entry.File
import OnBytes.Params.Configure
import Fmt.ParamsReadLaws
import Fmt.Rules8XPieces

set_option autoImplicit false

namespace OnBytes.Params

/-- The three public files of a configuration, in the order in which the digest takes them
(R4.9). -/
structure ConfigurationFiles where
  /-- the parameter file -/
  policy : ByteArray
  /-- the layout file -/
  layout : ByteArray
  /-- the scale file -/
  scales : ByteArray

/-- The configuration's digest (R4.9), at the format's hash. -/
def ConfigurationFiles.digest (x : ConfigurationFiles) : ByteArray :=
  configurationDigest [x.policy, x.layout, x.scales]

/-! ## What a dry run leaves -/

/-- What the dry run of a chain's block leaves. -/
structure ChainDry where
  /-- the rounds of the chain's description, each with the stored trees that it opens -/
  rounds : Rounds
  /-- the shapes of the oracle messages, in the order of sending -/
  oracles : Array OracleShape
  /-- in which tree each oracle message lies, and at which place among the tree's parts -/
  book : TreeBook

/-- The dry run of a block, with what it leaves and the block's value. It fails where `Blk.dryRun`
fails: it has the text of `Blk.dryRunNamed` and keeps two more fields of the context. -/
def chainDryWith {α : Type} (b : Blk α) (s : Start) : Option (ChainDry × α) :=
  match b.runNamed s true [] [] with
  | .error _ => none
  | .ok (a, c) =>
    if c.ch.entries.isEmpty && c.ch.items.isEmpty && c.ch.settled then
      some (⟨c.ch.noted.toList.map fun n => (⟨n.entry, n.kind, n.items, n.opens⟩, n.stored),
        c.st.oracles.map (·.shape), c.book⟩, a)
    else none

/-- The same without the block's value. -/
def chainDry {α : Type} (b : Blk α) (s : Start) : Option ChainDry := (chainDryWith b s).map (·.1)

/-- A table's key that has the sizes which the shape s asks for and the content of no table: a
record of zeros, and seeds with points of zeros and the factor one. (The same value as `zeroKey` of
OnBytes/Params/EntryRoundsRecord.lean, which lies in a file of theorems.) -/
def sizeKey (s : IndexShape) (item : Nat) : TableKey :=
  { item := item, record := Array.replicate (s.rows * s.answers) zeroE,
    seeds := List.replicate s.answers ⟨List.replicate s.cubeBits zeroE, oneE⟩ }

/-! ## Which oracle message lies where in a column -/

/-- The word of a column at which the main symbols of the tree's part number p begin. -/
def mainSkip (t : TreeShape) (p : Nat) : Nat := (t.mainSymbols.extract 0 p).foldl (· + ·) 0

/-- The word of a column at which the mask symbols of the tree's part number p begin (R7.1: all main
symbols, then all mask symbols). -/
def maskSkip (t : TreeShape) (p : Nat) : Nat :=
  t.mainWidth + (t.maskSymbols.extract 0 p).foldl (· + ·) 0

/-- The places of one oracle message's rows of one kind in a column of its tree. -/
structure Lane where
  /-- the tree's place in the book of trees -/
  tree : Nat
  /-- the oracle message's number, in the order of sending -/
  oracle : Nat
  /-- main rows or mask rows -/
  part : Part
  /-- its rows of this kind -/
  rows : Nat
  /-- the elements of the base field in a symbol: 1 or 3 -/
  deg : Nat
  /-- the first of its elements in a column, from 0; row number r begins at first + deg * r -/
  first : Nat
  /-- the logarithm of the rows' length: a row is read at the position modulo 2 ^ logN (R7.2) -/
  logN : Nat
  deriving DecidableEq, Repr, Inhabited

/-- how many elements of a column are the lane's -/
def Lane.count (l : Lane) : Nat := l.rows * l.deg

/-- The lanes of the oracle message number o: its main rows', if it has any, then its mask rows'. -/
def lanesOfOracle (d : ChainDry) (o : Nat) : List Lane :=
  match d.oracles[o]?, d.book.place[o]? with
  | some x, some (t, p) =>
    match d.book.trees[t]? with
    | some T =>
      (if x.mainRows == 0 then []
        else [⟨t, o, .main, x.mainRows, x.mainDeg, mainSkip T.shape p, T.shape.logN⟩]) ++
        (if x.maskRows == 0 then []
          else [⟨t, o, .mask, x.maskRows, 3, maskSkip T.shape p, T.shape.logNzk⟩])
    | none => []
  | _, _ => []

/-- All lanes of a chain's oracle messages, message by message. -/
def lanesOf (d : ChainDry) : List Lane := (List.range d.oracles.size).flatMap (lanesOfOracle d)

/-- True if the lanes of every tree of the book fill its columns: by their first elements they lie
one behind the other from element 0 on, without a gap, up to the width that the tree's shape says.
-/
def lanesFill (d : ChainDry) : Bool :=
  d.book.trees.toList.zipIdx.all fun T =>
    let mine := ((lanesOf d).filter (·.tree == T.2)).map fun l => (l.first, l.count)
    let sorted := mine.toArray.qsort (fun a b => a.1 < b.1) |>.toList
    (sorted.foldl
      (fun (s : Option Nat) x => s.bind fun e => if x.1 == e then some (e + x.2) else none)
      (some 0)) == some (T.1.shape.mainWidth + T.1.shape.maskWidth)

/-! ## The shape of an entry file: what follows without a hash -/

/-- The shape of an entry file. -/
structure EntryShape where
  /-- the plan of the link's chain -/
  plan : Fmt.Plan
  /-- the codes of the chain's proximity test -/
  codes : Codes
  /-- the item "the link" -/
  link : LinkShape
  /-- what the dry run of the link's block leaves -/
  dry : ChainDry

namespace EntryShape

/-- The one shape of the first table and of all further tables. -/
def table (E : EntryShape) : IndexShape := E.link.table

/-- The tables' shape as R4.10's six words: the logarithm of the code's length; the entries of a
row's message; of its tail; the logarithm of the number of rows; the stored answers of a row; the
bytes of a leaf's salt. -/
def shapeWords (E : EntryShape) : List Nat :=
  [E.table.code.logN, E.table.code.ell, E.table.code.r, E.table.v, E.table.answers,
    E.table.saltBytes]

/-- How many stored answers, elements of the extension field, follow a table's root in a file
(R13.3): one for each row and seed. -/
def answers (E : EntryShape) : Nat := E.table.rows * E.table.answers

/-- The two parameter items after the digest of the public files (R13.5). -/
def items (E : EntryShape) : List (String × ByteArray) :=
  [("codes", spellCodes E.codes), ("the link", spellLink E.link)]

/-- The chain's parameter bytes at the digest c of the public files (R4.3). -/
def params (E : EntryShape) (c : ByteArray) : ByteArray := Fmt.paramsBytes E.plan c E.items

/-- What these parameter bytes hold as those of a link's chain. -/
def linkAt (E : EntryShape) (c : ByteArray) : Link :=
  ⟨⟨E.params c, E.plan, c, E.items⟩, E.codes, E.link⟩

/-- The description of the chain at the digest c and a statement. -/
def spec (E : EntryShape) (c statement : ByteArray) : Fmt.SpecX :=
  { base := { label := labelLink, plan := E.plan, params := E.params c, statement := statement,
              rand := .inFile, firstTree := 0, cfg := c, rounds := E.dry.rounds.map (·.1) },
    stored := E.dry.rounds.map (·.2) }

/-- A table of this shape and of no content: a root of 32 zero bytes, answers of zeros. -/
def blankTable (E : EntryShape) : TableName := ⟨Fmt.zero32, List.replicate E.answers zeroE⟩

/-- The description at a digest of zeros and two blank tables. Its statement has the length and the
form of every statement of this shape. -/
def blankSpec (E : EntryShape) : Fmt.SpecX :=
  E.spec Fmt.zero32 (Link.statement E.blankTable E.blankTable)

/-- The parts of an entry file, in the file's order (R13.1, R13.3): the four bytes that say what the
file is, the four of the version, the further table's root, its stored answers, the link's chain. -/
def parts (E : EntryShape) : List Fmt.FilePart :=
  [.outside "head: the kind" 4, .outside "head: the version" 4,
    .outside "the further table's root" 32,
    .outside "the further table's stored answers" (24 * E.answers), .chain "the link" E.blankSpec]

/-- The pieces of the chain, in the file's order. -/
def pieces (E : EntryShape) : List Fmt.Piece := E.blankSpec.pieces

/-- The bytes of an entry file before its chain. -/
def before (E : EntryShape) : Nat := 4 + 4 + 32 + 24 * E.answers

/-- The length of the file; draws n are the positions that round n has drawn (R13.3: the file ends
with the chain). -/
def fileBytes (E : EntryShape) (draws : Nat → List Nat) : Nat :=
  Fmt.partsEnd (fun _ => draws) E.parts 0 0

/-- The bytes of the file before the first piece whose length depends on the draws: so far a file
can be cut by the public files alone. -/
def fixedBytes (E : EntryShape) : Nat := Fmt.partsFixed E.parts

/-- The greatest number of blocks of 32 bytes that a round's draws can need: R6.11's count of words,
four words a block. -/
def blocks (E : EntryShape) : Nat :=
  E.dry.rounds.foldl (fun a r => max a (Fmt.blocksFor (Fmt.wordsAtMost r.1.entry r.1.kind))) 0

/-- The four parts of the message of the round BASE, in elements of the extension field (R12.9): the
entries of a message under the last stage's base code, then under its mask code; the entries of a
tail under the base code, then under the mask code. -/
def baseParts (E : EntryShape) : List Nat :=
  match E.link.later.getLast? with
  | some s =>
    let c := E.codes.base.getD s.code default
    let z := E.codes.mask.getD s.maskCode default
    [c.ell, z.ell, c.r, z.r]
  | none => []

/-- The tests under which a shape is returned, beside the bounds that `entryShapeOf` asks first. The
description at blank content is in order: among much else, the rounds are the plan's, entry for
entry. The plan has one entry RECORD, with R13.15's words, and it is the first. What is spelled can
be read back: plan, names, items, codes, the
link. The six words of the tables' shape are the first six of the item "the link". The stored trees
have the tables' depth, rows and salt. The lanes fill the trees' columns. The last message has as
many items, all elements of the extension field, as the four numbers of `baseParts` add up to. -/
def ok (E : EntryShape) : Bool :=
  specXOk E.blankSpec &&
    (E.plan.entries.filter (·.name == Fmt.recordName) ==
      [{ name := Fmt.recordName, drawE := E.table.answers * (E.table.cubeBits + 1),
         drawNZ := E.table.answers }]) &&
    ((E.plan.entries.head?.map (·.name)) == some Fmt.recordName) &&
    E.plan.fit && (E.plan.ok && namesKnown E.plan) &&
    (E.items.all fun x => Fmt.nameFit x.1 && decide (x.2.size < 2 ^ 64)) &&
    readCodes (spellCodes E.codes) == some E.codes && readLink (spellLink E.link) == some E.link &&
    ((Fmt.rdMany Fmt.rdWord 6 (spellLink E.link) 0).map (·.1)) ==
      some (E.shapeWords.map UInt64.ofNat) &&
    (E.dry.rounds.all fun r => r.2.all fun t =>
      t.sh.a == E.table.code.logN && t.sh.W == E.table.rows && t.salt == E.table.saltBytes) &&
    lanesFill E.dry &&
    ((E.dry.rounds.getLast?.map fun r => r.1.items) ==
      some (List.replicate E.baseParts.sum .e))

end EntryShape

/-- What the link's block starts from: the plan's rounds and answers to a sample, the codes, no
tree. (`Entry.start` at these values.) -/
def entryStart (plan : Fmt.Plan) (codes : Codes) : Start :=
  { entries := plan.rounds, samples := plan.samples, st := { codes := codes } }

/-- The shape from a plan, codes and the item "the link". Nothing if the tables' numbers are beyond
the parser's bounds, if the dry run fails, or if a test of `EntryShape.ok` fails. -/
def entryShapeOf (plan : Fmt.Plan) (codes : Codes) (link : LinkShape) : Option EntryShape :=
  if decide (link.table.v ≤ 20) && decide (link.table.answers ≤ 4) then
    (chainDry (linkVerify link (sizeKey link.table 0) (sizeKey link.table 1))
      (entryStart plan codes)).bind fun d =>
        let E : EntryShape := ⟨plan, codes, link, d⟩
        if E.ok then some E else none
  else none

/-- The shape from what the parameter file's first 32 lines say. -/
def entryShapeOfLines (l : Lines) : Except String EntryShape := do
  let (x, codes, p) ← entrySized l
  match entryShapeOf p.plan codes x.shape with
  | some E => pure E
  | none => throw "entry-shape"

/-- **The shape of an entry file, from the parameter file.** No hash is called. It is no admission
of the public files: the head of this file says what is not asked, the caller's bits first. -/
def entryShape (policy : ByteArray) : Except String EntryShape := do
  let l ← readLines policy
  entryShapeOfLines l.1

/-! ## The layout at three public files -/

/-- The layout of an entry file: its shape, and the digest of the public files. -/
structure EntryLayout where
  /-- what follows from the parameter file without a hash -/
  shape : EntryShape
  /-- the digest of the public files -/
  cfg : ByteArray

/-- What the chain's parameter bytes hold. -/
def EntryLayout.link (L : EntryLayout) : Link := L.shape.linkAt L.cfg

/-- The description of the chain at a statement. -/
def EntryLayout.spec (L : EntryLayout) (statement : ByteArray) : Fmt.SpecX :=
  L.shape.spec L.cfg statement

/-- **The layout of an entry file, from the three public files**, at the format's hash. It is no
admission of the public files. -/
def entryLayout (x : ConfigurationFiles) : Except String EntryLayout := do
  pure ⟨← entryShape x.policy, x.digest⟩

/-- The parameter bytes of an entry file's chain, or the words of the step that refuses. -/
def entryBytes (x : ConfigurationFiles) : Except String ByteArray := do
  let l ← readLines x.policy
  entryParams l.1 x.digest

end OnBytes.Params

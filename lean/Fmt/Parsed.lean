-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Parsed.lean: the functions on the declared structure (Decl/Declared.lean) and on the records of
what stands in a file (Fmt/ParsedTypes.lean): a chain's description for this library's readers, the
tests on the declared structure itself, a statement's bytes, the writers that give a file's bytes
back, the tests of form, and the step from what a reader of this library holds to a parsed record.
Definitions only.

A parsed record holds what stands in a file and nothing else. The writers are here so that a run can
test that a converter has lost no byte and taken none twice: the record, written back, is the file.
The tests of form hold what a writer cannot see: the kinds of the items, the number of rounds, the
widths, the canonical forms. A function on a chain takes what it reads (the plan, the declared
chain); a function on a file takes the declared structure D. The configuration's digest is a value
of the hash and no part of D: a function that needs it takes it as the argument cfg.

Sources. The format page that ships: docs/format/FORMAT.md, docs/format/09-key-and-leaf-files.md
and docs/format/10-proof-file.md; rule numbers are that page's. No Mathlib, neither directly nor
through the imports.

1. What the file contains.
   The public side.
    `Declared.cfgW`, `Declared.cfg`: the configuration's digest (R4.9), from the public files' text
      and a hash; at the format's own hash.
    `TableShape.count`, `TableShape.name` (R4.10), `TableShape.words`, `TableShape.ok`.
    `Declared.params`: a chain's parameter bytes (R4.3), from its plan (`Declared.plan`,
      Decl/Declared.lean), the configuration's digest and its further items.
    `itemValue`; `TreeSource.src`, `DeclaredRound.round`, `Declared.spec`: the description of a chain for
      the readers of Fmt/Rules8X.lean, from the declared chain, the digest, the statement's bytes
      and, for trees that are taken over, what the file's earlier chains have sent. In case (b) of
      R4.5 the 32 bytes are read off the statement's item: they have no second source.
    `Declared.settingOk`, `Declared.chainOk`: the tests that all chains share.
    `ChainDecl.roots`, `ChainDecl.itemWords`, `ChainDecl.takenOk`, `Declared.chainsFormOk`,
    `Declared.keyFormOk`, `Declared.proofFormOk`: the tests on a key file's and a proof file's
      chains that need no hash and no statement.
    `Declared.chainsOf`, `Declared.shapeOf`: the shape of a tree, by file, chain and number.
    `storedShapeOk`, `entryShapeOk`, `Declared.entryFormOk`, `Declared.entryFormOkOwn`: tests on the
      declared structure as far as an entry file goes, at a statement. Which pairs of tellings they
      compare is listed at `Declared.entryFormOk`; which they do not: 4, below.
   The statement.
    `EntryStm.bytes` (R13.5, R4.6), `TableSt.item`, `sharedStm` (R13.5, R14.9), `ProofStm.bytes`
    (R14.3), `UserStm.reply` (R15.7), `idString` (R4.11), `TableSt.ok`, `EntryStm.ok`,
    `EntryParsed.stm`, `ProofParsed.copyFits` (R14.2).
   The writers.
    `tagKey`, `tagEntry`, `tagProof`, `headOf` (R13.1, R14.2); `TableSt.bytes`; `OpenParsed.bytes`
    (R7.8); `RoundParsed.bytes` (R8.7); `ChainParsed.bytes` (R8.1); `SlotParsed.bytes`;
    `KeyParsed.bytesAt`, `KeyParsed.bytes` (R13.2); `EntryParsed.bytes` (R13.3);
    `ProofParsed.bytesAt`, `ProofParsed.bytes` (R14.1). A writer reads of each chain's plan two
    widths, the bytes of a nonce and of a listed position, and nothing else of what is public.
   The form.
    `ItemValue.fitsItem`, `OpenParsed.fits`, `wantOpens`, `RoundParsed.fits`, `ChainParsed.fits`,
    `SlotParsed.fits`, `KeyParsed.fits`, `EntryParsed.fits`, `ProofParsed.fits`: kinds, widths,
    canonical forms, and the numbers that the declared structure fixes. They need no draw.
   The numbers that hang on the draws.
    `OpenParsed.counts`, `RoundParsed.counts`, `ChainParsed.counts`.
   From a reader of this library.
    `OpenParsed.of`, `RoundParsed.of`, `ChainParsed.of`: what a reader holds of a chain (`ChainOut`,
    Fmt/Rules8.lean), with all that is derived dropped. They return nothing rather than cut a list
    short.

2. What is checked when the file compiles. Only the types. Tests: Fmt/ParsedKnown.lean.

3. Theorems. None.

4. What is not claimed.
   No position stands in a parsed record. So `fits` cannot say that an opening has the right number
   of columns or of given digests, or that the listed positions are the right ones: all three follow
   from the draws (R7.8, R7.9, R8.2). It bounds the first by the number of draws. It does not test
   all that could be tested without a draw: no clause reads a tree's depth, so not R7.9's bound on
   the number of given digests. It is not so that two records which fit one D and are written to the
   same bytes are equal: where a column with its salt has 72 bytes, four columns more and nine given
   digests fewer have one length. By the format page (7.1) a file cannot be cut without the draws.
   `fits` does not test D. A record can fit a D that no public files give.
   The tests on D in this file do not compare everything that D tells twice. The further items
   (`others`) are hashed as they stand; the widths and depths of a chain's own trees, the numbers of
   its rounds and the rows that a round batches, which a reader follows, stand in the declared
   rounds. Here, of "the link" the first eight words are compared, of "the test on the table" the
   first six. What arithmetic on an item's words can hold beside (rows of `BAT`, three widths, the
   range of `LINK`'s and `LOC`'s positions, numbers of draws) is not tested in this file;
   this file does not gather all tests. What
   hangs on "codes" and on the lists of stages follows from the public files by the planner, and can
   be compared only where the planner lies.
   No reader from bytes is here: cutting needs the hash (Fmt/Rules8X.lean; Run/ParseLaxX.lean). A
   reader of a chain that is told the numbers, and its laws: Fmt/ParsedRead.lean,
   Fmt/ParsedReadLaws.lean.
   `fits` is a converter's test of itself. No verifier calls it, and nothing on soundness follows
   from it. This file does not say who tests a file's head before a verdict.
   `Declared.keyFormOk` and `Declared.proofFormOk` have some of the tests that need no hash and no
   statement. Left out: what R14.3 asks of a proof's items (one notice; the segments' first words;
   as many identifiers and layout entries as segments; at least one pending row), which the port
   tests (OnBytes/Params/Chains.lean); the setting's answers to a sample against the item "request's
   shape" (R12.14); that trees which are taken over stand by increasing place (R8.7). Of the
   format's own conditions on each chain's description (`SpecX.ok`) two are among them, which read
   no statement: the chain has a round, and every round's entry has its kind's draws and no others
   (`Declared.chainOk`). The others are not; several of these read a statement, and the later
   chains' statements hold seals and a binding tree's root. Both tests have been tried in this
   directory on made-up chains alone.
   Values of one run that are told twice, and that nothing here compares but the first: a proof
   file's number of the table and the statement's (`ProofParsed.copyFits`); `ProofStm.reply` and
   `UserStm.reply`, and the item of the round REPLY; `ProofStm.table`, `EntryStm.further` and
   `EntryParsed.table`; `EntryStm.first` and `KeyParsed.table`; `UserStm.id` and the hash of
   `idString`; `ProofStm.words` and `UserStm.request` (a test on these two: `ProofStm.wordsOk`,
   Fmt/RequestItem.lean). A verifier compares them (R14.8; R14.3; R13.5; 13.5).
   `ProofParsed.fits` has been tried on no file; `KeyParsed.fits` on the programs' toy key file.
   The port has the statement, the commitment ID and a file's head in its own types:
   `Params.Link.statement` (OnBytes/Params/Chains.lean), `Key.commitmentId`
   (OnBytes/Key/Table.lean), `Proof.FileKind`, `Proof.readHead` (OnBytes/Proof/Head.lean). At
   `P.s == 0` (`M3.sizesOK`, Fmt/M3Dec.lean): `M3.stmOf`
   (Fmt/M3Plan.lean); `M3.headKey`, `M3.headEntry` (Fmt/M3Entry.lean).

Terms: lean/GLOSSARY.md.

-/
import Fmt.ParsedTypes
import Fmt.FieldE
import Fmt.ParamsReadLaws
import Fmt.Rules8X
import Fmt.Rules8Own

namespace Fmt

/-! ## The public side -/

/-- The configuration's digest (R4.9) at a hash h: it is computed from the public files' text once
the hash is there, and is fixed by no field. -/
def Declared.cfgW {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (D : Declared) : m ByteArray :=
  configDigestW h D.files

/-- the same at the format's own hash -/
def Declared.cfg (D : Declared) : ByteArray := configDigest D.files

/-- how many stored answers a table of this shape has -/
def TableShape.count (s : TableShape) : Nat := 2 ^ s.logRows * s.answers

/-- the six words, in the page's order -/
def TableShape.words (s : TableShape) : List Nat :=
  [s.a, s.message, s.tail, s.logRows, s.answers, s.saltBytes]

/-- The ranges that the format page gives for a tables' shape without a planner: its first three
words are a code (R12.1: a from 1 to 60; at least one entry of a message; message and tail together
at most 2 ^ a and at most 2 ^ 32 entries); at most 2 ^ 40 rows; at least one answer; the pads leave a
plain entry (R13.8: a shape with 3 s >= l is rejected); the salt's length is one that a leaf can have (R7.3). And a
statement that names two tables of this shape, the longest that a key file's or an entry file's
chain has (`EntryStm.bytes`: 160 bytes and 48 for each answer of a table), has fewer than 2 ^ 64
bytes: a statement's length is one word in the hash of the chain's first value (R4.6), as an item's
length is one word (R4.1). -/
def TableShape.ok (s : TableShape) : Bool :=
  decide (1 ≤ s.a) && decide (s.a ≤ 60) && decide (1 ≤ s.message) &&
    decide (s.message + s.tail ≤ 2 ^ s.a) && decide (s.message + s.tail ≤ 2 ^ 32) &&
    decide (s.logRows ≤ 40) && decide (1 ≤ s.answers) && decide (3 * s.answers < s.message) &&
    saltLenOK s.saltBytes &&
    decide (160 + 48 * s.count < 2 ^ 64)

/-- A table's name (R4.10): 112 bytes where root and digest have 32. -/
def TableShape.name (s : TableShape) (cfg root : ByteArray) : ByteArray :=
  tableName root cfg s.a s.message s.tail s.logRows s.answers s.saltBytes

/-- A chain's parameter bytes (R4.3): the version's item, the plan, the item "configuration", the
further items. The plan's bytes are those of `Declared.plan`, which is made of the declared rounds.
-/
def Declared.params (D : Declared) (c : ChainDecl) (cfg : ByteArray) : ByteArray :=
  paramsBytes (D.plan c) cfg c.others

/-- the value of the statement's item number k, from 0 -/
def itemValue (statement : ByteArray) (k : Nat) : Option ByteArray :=
  ((rdItems statement.size statement 0).bind fun x => x.1[k]?).map (·.2)

/-- Root and start of a tree that a round opens. "earlier": for each earlier chain of the file, in
the file's order, the roots that it has sent and its run's value. -/
def TreeSource.src (earlier : List (List ByteArray × ByteArray)) : TreeSource → Option Src
  | .own n => some (.own n)
  | .taken c p => (earlier[c]?).bind fun e => (e.1[p]?).map fun r => .given r e.2

/-- A round as the readers take it. Its kind is that of its entry's name (`kindOf`). Nothing if the
format has no round of this name (R14.11). -/
def DeclaredRound.round (earlier : List (List ByteArray × ByteArray)) (r : DeclaredRound) : Option Round :=
  (kindOf r.entry.name).bind fun k =>
    (r.opens.mapM fun (o : Shape × TreeSource) => (o.2.src earlier).map fun s => (o.1, s)).map
      fun os => ⟨r.entry, k, r.items, os⟩

/-- The description of a chain, as the readers of Fmt/Rules8X.lean take it. Nothing if a round has a
name that the format has not; if in case (b) of R4.5 the statement has not the item; or if a tree is
taken over that "earlier" has not. -/
def Declared.spec (D : Declared) (c : ChainDecl) (cfg statement : ByteArray)
    (earlier : List (List ByteArray × ByteArray) := []) : Option SpecX :=
  (match c.rand with
    | .inFile => some Rand.inFile
    | .item k => (itemValue statement k).map Rand.given
    | .none => some Rand.none).bind fun rand =>
  (c.rounds.mapM fun (r : DeclaredRound) => r.round earlier).map fun rs =>
    { base :=
        { label := c.label
          plan := D.plan c
          params := D.params c cfg
          statement := statement
          rand := rand
          firstTree := c.firstTree
          cfg := cfg
          rounds := rs }
      stored := c.rounds.map DeclaredRound.stored }

/-- The chain's stored trees are trees of tables of the shape s (R7.4): depth, width and the salt's
length. The chain and the shape say these three numbers each in its own words. A stored tree is
marked as stored and has the number 0 (R7.4), as `storedOk` (Fmt/Rules8X.lean) asks. -/
def storedShapeOk (s : TableShape) (c : ChainDecl) : Bool :=
  (c.rounds.flatMap (·.stored)).all fun t =>
    t.sh.a == s.a && t.sh.W == 2 ^ s.logRows && t.salt == s.saltBytes && t.sh.stored &&
      t.sh.tree == 0

/-- The item "the link" begins with the tables' shape and the two numbers of columns (R13.9, items 1
to 3), and these are the shape that D tells and the parts of the draws that the link's stored trees
have (R7.19). -/
def entryShapeOk (D : Declared) : Bool :=
  ((D.link.others.lookup "the link").bind fun v =>
      (rdMany rdWord 8 v 0).map fun x => x.1.map (·.toNat)) ==
    some (D.table.words ++ (D.link.rounds.flatMap (·.stored)).map (·.count))

/-- how many roots a declared chain sends -/
def ChainDecl.roots (c : ChainDecl) : Nat := c.rounds.foldl (fun n r => n + r.entry.roots) 0

/-- The tests on the setting and on the tables' shape, which all seven chains share. A nonce has one
to eight bytes (R8.2), a listed position at most eight (08-parameters.md 8.1, test 20): the writers
write no more. The shape is within the format's ranges (`TableShape.ok`). The shape's number of
answers is the setting's number of answers to a sample (R13.8): the two tell it each in its own
words. -/
def Declared.settingOk (D : Declared) : Bool :=
  decide (1 ≤ D.setting.nonce) && decide (D.setting.nonce ≤ 8) && decide (D.setting.posB ≤ 8) &&
    D.table.ok &&
    D.table.answers == D.setting.samples

/-- The tests on one chain that need no hash, no statement and no word on which chain it is. Every
number of its plan is below 2 ^ 64, and every further item has a name of the format's characters and
fewer than 2 ^ 64 bytes, so that all is hashed as it stands and not modulo 2 ^ 64 (`Plan.fit`,
`nameFit`, Fmt/ParamsReadLaws.lean). The chain has a round. Every round has a name of the format
(R14.11), and its entry has its kind's draws and no others (R6.2: `Entry.fits`,
Fmt/Rules6Round.lean). A tree of the chain's own that a round opens is one whose root the chain
sends. The items of every message's cut (`Entry.cut`) have together the entry's number of bytes
(`Item.bytes`, Fmt/Rules8.lean). A round that samples positions opens a tree: a list of positions is
what a step reads oracle messages at, and the trees that hold them are opened (R13.12, R8.7). -/
def Declared.chainOk (D : Declared) (c : ChainDecl) : Bool :=
  let sent := c.roots
  (D.plan c).fit && (c.others.all fun x => nameFit x.1 && decide (x.2.size < 2 ^ 64)) &&
    !c.rounds.isEmpty &&
    c.rounds.all fun r => ((kindOf r.entry.name).any fun k => r.entry.fits k D.setting.samples) &&
      (r.opens.all fun o => match o.2 with | .own n => decide (n < sent) | .taken _ _ => true) &&
      r.items.foldl (fun n t => n + t.bytes) 0 == r.entry.msg &&
      (r.entry.poss == 0 || !(r.stored.isEmpty && r.opens.isEmpty))

/-- The first n words of the chain's parameter item of a name. -/
def ChainDecl.itemWords (c : ChainDecl) (name : String) (n : Nat) : Option (List Nat) :=
  (c.others.lookup name).bind fun v => (rdMany rdWord n v 0).map fun x => x.1.map (·.toNat)

/-- Every tree that the chain takes over is one that an earlier chain of its file sends: "sent" has
the numbers of roots of the earlier chains, in the file's order. The tree's number in its shape,
which enters its leaves' hashes, is the number under which its root was sent (R7.13): the shape and
the source tell it each in its own words. -/
def ChainDecl.takenOk (c : ChainDecl) (sent : List Nat) : Bool :=
  (c.rounds.flatMap (·.opens)).all fun o =>
    match o.2 with
    | .own _ => true
    | .taken k p => decide (p < sent.getD k 0) && o.1.tree == p

/-- Tests on what the three chains of a key file or of a proof file tell twice, or tell where the
format has a constant. They need no hash and no statement; what they leave out: this file's head, 4.
"label", "shared", "second": the three chains' labels (R13.4, R14.3, R14.9, R14.10): a key file's
and a proof file's are six numbers. "record": whether the first chain's plan has the entry RECORD
(R13.15: in a key file; R14.3: in no plan of a proof).
  `Declared.settingOk`, and `Declared.chainOk` of each chain. The labels (R13.4, R14.9, R14.10).
  The cases of the random bytes (FORMAT.md 7.8): in the file; item 1 of the statement, the binding
  tree's root; in the file. The entry RECORD. The last round of the first and of the shared chain is
  `SEAL`, and the second chain has no such round (R13.6, R13.18, R13.19; R14.9, R14.10 and
  10-proof-file.md 10.6 for a proof; the second chain's statement holds the two seals: R4.7). The
  binding tree's shape is the item "binding tree" of the first chain (R13.5, R14.6), its salts have
  the setting's length, and its depth is at most 48 (R14.6).
  The tables' shape is the beginning of "the test on the table" (R13.13), and the stored trees'. The
  shared chain has one round `LOC`; it opens the stored table, under the statement's item 0 and at
  all its draws, and no tree of the chain (R14.9). No other round of the three chains opens a stored
  table.
  "codes" and "the test on the table" are the same, byte for byte, in the first and the shared
  chain (R13.5, R14.9). The second chain has no item behind "configuration" (R13.5, R14.10).
  The second chain continues the first chain's list of trees and adopts one tree of the shared
  chain, so its first own tree has the number of the first chain's roots + 1 (R13.7). The first two
  chains take no tree over; whatever the second opens of the two earlier chains was sent there. -/
def Declared.chainsFormOk (D : Declared) (T : ThreeDecl) (label shared second : Nat)
    (record : Bool) : Bool :=
  D.settingOk && D.chainOk T.first && D.chainOk T.shared && D.chainOk T.second &&
    T.first.label == label && T.shared.label == shared && T.second.label == second &&
    T.first.rand == .inFile && T.shared.rand == .item 1 && T.second.rand == .inFile &&
    T.first.record == record && !T.shared.record && !T.second.record &&
    (T.first.rounds.getLast?).any (·.entry.name == "SEAL") &&
    (T.shared.rounds.getLast?).any (·.entry.name == "SEAL") &&
    !(T.second.rounds.any (·.entry.name == "SEAL")) &&
    T.first.itemWords "binding tree" 2 == some [T.bind.depth, T.bind.saltBytes] &&
    T.bind.saltBytes == D.setting.salt && decide (T.bind.depth ≤ 48) &&
    T.first.itemWords "the test on the table" 6 == some D.table.words &&
    storedShapeOk D.table T.first && storedShapeOk D.table T.shared &&
    storedShapeOk D.table T.second &&
    ((T.shared.rounds.filter fun r => r.entry.name == "LOC").map fun r =>
      r.stored.map (fun t => (t.item, t.lo, t.count)) == [(0, 0, r.entry.poss)] &&
        r.opens.isEmpty) == [true] &&
    (T.shared.rounds.all fun r => r.entry.name == "LOC" || r.stored.isEmpty) &&
    (T.first.rounds.all (·.stored.isEmpty)) && (T.second.rounds.all (·.stored.isEmpty)) &&
    (T.first.others.lookup "codes").isSome &&
    T.first.others.lookup "codes" == T.shared.others.lookup "codes" &&
    T.first.others.lookup "the test on the table" ==
      T.shared.others.lookup "the test on the table" &&
    T.shared.others.map (·.1) == ["codes", "the test on the table"] && T.second.others.isEmpty &&
    T.first.firstTree == 0 && T.shared.firstTree == 0 &&
    T.second.firstTree == T.first.roots + 1 &&
    T.first.takenOk [] && T.shared.takenOk [] && T.second.takenOk [T.first.roots, T.shared.roots]

/-- The hash-free tests on a key file's chains. The binding tree has the depth 0 (R13.6). -/
def Declared.keyFormOk (D : Declared) : Bool :=
  D.chainsFormOk D.key 0x46524d02 0x4c494e01 0x4c494e02 true && D.key.bind.depth == 0 &&
    D.key.first.others.map (·.1) ==
      ["index-mask message", "ranges", "binding tree", "codes", "the test on the table"]

/-- The hash-free tests on a proof file's chains. Behind "binding tree" any further items are
admitted (R14.3, 9; the programs place none there). -/
def Declared.proofFormOk (D : Declared) : Bool :=
  D.chainsFormOk D.proof 0x46524d01 0x46524d03 0x46524d04 false &&
    (D.proof.first.others.map (·.1)).take 7 ==
      ["codes", "the test on the table", "request's shape", "layout", "links' identifiers",
        "pending rows", "binding tree"]

/-- The chains of a file, in the file's order. "file": 0 an entry file, 1 a key file, 2 a proof
file. -/
def Declared.chainsOf (D : Declared) : Nat → List ChainDecl
  | 0 => [D.link]
  | 1 => [D.key.first, D.key.shared, D.key.second]
  | 2 => [D.proof.first, D.proof.shared, D.proof.second]
  | _ => []

/-- The shape of the tree whose root is sent as number n, from 0, on chain number "chain", from 0,
of a file: the shape under which it is first opened, by its own chain or by a later chain of the
file that has taken it over. Nothing if no round of the file opens it: a shape is told only where a
tree is opened. -/
def Declared.shapeOf (D : Declared) (file chain n : Nat) : Option Shape :=
  ((D.chainsOf file).zipIdx.flatMap fun c =>
    (c.1.rounds.flatMap (·.opens)).filter fun o =>
      match o.2 with
      | .own m => c.2 == chain && m == n
      | .taken k p => k == chain && p == n).head?.map (·.1)

/-! ## The statement -/

/-- The statement's bytes: both tables' items, the first table's first (R13.5). -/
def EntryStm.bytes (x : EntryStm) : ByteArray :=
  tableItem "the first table" x.first.root x.first.answers ++
    tableItem "the further table" x.further.root x.further.answers

/-- The statement of a key file's one-time chain (R13.5): the item "table". -/
def TableSt.item (t : TableSt) : ByteArray := tableItem "table" t.root t.answers

/-- The statement of a shared chain, in a key file and in a proof file (R13.5, R14.9): the item
"table", then the binding tree's root, which is computed and stands in no file. (The statement of a
second chain is `sealItems`, Fmt/Rules4.lean, of the two earlier chains' seals.) -/
def sharedStm (t : TableSt) (bindRoot : ByteArray) : ByteArray :=
  t.item ++ item bindRootName bindRoot

/-- The statement of a proof file's first chain (R14.3): "table", "stored copy", "request", "the
request file's words". -/
def ProofStm.bytes (x : ProofStm) : ByteArray :=
  x.table.item ++ item "stored copy" (u64n x.copy.toNat) ++ item "request" (text x.request) ++
    item "the request file's words" (text x.words)

/-- The next token as an element of E (R15.7): e_0 is the token, e_1 and e_2 are 0. -/
def UserStm.reply (u : UserStm) : Ext := (u.token.toUInt64, 0, 0)

/-- The string of which the commitment ID is the hash under the number 179 (R4.11): the
configuration's digest; the first table's name as a string of bytes; the list of the elements of its
record's seeds, flat; the list of its answers; a last list, which closes the string (by the page it
is empty, the word 0: no element of it is defined). The seeds and the last list are arguments, tied
to nothing here. The ID itself: `publishedID` (Fmt/Rules4.lean) at the same five arguments. -/
def idString (D : Declared) (cfg : ByteArray) (t : TableSt) (seeds : List Ext)
    (told : List ByteArray) : ByteArray :=
  publishedBytes cfg (D.table.name cfg t.root) seeds t.answers told

/-- The form of a table: a root of 32 bytes; as many answers as the shape says; each answer
canonical (R1.4). -/
def TableSt.ok (f : Fld) (s : TableShape) (t : TableSt) : Bool :=
  t.root.size == 32 && t.answers.length == s.count && t.answers.all f.okE

/-- The form of an entry's statement: both tables'. -/
def EntryStm.ok (D : Declared) (x : EntryStm) : Bool :=
  x.first.ok D.setting.field D.table && x.further.ok D.setting.field D.table

/-- The statement, from the first table and the file: the further table is the file's. -/
def EntryParsed.stm (first : TableSt) (F : EntryParsed) : EntryStm := ⟨first, F.table⟩

/-- Tests on the declared structure as far as an entry file goes, at a configuration's digest cfg
and a statement x. (They take a statement because the format's own conditions read one: its size,
and the roots in its items.) They do not show that D is what public files give: a made-up D can pass
(Fmt/ParsedKnown.lean has one); what they leave uncompared is told in this file's head, 4.
What D tells twice, and the clause that compares the two:
  the tables' shape, and the stored trees' depth, width and salt: `storedShapeOk`;
  the tables' shape and the parts of LINK's draws, and the item "the link": `entryShapeOk`;
  the shape's number of answers, and the setting's number of answers to a sample: `settingOk`;
  the parts of a round's draws, and the entry's number of positions: `storedOk` (Fmt/Rules8X.lean).
Where the format has a constant: the link's label (R13.4); its random bytes stand in the file; its
plan has the entry RECORD where tables have a record (R13.15); its first tree has the number 0, and
it takes no tree over (FORMAT.md 7.8, the table at its end); it has no round `SEAL` (R13.10); the
names and the order of its parameter items (R13.5). And `Declared.settingOk`, `Declared.chainOk`.
-/
def Declared.entryFormOk (D : Declared) (cfg : ByteArray) (x : EntryStm) : Bool :=
  cfg.size == 32 && D.settingOk && D.chainOk D.link && D.link.label == 0x4c4e4b01 &&
    D.link.rand == .inFile && D.link.record && D.link.firstTree == 0 && D.link.takenOk [] &&
    !(D.link.rounds.any (·.entry.name == "SEAL")) &&
    D.link.others.map (·.1) == ["codes", "the link"] &&
    ((D.spec D.link cfg x.bytes).any fun S => S.ok) && storedShapeOk D.table D.link &&
    entryShapeOk D

/-- The same at the configuration's digest that the format's own hash gives for the declared files.
In `Declared.entryFormOk` the digest is a free argument, of which its size alone is asked: whoever
calls it ties the digest to the files, as here; under another hash h by `Declared.cfgW h`. -/
def Declared.entryFormOkOwn (D : Declared) (x : EntryStm) : Bool := D.entryFormOk D.cfg x

/-! ## The writers -/

/-- the four bytes that say what kind of file it is (R13.1, R14.2) -/
def tagKey : String := "CPIK"
/-- the same of an entry file -/
def tagEntry : String := "CPEN"
/-- the same of a proof file -/
def tagProof : String := "CPPF"

/-- The first eight bytes of a file: its kind, then the four characters of the format's version,
which are the low bytes of the first parameter item's word (R4.3). -/
def headOf (tag : String) (f : Fld) : ByteArray := ascii tag ++ (versionValue f).extract 0 4

/-- A table's bytes in a file (R13.2, R13.3): the root, bare; the answers, without their number. -/
def TableSt.bytes (t : TableSt) : ByteArray := t.root ++ cat (t.answers.map ext)

/-- An opening's bytes (R7.8). -/
def OpenParsed.bytes (o : OpenParsed) : ByteArray :=
  cat (o.cols.map fun c => colBytes c.1 ++ c.2) ++ cat o.given

/-- A round's bytes (R8.7): the message; the nonce; the listed positions; the openings. -/
def RoundParsed.bytes (P : Plan) (r : RoundParsed) : ByteArray :=
  cat (r.vals.map spellGot) ++
    (match r.nonce with
      | none => ByteArray.empty
      | some x => lowBytes P.nonce x.toNat) ++
    cat (r.listed.map fun x => lowBytes P.posB x.toNat) ++ cat (r.opens.map OpenParsed.bytes)

/-- A chain's bytes (R8.1), under its plan. -/
def ChainParsed.bytes (P : Plan) (x : ChainParsed) : ByteArray :=
  x.rand.getD ByteArray.empty ++ cat (x.rounds.map (RoundParsed.bytes P))

/-- A slot's bytes: the word, the salt, the path. -/
def SlotParsed.bytes (s : SlotParsed) : ByteArray := u64 s.place ++ s.salt ++ cat s.path

/-- A key file's bytes (R13.2), under its three chains' plans. -/
def KeyParsed.bytesAt (P1 P2 P3 : Plan) (F : KeyParsed) : ByteArray :=
  F.head ++ F.table.bytes ++ F.first.bytes P1 ++ F.slot.bytes ++ F.shared.bytes P2 ++
    F.second.bytes P3

/-- The same under the plans of the declared structure. -/
def KeyParsed.bytes (D : Declared) (F : KeyParsed) : ByteArray :=
  F.bytesAt (D.plan D.key.first) (D.plan D.key.shared) (D.plan D.key.second)

/-- An entry file's bytes (R13.3). -/
def EntryParsed.bytes (D : Declared) (F : EntryParsed) : ByteArray :=
  F.head ++ F.table.bytes ++ F.link.bytes (D.plan D.link)

/-- A proof file's bytes (R14.1, R14.2), under its three chains' plans. -/
def ProofParsed.bytesAt (P1 P2 P3 : Plan) (F : ProofParsed) : ByteArray :=
  F.head ++ lowBytes 4 F.copy.toNat ++ F.first.bytes P1 ++ F.slot.bytes ++ F.shared.bytes P2 ++
    F.second.bytes P3

/-- The same under the plans of the declared structure. -/
def ProofParsed.bytes (D : Declared) (F : ProofParsed) : ByteArray :=
  F.bytesAt (D.plan D.proof.first) (D.plan D.proof.shared) (D.plan D.proof.second)

/-! ## The form -/

/-- The item is of the kind that the cut names, and in its one spelling (R1.3, R1.4, R1.5). -/
def ItemValue.fitsItem (f : Fld) : ItemValue → Item → Bool
  | .f x, .f => f.ok x
  | .e x, .e => f.okE x
  | .word _, .word => true
  | .root d, .root => d.size == 32
  | .answer x, .answer => f.okE x
  | _, _ => false

/-- The form of an opening of a tree with columns of W elements and salts of salt bytes, behind
"most" draws: at least one column (R7.8) and at most one for each draw (R6.6); every column and
salt of its length, every element canonical; every given digest of 32 bytes. How many columns and
how many given digests there must be follows from the draws, and is not tested. -/
def OpenParsed.fits (f : Fld) (W salt most : Nat) (o : OpenParsed) : Bool :=
  decide (1 ≤ o.cols.length) && decide (o.cols.length ≤ most) &&
    (o.cols.all fun c => c.1.length == W && c.1.all f.ok && c.2.size == salt) &&
    o.given.all fun d => d.size == 32

/-- What a round's openings must look like, in the file's order (R8.7): for each its columns' width,
its salts' length and the number of its draws. The stored trees come first, each with its table's
salt and its part of the draws; then the other trees, with the plan's salt and all draws. -/
def wantOpens (S : PlanSetting) (r : DeclaredRound) : List (Nat × Nat × Nat) :=
  (r.stored.map fun t => (t.sh.W, t.salt, t.count)) ++
    r.opens.map fun o => (o.1.W, S.salt, r.entry.poss)

/-- The form of a round against its declared round r, under the setting S. -/
def RoundParsed.fits (S : PlanSetting) (r : DeclaredRound) (x : RoundParsed) : Bool :=
  x.vals.length == r.items.length &&
    ((x.vals.zip r.items).all fun y => y.1.fitsItem S.field y.2) &&
    (match x.nonce with
      | none => r.entry.work == 0
      | some n => r.entry.work != 0 && decide (n.toNat < 256 ^ S.nonce)) &&
    (if S.posB == 0 || r.entry.poss == 0 then x.listed.isEmpty
      else !x.listed.isEmpty && decide (x.listed.length ≤ r.entry.poss) &&
        increasing (x.listed.map (·.toNat)) &&
        x.listed.all fun p =>
          decide (p.toNat < 2 ^ r.entry.logN) && decide (p.toNat < 256 ^ S.posB)) &&
    x.opens.length == (wantOpens S r).length &&
    (x.opens.zip (wantOpens S r)).all fun y => y.1.fits S.field y.2.1 y.2.2.1 y.2.2.2

/-- The form of a chain: its random bytes stand in the file exactly in case (a) of R4.5, and are
32; it has as many rounds as the declared chain; every round fits. -/
def ChainParsed.fits (S : PlanSetting) (c : ChainDecl) (x : ChainParsed) : Bool :=
  (match x.rand with
    | none => c.rand != .inFile
    | some b => c.rand == .inFile && b.size == 32) &&
    x.rounds.length == c.rounds.length && (c.rounds.zip x.rounds).all fun y => y.2.fits S y.1

/-- The form of a slot: below 2 ^ depth; the salt's length; one digest of 32 bytes a level. -/
def SlotParsed.fits (b : BindShape) (s : SlotParsed) : Bool :=
  decide (s.place.toNat < 2 ^ b.depth) && s.salt.size == b.saltBytes &&
    s.path.length == b.depth && s.path.all fun d => d.size == 32

/-- The form of a key file. -/
def KeyParsed.fits (D : Declared) (F : KeyParsed) : Bool :=
  F.head == headOf tagKey D.setting.field && F.table.ok D.setting.field D.table &&
    F.first.fits D.setting D.key.first && F.slot.fits D.key.bind &&
    F.shared.fits D.setting D.key.shared && F.second.fits D.setting D.key.second

/-- The form of an entry file. -/
def EntryParsed.fits (D : Declared) (F : EntryParsed) : Bool :=
  F.head == headOf tagEntry D.setting.field && F.table.ok D.setting.field D.table &&
    F.link.fits D.setting D.link

/-- The form of a proof file. -/
def ProofParsed.fits (D : Declared) (F : ProofParsed) : Bool :=
  F.head == headOf tagProof D.setting.field && F.first.fits D.setting D.proof.first &&
    F.slot.fits D.proof.bind && F.shared.fits D.setting D.proof.shared &&
    F.second.fits D.setting D.proof.second

/-- The proof file's head names the table that the statement names (R14.2). -/
def ProofParsed.copyFits (x : ProofStm) (F : ProofParsed) : Bool := F.copy == x.copy

/-! ## The numbers that hang on the draws -/

/-- an opening's two numbers: of columns, of given digests -/
def OpenParsed.counts (o : OpenParsed) : Nat × Nat := (o.cols.length, o.given.length)

/-- a round's numbers: of listed positions; each opening's two -/
def RoundParsed.counts (r : RoundParsed) : Nat × List (Nat × Nat) :=
  (r.listed.length, r.opens.map OpenParsed.counts)

/-- A chain's numbers, round by round. They are what `fits` cannot hold: they follow from the draws
(R7.8, R7.9, R8.2). -/
def ChainParsed.counts (x : ChainParsed) : List (Nat × List (Nat × Nat)) :=
  x.rounds.map RoundParsed.counts

/-! ## From a reader of this library -/

/-- What stands in the file of an opening that was read: without the root in which the walk ends,
the vertices met and the place behind it. Nothing if there is not one salt for each column. -/
def OpenParsed.of (o : OpenOut) : Option OpenParsed :=
  if o.cols.length == o.salts.length then some ⟨o.cols.zip o.salts, o.given⟩ else none

/-- What stands in the file of a round that was read: without the message's bytes (the items spell
them), the draws, and each opening's shape and list. P: the chain's plan; e: the round's entry.
The listed positions are taken from the list that the reader has derived: a strict reader has
compared the file's bytes with it and dropped them. A reader that does not compare must hand on the
file's own. -/
def RoundParsed.of (P : Plan) (e : Entry) (r : RoundOut) : Option RoundParsed :=
  (r.opens.mapM fun y => OpenParsed.of y.2.2).map fun os =>
    { vals := r.vals
      nonce := if e.work == 0 then none else some (UInt64.ofNat r.nonce)
      listed := if P.posB == 0 || e.poss == 0 then [] else r.list.map UInt64.ofNat
      opens := os }

/-- What stands in the file of a chain that was read. P: the chain's plan; rand: the chain's random
bytes, if they stand in the file; a reader does not keep them. Round number i is read under entry
number i of the plan's rounds, the list that the strict reader itself follows. Nothing if the chain
has not as many rounds as that list has entries. -/
def ChainParsed.of (P : Plan) (rand : Option ByteArray) (o : ChainOut) : Option ChainParsed :=
  if P.rounds.length == o.rounds.size then
    ((P.rounds.zip o.rounds.toList).mapM fun x => RoundParsed.of P x.1 x.2).map fun rs => ⟨rand, rs⟩
  else none

end Fmt

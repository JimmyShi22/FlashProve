-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules4.lean: the first query of a chain: items, the plan's bytes, the parameter bytes and their
digest, the run's value, the chain's first value, a stored table's name and the chain of its record,
the commitment ID, the configuration's digest.

A chain is the non-interactive form of one interactive protocol; which one, its label says (a number
below 2^32; the chain of a stored table's record alone has the label 2^32: `recordLabel`). The first
query is the hash call that gives the chain's first value (`firstValueW`). Its first value is a hash
of whatever is settled before the prover's first message: parameters, statement, record, and the
run's value if the chain has random bytes. These are total functions on bytes. The programs are the
C++ implementation that comes with this Lean code.

Sources. Section 4 of the format page (docs/format/FORMAT.md, which comes with the programs), rules
R4.1 to R4.10 as they stand at one edition of the page, and R4.11 as it stands at another,
which lays the record's seeds into the commitment ID's input and ends it with a list
that is empty: the word 0. Neither is the edition that ships.
At one or the other of two further editions, which are not in this repository either, R4.3 and R4.12
differ from the edition named first, and the section's other rules do not.
The section's known answers are taken from these editions and from others of the page
(a stored table's item, a stored table's name, those of the commitment ID);
none of this is
held against the page that ships. R4.12, the committer's rule, is a rule on
an honest committer that no verifier can see kept: nothing of it is here. No Mathlib.

1. What the file contains.
   Every rule that hashes is generic in a monad m and in the hash h : number, tree, index, start,
     bytes ↦ m bytes, its first argument (names that end in W). At m := Id, h := `Fmt.formatHash`: the
     evaluation, and the flat names without W, at which the tests stand. At a tree of queries: a
     parser that asks the oracle (`HM`, Fmt/Rules23.lean; the reader of a chain in a file:
     Fmt/Rules8.lean).
 Without a hash.
   `item name value` (R4.1). A name (a text), the word (8 bytes, the lowest first: `u64n`,
     Fmt/Rules1.lean) of the length of the value's bytes, the value's bytes. `items`: several in a
     row.
   `Entry.bytes`, `Plan.bytes` (R4.3, 2). The spelling of a plan (Fmt/Plan.lean): eight words
     (field; hash: 1; bytes of a leaf's salt; of a nonce in a file; of a listed position; answers to
     each out-of-domain sample; whether a sum-check's message leaves out the coefficient that the
     check fixes; number of entries), then each entry: its name (a text) and its eleven words.
   `Plan.rounds` (R4.3, end). `Plan.ok`: what the page asks of a plan of a chain and can be tested
     on the plan alone, in part (more of it: `Spec.ok`, Fmt/Rules8.lean).
   `versionValue f` (R4.3, 1). The value of the first parameter item: one word: the characters H, 8,
     the field's digit, the hash's digit 1, then four zero bytes.
   `paramsHead P` (R4.3, 1 and 2).
   `paramsBytes P cfg others` (R4.3, R4.9).
   `firstBytes pd st rec run` (R4.6). No chain of the format fills the record (the argument
     `record`): its length word is the constant 0; the argument stays for the sake of the laws in
     Fmt/Rules4Laws.lean.
   `runOk run` (R4.5, end).
   `sealItem s`, `sealItems l` (R4.7). A chain that goes on where earlier chains of the session have
     ended has in its statement one item for each of them (s: that chain's seal: `Kind.sealed`,
     Fmt/Plan.lean; `drawSeal`, Fmt/Rules6.lean), in an order that the protocol fixes (a request's
     chain behind a batch's shared rounds: its own first chain's, then the shared chain's).
   `bindRootName` (R4.5's bracket).
 With the hash.
   `paramsDigestW h params` (R4.4).
   `runValueW h lab pd rnd` (R4.5).
   `firstValueW h lab pd st rec run` (R4.6).
   `startChainW h lab pd st rnd`.
   `recordLabel`, `recordFirstW h name` (R4.8). The chain from which the seeds of a stored table's
     record (its list of answers) are drawn. Its one round and the drawing are other sections'
     rules.
   `tableName` (R4.10; no hash). The root of its tree; the configuration's digest; six words (a,
     where rows have length 2^a; the entries of a row's message; of its random tail; v, where the
     table has 2^v rows; the stored answers to a sample for each row; the bytes of a
     leaf's salt): 112 bytes. (The tree's number is not among them:
     every stored table's tree has the number 0, a constant of the format: R7.4;
     not held against the page that ships.)
   `tableItem name root answers` (R4.6; no hash). The item of a stored table that a chain reads: its
     root as a string of bytes (`text`, Fmt/Rules1.lean: the word 32, the 32 bytes), then its
     record: the list of its answers, elements of E, by row and within a row by answer. The
     record's seeds stand in no item. The 112-byte name
     stands in no item (R4.10): it is computed (`tableName`) and stands in two places: as the
     statement of the chain of R4.8 (`recordFirstW`) and in the input of the commitment ID
     (`publishedIDW`: the commitment ID).
   `publishedIDW h cfg name seeds answers told` (R4.11). The commitment ID (its input:
     `publishedBytes`): the configuration's digest; the name as a string of bytes; three lists, each
     behind the word of its number: the elements of the record's seeds (R4.8), one flat list, seed
     by seed the coordinates of its point and then its factor, 24 bytes each, with no word for the
     number of coordinates (the name, which stands before the list, fixes it: R4.10); the record's
     answers, 24 bytes each; a last list, which closes the string: by the page it is empty, the word
     0 and nothing behind it, and no element of it is defined by the format. The
     function lays the elements that a caller hands (`told`) as they are, with no length of their
     own; which elements, how many and of what length is tested by no function here.
     The configuration's digest
     stands in the input twice (the name holds it); the page says: on purpose. It says what is
     committed under which public files, not whose weights (R4.11). It stands in no first query
     (R4.6's last sentence). The number 179 is R3.1's;
     not held against the page that ships.
   `configDigestW h files` (R4.9; its input: `configBytes`). The word of the number of public files,
     then each file behind the word of its length.

2. What is checked when the file compiles. 33 tests (#guard). Every known answer of the page's
section on the first query is among them, at the end of the file.

3. Theorems. None.

4. What is not here, and what is this library's own.
   Not here: (a) the canonical bytes of
     types made of several fields (R4.2); (b) which files the configuration's digest takes in beyond
     the first, and their order; (c) the list of the rounds' names with their kinds. At
     another edition than the one that ships: (a) and (b)
     are not ruled by the page (R4.2 and R4.9 say so themselves); (c) is ruled for
     the three toy runs in sections 12 and 13 (R12.8, R13.10), rendered in Fmt/M1Plan.lean,
     Fmt/M2Plan.lean, Fmt/M3Plan.lean.
   Which of the three cases of random bytes holds (the first 32 bytes of the chain in its file; 32
     bytes that stand in this query as an item; none) is the protocol's to say: here the caller
     hands the bytes, or none.
   That the root and the record of every stored table which a chain reads stand among the items of
     its statement, by value, before its other items, one item a table (R4.6: statement, not
     parameters: a file never sets a public parameter), is a duty of whoever lists the items:
     `tableItem` spells one such item.
   This library's own, not the page's (it is silent). A number is spelled modulo 2^64; a name by its
     UTF-8 bytes (the format's names are ASCII). `startChainW` refuses a label that is not below
     2^32 and random bytes that are not 32; it makes its hash calls only behind these two tests.
   Of all these functions `startChainW` alone tests the length of a byte string, and none tests that
     a triple is an element of E: the counts 32 and 112 above are those of a root, a digest and a
     name of the format.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Plan
import Fmt.Rules23

namespace Fmt

/-- An item: name, length of the value, value. -/
def item (name : String) (value : ByteArray) : ByteArray := textS name ++ u64n value.size ++ value

/-- several items in a row -/
def items (l : List (String × ByteArray)) : ByteArray := cat (l.map fun x => item x.1 x.2)

/-- the spelling of an entry of a plan: the round's name and the eleven words, in the page's order
-/
def Entry.bytes (r : Entry) : ByteArray :=
  textS r.name ++ u64n r.count ++ u64n r.work ++ u64n r.msg ++ u64n r.roots ++ u64n r.answers ++
    u64n r.drawE ++ u64n r.drawNZ ++ u64n r.poss ++ u64n r.logN ++ u64n r.trits ++ u64n r.rows

/-- the field's number: 1 or 2 -/
def Fld.num : Fld → Nat
  | .one => 1
  | .two => 2

/-- The plan's bytes: eight words, then the entries. -/
def Plan.bytes (P : Plan) : ByteArray :=
  u64n P.field.num ++ u64n 1 ++ u64n P.salt ++ u64n P.nonce ++ u64n P.posB ++ u64n P.samples ++
    u64n P.saved ++ u64n P.entries.length ++ cat (P.entries.map Entry.bytes)

/-- the name of the one entry that is no round of its chain -/
def recordName : String := "RECORD"

/-- The rounds of the chain: the entry under the name RECORD is passed over. -/
def Plan.rounds (P : Plan) : List Entry := P.entries.filter fun r => r.name != recordName

/-- What can be tested on the plan alone, in part (more of it: `Spec.ok`, Fmt/Rules8.lean): the
first of the eleven words is 1 in every entry; the word "saved" is 1; at most one entry stands under
the name RECORD. -/
def Plan.ok (P : Plan) : Bool :=
  P.entries.all (fun r => r.count == 1) && P.saved == 1 &&
    decide ((P.entries.filter fun r => r.name == recordName).length ≤ 1)

/-- the name of the first parameter item -/
def versionName : String := "the format's version"

/-- the value of the first parameter item: one word -/
def versionValue : Fld → ByteArray
  | .one => ascii "H811" ++ zeroBytes 4
  | .two => ascii "H821" ++ zeroBytes 4

/-- the version's item and the plan -/
def paramsHead (P : Plan) : ByteArray := item versionName (versionValue P.field) ++ P.bytes

/-- the name of the first item behind the plan -/
def configName : String := "configuration"

/-- The parameters' bytes; cfg: the configuration's digest. -/
def paramsBytes (P : Plan) (cfg : ByteArray) (others : List (String × ByteArray)) : ByteArray :=
  paramsHead P ++ item configName cfg ++ items others

/-- What is hashed for the chain's first value. -/
def firstBytes (pd statement record : ByteArray) (run : Option ByteArray) : ByteArray :=
  pd ++ u64n statement.size ++ statement ++ u64n record.size ++ record ++ (match run with
    | none => u64n 0
    | some r => u64n 1 ++ r)

/-- a verifier refuses a run's value of 32 zero bytes -/
def runOk (run : ByteArray) : Bool := decide (run ≠ zero32)

/-- the item of a chain that goes on where an earlier chain of the same session has ended. -/
def sealItem (s : ByteArray) : ByteArray := item "the seal of an earlier chain" s

/-- one item `sealItem` for each earlier chain, in the order given -/
def sealItems (l : List ByteArray) : ByteArray := cat (l.map sealItem)

/-- the name of the item of a batch's shared chain whose 32 bytes are its random bytes -/
def bindRootName : String := "the binding tree's root"

/-- the label of the chain from which the seeds of a stored table's record are drawn -/
def recordLabel : Nat := 2 ^ 32

/-- A stored table's name. -/
def tableName (root cfg : ByteArray) (a message tail logRows answers saltBytes : Nat) : ByteArray :=
  root ++ cfg ++ u64n a ++ u64n message ++ u64n tail ++ u64n logRows ++
    u64n answers ++ u64n saltBytes

/-- the input of the commitment ID: the configuration's digest; the first table's name as a string
of bytes; the list of the elements of its record's seeds, seed by seed the point's coordinates and
then the factor; the list of its record's answers; a last list, which closes the string, each
element laid as it is (by the page it is empty, the word 0: no element of it is defined by the
format) -/
def publishedBytes (cfg name : ByteArray) (seeds answers : List (UInt64 × UInt64 × UInt64))
    (told : List ByteArray) : ByteArray :=
  cfg ++ text name ++ list ext seeds ++ list ext answers ++ list id told

/-- The item of a stored table: its root as a string of bytes, then the list of its record's
answers. -/
def tableItem (name : String) (root : ByteArray) (answers : List (UInt64 × UInt64 × UInt64)) :
    ByteArray :=
  item name (text root ++ list ext answers)

/-- what is hashed for the configuration's digest -/
def configBytes (files : List ByteArray) : ByteArray := u64n files.length ++ cat (files.map text)

/-- what stands at the head of a chain: its run's value, if it has random bytes, and its first value
-/
structure ChainHead where
  run  : Option ByteArray
  rho0 : ByteArray

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The parameters' digest. -/
def paramsDigestW (params : ByteArray) : m ByteArray := h 169 0 1 zero32 params

/-- The run's value. -/
def runValueW (lab : Nat) (pd rnd : ByteArray) : m ByteArray := h 172 0 lab zero32 (pd ++ rnd)

/-- The chain's first value. -/
def firstValueW (lab : Nat) (pd statement record : ByteArray) (run : Option ByteArray) :
    m ByteArray :=
  h 160 0 lab zero32 (firstBytes pd statement record run)

/-- The head of a chain that is started from the parameters' digest and the statement (the digest of
`paramsBytes`; the statement a list of items): the record is empty. Refused: a label that is not
below 2^32; random bytes that are not 32; a run's value of 32 zero bytes. -/
def startChainW (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray) :
    m (Option ChainHead) :=
  if lab < 2 ^ 32 then
    match rnd with
    | none => do
        let r0 ← firstValueW h lab pd statement ByteArray.empty none
        pure (some ⟨none, r0⟩)
    | some b =>
        if b.size = 32 then do
          let run ← runValueW h lab pd b
          if runOk run then
            let r0 ← firstValueW h lab pd statement ByteArray.empty (some run)
            pure (some ⟨some run, r0⟩)
          else pure none
        else pure none
  else pure none

/-- The first value of the chain of a stored table's record: a function of the table's name alone.
-/
def recordFirstW (tableName : ByteArray) : m ByteArray :=
  firstValueW h recordLabel zero32 tableName ByteArray.empty none

/-- The configuration's digest. -/
def configDigestW (files : List ByteArray) : m ByteArray := h 169 0 2 zero32 (configBytes files)

/-- The commitment ID. -/
def publishedIDW (cfg name : ByteArray) (seeds answers : List (UInt64 × UInt64 × UInt64))
    (told : List ByteArray) : m ByteArray :=
  h 179 0 0 zero32 (publishedBytes cfg name seeds answers told)

end

/-! ## The flat names: at the format's own hash -/

def paramsDigest (params : ByteArray) : ByteArray := paramsDigestW (m := Id) formatHash params
def runValue (lab : Nat) (pd rnd : ByteArray) : ByteArray := runValueW (m := Id) formatHash lab pd rnd
def firstValue (lab : Nat) (pd statement record : ByteArray) (run : Option ByteArray) : ByteArray :=
  firstValueW (m := Id) formatHash lab pd statement record run
def startChain (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray) : Option ChainHead :=
  startChainW (m := Id) formatHash lab pd statement rnd
def recordFirst (tableName : ByteArray) : ByteArray := recordFirstW (m := Id) formatHash tableName
def configDigest (files : List ByteArray) : ByteArray := configDigestW (m := Id) formatHash files
def publishedID (cfg name : ByteArray) (seeds answers : List (UInt64 × UInt64 × UInt64))
    (told : List ByteArray) : ByteArray :=
  publishedIDW (m := Id) formatHash cfg name seeds answers told

/-! ## The page's known answers: a toy plan of six rounds, in both fields -/

namespace Toy4

/-- the toy plan, read off the known parameters' bytes -/
def plan (f : Fld) : Plan where
  field := f
  salt := 40
  nonce := 8
  posB := 0
  samples := 1
  saved := 1
  entries := [
    { name := "toy: challenge", msg := 48, drawE := 1 },
    { name := "toy: nothing", msg := 24 },
    { name := "toy: positions", work := 8, msg := 32, roots := 1, drawE := 1, poss := 5,
      logN := 10, rows := 3 },
    { name := "toy: seed", drawE := 3, drawNZ := 1 },
    { name := "toy: matrix", msg := 24, answers := 1, trits := 40 },
    { name := "toy: seal", msg := 8 } ]

/-- the toy's configuration: one public file, the four bytes "toy" and a line feed -/
def cfg : ByteArray := configDigest [ascii "toy\n"]
def params (f : Fld) : ByteArray := paramsBytes (plan f) cfg [("toy: a table's length", u64n 1024)]
def pd (f : Fld) : ByteArray := paramsDigest (params f)
def statement : ByteArray := items [("toy: claim", ext (1, 2, 3)), ("toy: name", textS "abc")]
def rnd : ByteArray := pattern 32 5 1
def run (f : Fld) : ByteArray := runValue 7 (pd f) rnd

end Toy4

#guard hex (Toy4.params .two) = "140000000000000074686520666f726d617427732076657273696f6e08000000000000004838323100000000020000000000000001000000000000002800000000000000080000000000000000000000000000000100000000000000010000000000000006000000000000000e00000000000000746f793a206368616c6c656e6765010000000000000000000000000000003000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000746f793a206e6f7468696e67010000000000000000000000000000001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e00000000000000746f793a20706f736974696f6e73010000000000000008000000000000002000000000000000010000000000000000000000000000000100000000000000000000000000000005000000000000000a00000000000000000000000000000003000000000000000900000000000000746f793a2073656564010000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000b00000000000000746f793a206d6174726978010000000000000000000000000000001800000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000280000000000000000000000000000000900000000000000746f793a207365616c010000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d00000000000000636f6e66696775726174696f6e2000000000000000e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f1500000000000000746f793a2061207461626c652773206c656e67746808000000000000000004000000000000"
#guard hex Toy4.cfg = "e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f"
#guard hex (tableName (pattern 32 13 4) Toy4.cfg 10 512 40 9 1 40) = "04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9ce7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f0a0000000000000000020000000000002800000000000000090000000000000001000000000000002800000000000000" && (tableName (pattern 32 13 4) Toy4.cfg 10 512 40 9 1 40).size = 112
-- this name's second word is 512 and its fourth 9, so a seed's point has nine coordinates and the
-- table 512 rows. The second of the next three tests the coding alone: a point of two coordinates
-- and two answers fit no such name. The third has, by the page, this name's own seed (R4.8): nine
-- coordinates, then the factor; it fits the name in its seed, not in its answers. The ten elements
-- are written out: this file has no drawing, and that they are what is drawn is not tested here
#guard hex (publishedID Toy4.cfg (tableName (pattern 32 13 4) Toy4.cfg 10 512 40 9 1 40) [] [] []) = "80d59c8b07aaa71829c9765057082a108618402daf661caf2c390c09dfafddd3"
#guard hex (publishedID Toy4.cfg (tableName (pattern 32 13 4) Toy4.cfg 10 512 40 9 1 40) [(7, 8, 9), (10, 11, 12), (13, 14, 15)] [(1, 2, 3), (4, 5, 6)] []) = "4fb918a30faa7643cf8e6bc431c6643d7b5b4cc298dd0531cc0206bb4f756a0b"
#guard hex (publishedID Toy4.cfg (tableName (pattern 32 13 4) Toy4.cfg 10 512 40 9 1 40) [(17799733082786975360, 14854592069346109399, 5990731933783482823), (13564804438734996683, 441656099523667129, 215777466525601570), (16239737854738838316, 15045419985285204138, 10431163260387808820), (14884426890899013557, 9492689195496810980, 12193896627802477559), (15067948119200355445, 12482920520684999794, 13305970125725682734), (5854266964013340952, 3332347011981759785, 16152420038908725532), (1133196081987121975, 10033814388777857401, 5526922237616460697), (10964707569585212473, 17110115918534250475, 9088734603053602828), (1483051306215837095, 5357982833568135867, 7051363869388652834), (1591371840649369906, 5631853371392708714, 1088755482909579120)] [(1, 2, 3), (4, 5, 6)] []) = "e18438e0725ec651fc8bffa3b3f860ddeca70e6cb1991dd43620b98ef6f05bd2"
#guard hex (tableItem "table" (pattern 32 13 4) []) = "05000000000000007461626c653000000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9c0000000000000000"
-- this library's own: with a record of two answers the value grows by 48 bytes and the list's word
-- is 2
#guard (tableItem "table" (pattern 32 13 4) [(1, 2, 3), (4, 5, 6)]).size = 69 + 48 && hex ((tableItem "table" (pattern 32 13 4) [(1, 2, 3), (4, 5, 6)]).extract 61 77) = "02000000000000000100000000000000"
#guard hex Toy4.statement = "0a00000000000000746f793a20636c61696d18000000000000000100000000000000020000000000000003000000000000000900000000000000746f793a206e616d650b000000000000000300000000000000616263"
#guard hex (Toy4.pd .two) = "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1"
#guard hex (Toy4.run .two) = "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986"
#guard hex (firstValue 7 (Toy4.pd .two) Toy4.statement ByteArray.empty (some (Toy4.run .two))) = "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72"
#guard hex (firstValue 7 (Toy4.pd .two) Toy4.statement ByteArray.empty none) = "8f1d3a0a2a3f69ec890ce893d576a15eb38d2f9f11f497eee333c9eb23247f33"
#guard hex (Toy4.pd .one) = "7de82393ca9b1c414194f8ba35e40fd5b2aa2a9ad637d741cea7e93a9c257f82"
#guard hex (Toy4.run .one) = "fd50818f742a65f3a1585c667ae07d35b3759f5e922910132b6d953d9feee385"
#guard hex (firstValue 7 (Toy4.pd .one) Toy4.statement ByteArray.empty (some (Toy4.run .one))) = "8ab45624b5f889e335e84864762f4b3d7e51eb87d278e34722ed12b0e114d90c"
#guard hex (firstValue 7 (Toy4.pd .one) Toy4.statement ByteArray.empty none) = "3d779f4e33228af38fe59cf4b550a6d778a1bcbe51b9fb5e9d3ad2800fb427cd"

/-! ## Tests of this library's own, not the page's: the verifier's head of a chain; the plan; the
record's chain and the configuration's digest (values made by the page's program lines); the
oracle's form of the hash gives the same -/

#guard ((startChain 7 (Toy4.pd .two) Toy4.statement (some Toy4.rnd)).map fun c => (c.run.map hex, hex c.rho0)) = some (some "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986", "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72")
#guard ((startChain 7 (Toy4.pd .two) Toy4.statement none).map fun c => (c.run.map hex, hex c.rho0)) = some (none, "8f1d3a0a2a3f69ec890ce893d576a15eb38d2f9f11f497eee333c9eb23247f33")
#guard (startChain (2 ^ 32) (Toy4.pd .two) Toy4.statement none).isNone
#guard (startChain 7 (Toy4.pd .two) Toy4.statement (some (pattern 31))).isNone
#guard (Toy4.plan .two).ok
#guard (Toy4.plan .two).rounds.length = 6
#guard (Toy4.params .two).size = 859
#guard sealItems [pattern 32, pattern 32 5 1] = sealItem (pattern 32) ++ sealItem (pattern 32 5 1)
#guard (sealItem (pattern 32)).size = 8 + 28 + 8 + 32
#guard runOk zero32 = false
#guard runOk (pattern 32) = true
#guard hex (firstBytes zero32 (pattern 5) ByteArray.empty none) = "00000000000000000000000000000000000000000000000000000000000000000500000000000000030a11181f00000000000000000000000000000000"
#guard hex (recordFirst (pattern 5)) = "9793bf33702e6448469bb6d53c70985a06f2b4ff70cd4dd9b55a72a382337c16"
#guard hex (configBytes [pattern 3, ByteArray.empty]) = "02000000000000000300000000000000030a110000000000000000"
#guard hex (configDigest [pattern 3, ByteArray.empty]) = "0eee7e030496e46e269f68a5e5163f946fe606be83c5ddf57f617efd98a8be5e"
#guard hex (firstValueW (m := Id) (HO oracle) 7 (Toy4.pd .two) Toy4.statement ByteArray.empty none) = "8f1d3a0a2a3f69ec890ce893d576a15eb38d2f9f11f497eee333c9eb23247f33"

end Fmt

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/TestChainStm.lean: the tests (#guard) on the statements of the chains of a key file, an entry
file and a proof file, and the values that the tests need. No theorem. Two other files of tests use
values of its namespace `ChainStmKnown`. A test is an evaluation at the values that it names, not a
theorem.
States: 249 tests and 3 examples are checked when the file compiles (A, B, C, E); D is elsewhere.
 A. 55 tests of the readers of Fmt/ChainStmRead.lean at one made-up value of each kind with the
    sizes of a full-size one: the forms hold there, each reader gives the values back; refusals.
 B. 140 tests of Fmt/ChainStm.lean (the statements, the binding tree's root, the test on the
    commitment ID). A test's comment says which kind of expected value from outside this library it
    has. PAGE: a known answer that the format page prints, named by its line's number. SCRIPT: made
    by the page's own script, called by a small program that imports it [that program is not in this
    library]. SCRIPT, OUR ORDER: put together by that program from the script's parts. None of the
    three: a value of this file's own.
 C. 54 tests of Fmt/ChainStmMore.lean at made-up values; among them: two different shapes, one of
    them without `TableShape.wordsFit`, give one string of the commitment ID; so do two different
    lists of digests, one of them without `toldOk`.
 D. 3 tests, in OnBytes/Entry/TestRecordToyDeclared.lean: the two premises of
    `Declared.spec_ok_small` and `Declared.spec_ok_lt` (Fmt/ChainStmSmall.lean) are met together
    at a toy link; under another setting the second is not; the two premises of
    `Declared.entryFormOk_count` and `Declared.entryFormOk_fitsWord` are met together at that link.
 E. 3 examples (no #guard): what `startChainW_rest`, `Declared.idString_closed_inj` and
    `Declared.seedsW_ok_of_size` (Fmt/ChainStmMore.lean) require of their parameter h is met by the
    format's own hash.
Under: nothing is assumed. Fmt.TestRecordSeeds and Fmt.TestRequestItem are imported so that whoever
builds this file builds these two files of tests too; nothing here calls them.
Does not show:
 (1) A SCRIPT value was computed by another implementation than this library's, the page's script;
     it is NO KNOWN ANSWER OF THE PAGE.
 (2) In a value under SCRIPT, OUR ORDER the order is that program's reading of the page, not the
     script's.
 (3) Part A's declared structure has no public file and no chain: `ProofStm.ok` reads its field and
     its tables' shape alone.
 (4) The test "fewer than 2 ^ 64 bytes" (`wholeStm`) is reached by no #guard: no such string can be
     made. What it does is stated by theorems alone (Fmt/ChainStmLaws.lean).
 (5) Part D's tests are at a link's chain: no description of a key's or a proof's chain is tried.
 (6) Of part B, as are (7) to (17). Some tests hold by a definition or by a theorem of the
     neighbouring files, and can fail only if that definition is changed: the four roots of
     `SlotParsed.rootW` beside those of `SlotParsed.root`; `UserStm.keyStm`; "the parts by their own
     names"; the answers are not in the name; the reply is no item.
 (7) Where a closed form is compared with the open form at `SlotParsed.root`, what the test shows is
     that the closed form is something; the tests under `hPage` and on the calls check the value.
 (8) The page has no known answer for: a root at another depth than 2; a shared chain's statement; a
     second chain's.
 (9) The page's two IDs are at a shape of 2 ^ 9 rows with one answer each, and at a table of two
     answers: these tables have not the form `TableSt.ok` at that shape.
 (10) The seeds' elements of the ID with three elements have not the form `seedsOk` there; those of
      the ID whose seed is drawn from the name have it.
 (11) `KeyStm.idOkW` does not require that form. `KeyParsed.idOkW` requires it: so the closed form
      of the test on the ID is checked at no known answer of the page, and at one value alone, which
      is SCRIPT.
 (12) In block 2 two slots do not fit the depth at which their root is computed (`SlotParsed.fits`),
      and `SlotParsed.root` answers all the same: it requires no form. Each of the two tests says
      so.
 (13) In blocks 0 to 7 every hash is the format's own (`hId`, Fmt/Rules7.lean). Block 8 has four
      stand-ins beside it, each described at its definition.
 (14) Several seeds of one record are compared with `Known56.recordSeeds` (Fmt/Rules56Known.lean)
      alone, in Fmt/TestRecordSeeds.lean, and here by their number and form: the page's one drawn
      seed is one.
 (15) That the closed forms require `TableShape.fitsWord` is reached by no test: a shape without it
      says more answers than a table can be given here, so `TableSt.ok` fails there too.
 (16) The last clause of `ProofStm.ok` (fewer than 2 ^ 64 bytes) is reached by no test either: no
      such request or table can be made here.
 (17) Of the chains of the closed forms' declared structure one parameter item alone is set: it
      passes neither `Declared.keyFormOk` nor `Declared.proofFormOk` (Fmt/Parsed.lean; a test in
      block 8), which the closed forms do not require.
Notes in full, with every limit at length, stand at the end of this file.

-/
import Fmt.ChainStmMore
import Fmt.ChainStmSmall
import Fmt.Rules56Known
import Fmt.TestRecordSeeds
import Fmt.TestRequestItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-! # A. The readers at made-up values -/

section
namespace ChainStmTest

/-- 2 ^ 8 rows with one answer each: 256 answers. Rows of length 2 ^ 23, 2 ^ 8 rows, one answer and
salts of 40 bytes are the numbers of the lines table, answers and salt of the small example's
parameter file (prover/examples/target_small_f2/policy.txt). -/
def shape : TableShape := ⟨23, 803, 1001, 8, 1, 40⟩

/-- p - 1 in the second field: the greatest canonical word -/
def pLast : UInt64 := 18446744069414584320

def table : TableSt :=
  ⟨pattern 32, (List.range 256).map fun i => (UInt64.ofNat i, UInt64.ofNat (7 * i + 1), pLast)⟩

def seal1 : ByteArray := pattern 32 5 1
def broot : ByteArray := pattern 32 11 2
def seal2 : ByteArray := pattern 32 13 3

/-- the value of the item "request": 177 words of four bytes; the request file's own bytes: 1,026
words of four bytes (another pattern, so that the two can be told apart) -/
def stm : ProofStm := ⟨table, 7, pattern 708, pattern 4104 9 4, (5, 0, 0)⟩

/-- a declared structure with the shape, a setting in the second field (its five numbers are made
up), no public file and no chain -/
def decl : Declared := { files := [], setting := ⟨.two, 40, 8, 4, 1, 1⟩, table := shape }

/-- all bytes but the last -/
def cutLast (b : ByteArray) : ByteArray := b.extract 0 (b.size - 1)

/-- one zero byte more -/
def oneMore (b : ByteArray) : ByteArray := b ++ zeroBytes 1

def copyItem : ByteArray := item "stored copy" (u64n 7)
def requestBytes708 : ByteArray := item "request" (text (pattern 708))
/-- the fourth item, with its name written out here anew -/
def wordsBytes4104 : ByteArray := item "the request file's words" (text (pattern 4104 9 4))

end ChainStmTest

open ChainStmTest

-- the shape's two tests and the forms hold at these values
#guard shape.count = 256 && shape.ok && shape.fitsWord
#guard table.ok .two shape && stm.ok decl && sealsOk seal1 broot seal2 && stm.request.size = 708 &&
  stm.words.size = 4104
-- `sealsOk`: the first seal of 31 bytes; the root of 33; the second seal of 31
#guard !sealsOk (pattern 31 5 1) broot seal2 && !sealsOk seal1 (pattern 33 11 2) seal2 &&
  !sealsOk seal1 broot (pattern 31 13 3)
-- 2 ^ 40 rows with 2 ^ 30 answers each: the value of such a table's item is too long for a word; no
-- fitsWord, and so no `TableShape.ok`, whose last clause is the same inequality; with 2 ^ 10
-- answers each, all else the same, the shape has both
#guard decide (2 ^ 64 ≤ 48 + 24 * (⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 30, 40⟩ : TableShape).count) &&
  !(⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 30, 40⟩ : TableShape).fitsWord
-- a shape with no answer
#guard !(⟨10, 512, 40, 9, 0, 40⟩ : TableShape).ok && (⟨10, 512, 40, 9, 1, 40⟩ : TableShape).ok
#guard !(⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 30, 40⟩ : TableShape).ok &&
  (⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 10, 40⟩ : TableShape).ok &&
  (⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 10, 40⟩ : TableShape).fitsWord
-- on the bare numbers: the last clause of ProofStm.ok bounds the shared chain's statement too: the
-- greatest count that it admits, with two empty strings; one more is refused
#guard decide (183 + 24 * 768614336404564643 + 0 + 0 < 2 ^ 64) && decide (140 + 24 *
  768614336404564643 < 2 ^ 64) && decide (2 ^ 64 ≤ 183 + 24 * 768614336404564644 + 0 + 0)
#guard table.item.size = 69 + 24 * 256 && (sharedStm table broot).size = 140 + 24 * 256 &&
  (sealItems [seal1, seal2]).size = 152 && stm.bytes.size = 183 + 24 * 256 + 708 + 4104 &&
  (EntryStm.bytes ⟨table, table⟩).size = 160 + 48 * 256

-- a key's one-time chain
#guard TableSt.readItem .two shape (keyStmAt table seal1 broot seal2 .first) = some table
-- another name
#guard TableSt.readItem .two shape (tableItem "the first table" table.root table.answers) = none
-- a name in another case; with a blank more
#guard TableSt.readItem .two shape (tableItem "Table" table.root table.answers) = none &&
  TableSt.readItem .two shape (tableItem "table " table.root table.answers) = none
-- a byte behind; the last byte gone
#guard TableSt.readItem .two shape (oneMore table.item) = none
#guard TableSt.readItem .two shape (cutLast table.item) = none
-- a root of 31 bytes, of 33 bytes
#guard TableSt.readItem .two shape ({ table with root := pattern 31 } : TableSt).item = none
#guard TableSt.readItem .two shape ({ table with root := pattern 33 } : TableSt).item = none
-- the first answer's first word is p, and p - 1
#guard TableSt.readItem .two shape ({ table with answers := (pLast + 1, 1, pLast) ::
  table.answers.tail } : TableSt).item = none
#guard (TableSt.readItem .two shape ({ table with answers := (pLast, 1, pLast) ::
  table.answers.tail } : TableSt).item).isSome
-- the same bytes in the first field, where p is smaller
#guard TableSt.readItem .one shape table.item = none
-- 255 answers under the shape of 256; the same under a shape of 255
#guard TableSt.readItem .two shape ({ table with answers := table.answers.tail } : TableSt).item =
  none
#guard (TableSt.readItem .two { shape with logRows := 0, answers := 255 } ({ table with answers :=
  table.answers.tail } : TableSt).item).isSome
-- a byte behind the list, inside the item's value
#guard TableSt.readItem .two shape (item "table" (oneMore (text table.root ++ list ext
  table.answers))) = none
#guard TableSt.readItem .two shape (item "table" (text table.root ++ list ext table.answers)) =
  some table
-- the list's own word against the answers that follow it: 257 for 256; 255 for 256, under the shape
-- of 256 (the number) and under a shape of 255 (24 bytes are left in the value)
#guard TableSt.readItem .two shape (item "table" (text table.root ++ u64n 257 ++ cat
  (table.answers.map ext))) = none
#guard TableSt.readItem .two shape (item "table" (text table.root ++ u64n 255 ++ cat
  (table.answers.map ext))) = none
#guard TableSt.readItem .two { shape with logRows := 0, answers := 255 } (item "table" (text
  table.root ++ u64n 255 ++ cat (table.answers.map ext))) = none
#guard TableSt.readItem .two shape (item "table" (text table.root ++ u64n 256 ++ cat
  (table.answers.map ext))) = some table
-- the item's word one too small: the value's last byte stands behind the item
#guard TableSt.readItem .two shape (textS "table" ++ u64n (48 + 24 * 256 - 1) ++ (text table.root
  ++ list ext table.answers)) = none
#guard TableSt.readItem .two shape (textS "table" ++ u64n (48 + 24 * 256) ++ (text table.root ++
  list ext table.answers)) = some table

-- a shared chain, of a key and of a proof
#guard rdSharedStm .two shape (keyStmAt table seal1 broot seal2 .shared) = some (table, broot)
#guard rdSharedStm .two shape (proofStmAt stm seal1 broot seal2 .shared) = some (table, broot)
-- the other order; the second item gone; the second item under another name
#guard rdSharedStm .two shape (item bindRootName broot ++ table.item) = none
#guard rdSharedStm .two shape table.item = none
#guard rdSharedStm .two shape (table.item ++ sealItem broot) = none
-- a root of the binding tree of 31 bytes, of 33 bytes; a byte behind
#guard rdSharedStm .two shape (sharedStm table (pattern 31 11 2)) = none
#guard rdSharedStm .two shape (sharedStm table (pattern 33 11 2)) = none
#guard rdSharedStm .two shape (oneMore (sharedStm table broot)) = none
-- the first item's word one too great: the value would take the next item's first byte
#guard rdSharedStm .two shape (textS "table" ++ u64n (48 + 24 * 256 + 1) ++ (text table.root ++
  list ext table.answers) ++ item bindRootName broot) = none

-- a second chain
#guard rdSealItems (keyStmAt table seal1 broot seal2 .second) = some (seal1, seal2)
#guard rdSealItems (proofStmAt stm seal1 broot seal2 .second) = some (seal1, seal2)
-- one seal; three seals
#guard rdSealItems (sealItems [seal1]) = none && rdSealItems (sealItems [seal1, seal2, broot]) =
  none
-- a seal of 31 bytes, of 33 bytes: the second, the first
#guard rdSealItems (sealItems [seal1, pattern 31 13 3]) = none && rdSealItems (sealItems [seal1,
  pattern 33 13 3]) = none && rdSealItems (sealItems [pattern 31 5 1, seal2]) = none && rdSealItems
  (sealItems [pattern 33 5 1, seal2]) = none
-- another name; the last byte gone
#guard rdSealItems (sealItem seal1 ++ item bindRootName seal2) = none
#guard rdSealItems (cutLast (sealItems [seal1, seal2])) = none
-- the order of the seals is kept; the empty string
#guard rdSealItems (sealItems [seal2, seal1]) = some (seal2, seal1) && rdSealItems ByteArray.empty
  = none

-- a proof's first chain
#guard ProofStm.read .two shape (proofStmAt stm seal1 broot seal2 .first) = some (table, 7, pattern
  708, pattern 4104 9 4)
#guard stm.bytes = table.item ++ copyItem ++ requestBytes708 ++ wordsBytes4104 && stm.hashed =
  (table, 7, pattern 708, pattern 4104 9 4)
-- another order; a copy of 2 ^ 32, and of 2 ^ 32 - 1; the request bare, without the word of its
-- length
#guard ProofStm.read .two shape (table.item ++ requestBytes708 ++ copyItem ++ wordsBytes4104) = none
#guard ProofStm.read .two shape (table.item ++ item "stored copy" (u64n (2 ^ 32)) ++
  requestBytes708 ++ wordsBytes4104) = none && ProofStm.read .two shape (table.item ++ item
  "stored copy" (u64n (2 ^ 32 - 1)) ++ requestBytes708 ++ wordsBytes4104) = some (table, 4294967295,
  pattern 708, pattern 4104 9 4)
#guard ProofStm.read .two shape (table.item ++ copyItem ++ item "request" (pattern 708) ++
  wordsBytes4104) = none
-- a byte behind the request inside its item; a byte behind the statement; no statement of another
-- chain
#guard ProofStm.read .two shape (table.item ++ copyItem ++ item "request" (oneMore (text (pattern
  708))) ++ wordsBytes4104) = none && ProofStm.read .two shape (oneMore stm.bytes) = none &&
  ProofStm.read .two shape (sharedStm table broot) = none && TableSt.readItem .two shape stm.bytes =
  none
-- the fourth item: its name, the name's 24 bytes, its length
#guard wordsName = "the request file's words" && (ascii wordsName).size = 24 &&
  wordsBytes4104.size = 48 + 4104
-- without the fourth item; the last two items in each other's places; the fourth item twice; the
-- file's bytes bare, without the word of their length
#guard ProofStm.read .two shape (table.item ++ copyItem ++ requestBytes708) = none &&
  ProofStm.read .two shape (table.item ++ copyItem ++ wordsBytes4104 ++ requestBytes708) = none &&
  ProofStm.read .two shape (stm.bytes ++ wordsBytes4104) = none && ProofStm.read .two shape
  (table.item ++ copyItem ++ requestBytes708 ++ item "the request file's words" (pattern 4104 9 4))
  = none
-- A SWAP: the item "request"'s value and the request file's bytes in each other's fields. Both are
-- strings of bytes, so the types let it pass: the statement's bytes are others, and the reader
-- gives the two back as they were written
#guard ({ stm with request := stm.words, words := stm.request } : ProofStm).bytes != stm.bytes &&
  ProofStm.read .two shape
    ({ stm with request := stm.words, words := stm.request } : ProofStm).bytes =
    some (table, 7, pattern 4104 9 4, pattern 708)

-- the first item's name
#guard [Which.first, .shared, .second].map (fun w => firstName (keyStmAt table seal1 broot seal2
  w)) = [some "table", some "table", some "the seal of an earlier chain"]
#guard [Which.first, .shared, .second].map (fun w => firstName (proofStmAt stm seal1 broot seal2
  w)) = [some "table", some "table", some "the seal of an earlier chain"]

end

/-! # B. Fmt/ChainStm.lean: the page's known answers, the script's values, refusals -/

section
namespace ChainStmKnown

/-- lines 188 to 191: "configuration pattern(32)" -/
def cfgP : ByteArray := pattern 32
/-- "seal pattern(32) with 5 i + 1" -/
def sealP : ByteArray := pattern 32 5 1
/-- "salt pattern(40) with 3 i + 9" -/
def saltP : ByteArray := pattern 40 3 9
/-- "siblings pattern(32) with 11 i + 2 and with 13 i + 4": the first -/
def sibA : ByteArray := pattern 32 11 2
/-- the second; lines 139 to 143 have the same string as a table's root -/
def sibB : ByteArray := pattern 32 13 4
/-- a third string, of this file's: no line of the page has it -/
def sibC : ByteArray := pattern 32 17 6
/-- a second seal, of this file's -/
def seal2P : ByteArray := pattern 32 13 3

/-- the slot of lines 188 to 191 at a place -/
def slotP (p : Nat) : SlotParsed := ⟨UInt64.ofNat p, saltP, [sibA, sibB]⟩

/-- the lowest bit of byte i turned -/
def turn (b : ByteArray) (i : Nat) : ByteArray := b.set! i (byteAt b i ^^^ 1)

/-- line 139: "a = 10, 512 entries, tail 40, 2^9 rows, 1 answer, salt 40" -/
def shapeP : TableShape := ⟨10, 512, 40, 9, 1, 40⟩

/-- A declared structure with that shape and with line 36's one public file, "one file 'toy' and a
line feed". The setting's numbers are the toy plan's (`Toy4.plan`, Fmt/Rules4.lean); no function
under test reads them. No chain. -/
def declP : Declared :=
  { files := [ascii "toy\n"], setting := ⟨.two, 40, 8, 0, 1, 1⟩, table := shapeP }

/-- line 141: "the two answers (1, 2, 3) and (4, 5, 6)" -/
def two : List Ext := [(1, 2, 3), (4, 5, 6)]

/-- Three elements in the place of a record's seeds: a point of two coordinates and a factor. They
are drawn from no name, and under the page's shape they have not the form `seedsOk`. -/
def three : List Ext := [(7, 8, 9), (10, 11, 12), (13, 14, 15)]

/-- `KeyStm.idOkW` at the format's own hash, with no digest at the end -/
def idOk (id : ByteArray) (D : Declared) (cfg : ByteArray) (t : TableSt) (seeds : List Ext) :
    Bool :=
  Id.run ((⟨id⟩ : KeyStm).idOkW hId D cfg t seeds [])

/-- `Declared.seedsW` at the format's own hash -/
def drawn (D : Declared) (cfg : ByteArray) (t : TableSt) : List Ext := Id.run (D.seedsW hId cfg t)

/-- `climbW` at the format's own hash -/
def climb (cfg : ByteArray) (path : List ByteArray) (x : ByteArray) (p : Nat) : ByteArray :=
  Id.run (climbW hId cfg path x p)

/-- a string of 32 bytes that is the ID of none of these tests -/
def idOther : ByteArray := unhex "80d59c8b07aaa71829c9765057082a108618402daf661caf2c390c09dfafddd3"
/-- PAGE 141: the ID at the seeds' elements `three` and the answers `two` -/
def id141 : ByteArray := unhex "4fb918a30faa7643cf8e6bc431c6643d7b5b4cc298dd0531cc0206bb4f756a0b"
/-- PAGE 142: the ID at the seed that is drawn from the name, and the answers `two` -/
def idDrawn : ByteArray :=
  unhex "e18438e0725ec651fc8bffa3b3f860ddeca70e6cb1991dd43620b98ef6f05bd2"

/-- line 184's "the request file's words 05 06 07 08" -/
def wordsP : ByteArray := ⟨#[5, 6, 7, 8]⟩

/-- The last 52 bytes of line 184, in base 16: the fourth item at `wordsP`: the word 24, the name's
24 bytes, the word 12, the word 4, the four bytes. -/
def wordsPHex : String :=
  "180000000000000074686520726571756573742066696c65277320776f7264730c0000000000000004000000000000\
      0005060708"

/-- the page: "the table's root pattern(32), the one answer (1, 2, 3); the copy 1; the request
01 02 03 04; the request file's words 05 06 07 08". The reply is this file's: it is no item of a statement. -/
def stmP : ProofStm := ⟨⟨pattern 32, [(1, 2, 3)]⟩, 1, ⟨#[1, 2, 3, 4]⟩, wordsP, (5, 0, 0)⟩

end ChainStmKnown

open ChainStmKnown

/-! ## 0. The page's "pattern" -/

-- PAGE, the head (line 1): "pattern(n): byte i is (7 i + 3) mod 251; pattern(n) with a i + b: byte
-- i is (a i + b) mod 251", spelled here again over a list, at every pair (a, b) and length used
-- below
#guard [(32, 7, 3), (64, 7, 3), (12, 7, 3), (32, 5, 1), (40, 3, 9), (48, 3, 9), (32, 11, 2), (32,
  13, 4), (32, 13, 3), (32, 17, 6)].all fun (x : Nat × Nat × Nat) => (pattern x.1 x.2.1
  x.2.2).data.toList = (List.range x.1).map fun i => UInt8.ofNat ((x.2.1 * i + x.2.2) % 251)
-- PAGE 184, its bytes 29 to 60 (the root "pattern(32)"); PAGE 143, its bytes 29 to 60 (the root
-- "pattern(32) with 13 i + 4", which passes 251 at i = 19)
#guard hex (pattern 32) = "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc" && hex
  (pattern 32 13 4) = "04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9c"

/-! ## 1. `climbW` -/

-- PAGE 11: "a vertex of the binding tree: H(178, 0, 0, start = pattern(32); pattern(64))". One
-- level. At place 0 the sibling is the right child: the vertex is pattern(64)'s first half
#guard hex (climb (pattern 32) [(pattern 64).extract 32 64] ((pattern 64).extract 0 32) 0) =
  "5060c36d8a53d1f4d4fcce8b2678190f7a3ab70d9a7e09c978a808fb3a01f408"
-- PAGE 11 again: at place 1 the sibling is the left child: the vertex is the second half
#guard hex (climb (pattern 32) [(pattern 64).extract 0 32] ((pattern 64).extract 32 64) 1) =
  "5060c36d8a53d1f4d4fcce8b2678190f7a3ab70d9a7e09c978a808fb3a01f408"
-- SCRIPT: the first test's vertex and sibling at place 1: the halves stand the other way round
#guard hex (climb (pattern 32) [(pattern 64).extract 32 64] ((pattern 64).extract 0 32) 1) =
  "cb96a52eccddc7ca7c3b8cad2e98e0325532764cbdaf767203fe7acdadb381f6"
-- no level: the vertex itself, at any place
#guard climb cfgP [] sealP 0 = sealP && climb cfgP [] sealP 5 = sealP
-- PAGE 188 to 191 for the value; SCRIPT for the vertex from which the climb starts (binding_leaf at
-- depth 2 and that place). The four places take both branches at both levels
#guard [("820c72d6538394747407cee5b61262c892bfbf9c9c4ae77a55a213ae446b79c4", 0),
  ("ab654071b1bd485517a6b9995915505bb58ebf4e97e541a7ee6ee1570eb28f28", 1),
  ("6a90a5a1a648bd84c8a36e5f99c5b540e22b2500dbf01425d84972e65e1f6371", 2),
  ("50c28ab9c2117a1f78b4122e61cb7407ae0e96685fd6f1df65dc85b38de48b68", 3)].map (fun (x : String ×
  Nat) => hex (climb cfgP [sibA, sibB] (unhex x.1) x.2)) =
  ["11849a2d11ba514292eb743d1e64ec3db561ca1f9bcc827f4a42f6dc0d068f4e",
  "dc8b600e35209b9d3d4cbe8d7703cb42866eebbf8fdf55069f5f16e6c929f88f",
  "8867ccb5e2fdefae951fc542ca447b1eff22c42267ddb65eba7f07faced2c7a9",
  "174a65e766c3f047d96c6cc49696f24b1dbdbb88e83063f5a007e31060ef2a0a"]
-- SCRIPT, OUR ORDER: place 0's leaf climbed as from place 1 (the leaf's sibling on the wrong side,
-- the upper one on the right side) and as from place 2 (the upper sibling on the wrong side)
#guard hex (climb cfgP [sibA, sibB] (unhex
  "820c72d6538394747407cee5b61262c892bfbf9c9c4ae77a55a213ae446b79c4") 1) =
  "7c2aca3b8995d99acd8593e5fe0a1c30a70d0a25bb6073f94620b3b9d7247aa3"
#guard hex (climb cfgP [sibA, sibB] (unhex
  "820c72d6538394747407cee5b61262c892bfbf9c9c4ae77a55a213ae446b79c4") 2) =
  "1703a90db89da1b87a984c2c4b2afa054fb796a2606d9ca18aceb87281bd0a3d"

/-! ## 2. `SlotParsed.rootW`, `SlotParsed.root` -/

-- the four slots fit the page's tree (depth 2, salts of 40 bytes: line 187); place 4 does not
#guard (List.range 5).map (fun p => (slotP p).fits ⟨2, 40⟩) = [true, true, true, true, false]
-- PAGE 188, 189, 190, 191: "the binding tree's root: depth 2, place 0 | 1 | 2 | 3, …"
#guard hex ((slotP 0).root 2 cfgP sealP) =
  "11849a2d11ba514292eb743d1e64ec3db561ca1f9bcc827f4a42f6dc0d068f4e"
#guard hex ((slotP 1).root 2 cfgP sealP) =
  "dc8b600e35209b9d3d4cbe8d7703cb42866eebbf8fdf55069f5f16e6c929f88f"
#guard hex ((slotP 2).root 2 cfgP sealP) =
  "8867ccb5e2fdefae951fc542ca447b1eff22c42267ddb65eba7f07faced2c7a9"
#guard hex ((slotP 3).root 2 cfgP sealP) =
  "174a65e766c3f047d96c6cc49696f24b1dbdbb88e83063f5a007e31060ef2a0a"
-- PAGE 188 to 191 again: the same four of `SlotParsed.rootW` at `hId`
#guard (List.range 4).map (fun p => hex (Id.run ((slotP p).rootW hId 2 cfgP sealP))) =
  ["11849a2d11ba514292eb743d1e64ec3db561ca1f9bcc827f4a42f6dc0d068f4e",
  "dc8b600e35209b9d3d4cbe8d7703cb42866eebbf8fdf55069f5f16e6c929f88f",
  "8867ccb5e2fdefae951fc542ca447b1eff22c42267ddb65eba7f07faced2c7a9",
  "174a65e766c3f047d96c6cc49696f24b1dbdbb88e83063f5a007e31060ef2a0a"]
-- PAGE 112: "a binding leaf: depth 2, place 3, that start as the configuration's digest, seal
-- pattern(32), that salt" (line 94: salt pattern(40) with 3 i + 9; start pattern(32) with 5 i + 1).
-- A slot without a sibling does not fit depth 2; root asks no form and gives the leaf
#guard hex ((⟨3, pattern 40 3 9, []⟩ : SlotParsed).root 2 (pattern 32 5 1) (pattern 32)) =
  "0b573addb4922151823d80974c91e8697c33ff51bf4acf7de4ff96434c05ce86" && !(⟨3, pattern 40 3 9, []⟩ :
  SlotParsed).fits ⟨2, 40⟩
-- SCRIPT: depth 0, place 0, as in a key file (R13.6): the leaf is the root
#guard hex ((⟨0, saltP, []⟩ : SlotParsed).root 0 cfgP sealP) =
  "bc5ae2c2e8f9d9132c00655ac03fd8e11daad1a1a75d0088c8fc6cbd3081bb0e" && (⟨0, saltP, []⟩ :
  SlotParsed).fits ⟨0, 40⟩
-- SCRIPT: depth 1, places 0 and 1; depth 3, place 5 (bits 1, 0, 1), with a third sibling
#guard hex ((⟨0, saltP, [sibA]⟩ : SlotParsed).root 1 cfgP sealP) =
  "d1fcb385efcde5ea85b22fe0afbf43ea1b5eccb60c7eba0dcf8a7c8fbc8f0d29"
#guard hex ((⟨1, saltP, [sibA]⟩ : SlotParsed).root 1 cfgP sealP) =
  "58a3233bcb5ed7c4fcba58b91488470b42fcfd1b01afa53c1f224ac77aeafe6f"
#guard hex ((⟨5, saltP, [sibA, sibB, sibC]⟩ : SlotParsed).root 3 cfgP sealP) =
  "49607eb737e5f587e8178348face975a898e4bd1f1c96344925d991e5fab35d8"
-- SCRIPT: line 188 with one thing turned. The siblings in the other order
#guard hex ((⟨0, saltP, [sibB, sibA]⟩ : SlotParsed).root 2 cfgP sealP) =
  "369dbf35461a2fe0373dd118192289fd65e98f4ded8fc053189fe79dbdb0eaa4"
-- SCRIPT: the seal's first byte turned; its last byte
#guard hex ((slotP 0).root 2 cfgP (turn sealP 0)) =
  "ae2fdae9e28eb0ee67b0d8d953065ed68adc77b6f2dc79cf4801fb422ffe9e6b"
#guard hex ((slotP 0).root 2 cfgP (turn sealP 31)) =
  "3677d5025485fe1fecb74d14aae8eafbb320e9026300608c1f69371953bb4e6c"
-- SCRIPT: the salt's last byte turned; a salt of 48 bytes (its number of words is in the hash's
-- label)
#guard hex ((⟨0, turn saltP 39, [sibA, sibB]⟩ : SlotParsed).root 2 cfgP sealP) =
  "f4c5bf8a3f146ba06a4addf9a72d5da80096c59888987aaa85b184a04a801f3c"
#guard hex ((⟨0, pattern 48 3 9, [sibA, sibB]⟩ : SlotParsed).root 2 cfgP sealP) =
  "67cd5dc1d51e5249c921fbf3ab275d8b0374ffaef13a74875422538908135999"
-- SCRIPT: another configuration's digest
#guard hex ((slotP 0).root 2 sibC sealP) =
  "177eae2b2bc4514a71934b91e268ca0e9cda1d48efc7039d55d88b1bc6dc05ac"
-- SCRIPT, OUR ORDER: line 188's slot asked at depth 3: the leaf's index is 2 ^ 3 + 0, the climb has
-- the slot's two levels. The slot does not fit depth 3; root asks no form
#guard hex ((slotP 0).root 3 cfgP sealP) =
  "2e73070af5daa507a4ba472b3921cb0807b6399045081d6f8b65e29fce54a162" && !(slotP 0).fits ⟨3, 40⟩

/-! ## 3. `KeyStm.ok`, `UserStm.keyStm`, `KeyStm.idOkW` -/

-- the form: 32 bytes
#guard KeyStm.ok ⟨idOther⟩ && KeyStm.ok ⟨id141⟩ && !KeyStm.ok ⟨pattern 31⟩ && !KeyStm.ok ⟨pattern 33⟩
  && !KeyStm.ok ⟨ByteArray.empty⟩
-- the caller's ID, and neither of the caller's two other values
#guard (⟨id141, [1, 2, 3], 9⟩ : UserStm).keyStm = ⟨id141⟩ && (⟨idOther, [1, 2, 3], 9⟩ :
  UserStm).keyStm != ⟨id141⟩ && (⟨id141, [], 0⟩ : UserStm).keyStm = (⟨id141, [1, 2, 3], 9⟩ :
  UserStm).keyStm
-- PAGE 139, its bytes 32 to 63: the digest of "the configuration above" (line 36: "one file 'toy'
-- and a line feed") is what the declared files give
#guard hex declP.cfg = "e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f"
-- PAGE 141: "the same with one seed, the point (7, 8, 9), (10, 11, 12) and the factor (13, 14, 15),
-- and the two answers (1, 2, 3) and (4, 5, 6): a test of the coding alone: that name's own seed has
-- 9 coordinates, its table 512 answers"; also by way of the caller's values
#guard idOk id141 declP declP.cfg ⟨sibB, two⟩ three
#guard Id.run ((⟨id141, [1, 2, 3], 9⟩ : UserStm).keyStm.idOkW hId declP declP.cfg ⟨sibB, two⟩ three
  [])
-- PAGE 142: "the same with that name's own seed (R4.8; field 2: 9 coordinates and the factor),
-- sampled and not given, and the two answers (1, 2, 3) and (4, 5, 6)". `Declared.seedsW`,
-- `TableShape.cube`, `recordSeedsW` and `flatSeeds` are held here together, at one value that this
-- library's drawing did not make
#guard idOk idDrawn declP declP.cfg ⟨sibB, two⟩ (drawn declP declP.cfg ⟨sibB, two⟩)
-- each ID at another's table or seeds; line 141's ID with its first byte turned, with its last
#guard !idOk idOther declP declP.cfg ⟨sibB, two⟩ three && !idOk id141 declP declP.cfg ⟨sibB, []⟩ [] &&
  !idOk id141 declP declP.cfg ⟨sibB, two⟩ [] && !idOk id141 declP declP.cfg ⟨sibB, []⟩ three &&
  !idOk id141 declP declP.cfg ⟨sibB, two⟩ (drawn declP declP.cfg ⟨sibB, two⟩) &&
  !idOk idDrawn declP declP.cfg ⟨sibB, two⟩ three
#guard !idOk (turn id141 0) declP declP.cfg ⟨sibB, two⟩ three && !idOk (turn id141 31) declP
  declP.cfg ⟨sibB, two⟩ three
-- SCRIPT: line 141 with one thing turned: the new ID is told, line 141's is not. The two
-- answers in the other order
#guard idOk (unhex "82d662bf554545bc6f3d561511d81f7efd103cc8a4df73d6787efe3eb5c6e1d7") declP
  declP.cfg ⟨sibB, two.reverse⟩ three && !idOk id141 declP declP.cfg ⟨sibB, two.reverse⟩ three
-- SCRIPT: the seeds' elements in the other order
#guard idOk (unhex "b2e15ffb7bdcd3b37a6a67a8d88e8da7fc10b9f86531f4aa50704d79965a8b7e") declP
  declP.cfg ⟨sibB, two⟩ three.reverse && !idOk id141 declP declP.cfg ⟨sibB, two⟩ three.reverse
-- SCRIPT: A SWAP: the seeds' elements and the answers in each other's places. Both are lists
-- of elements, so the types let it pass: another ID
#guard idOk (unhex "dbd5e46591f311f661d76c8b3016ab7c0e41713d8ea244c06d66eb9a015cb71d") declP
  declP.cfg ⟨sibB, three⟩ two && !idOk id141 declP declP.cfg ⟨sibB, three⟩ two
-- SCRIPT: the seeds' last element as the first answer: the same five elements in the same
-- order, and the two words of the lists' numbers are others
#guard idOk (unhex "508fefa3bc52bc9796ec859fd8a7f680d92704bcb5411c5a50c2fb6ce4124084") declP
  declP.cfg ⟨sibB, (13, 14, 15) :: two⟩ (three.take 2) && !idOk id141 declP declP.cfg
  ⟨sibB, (13, 14, 15) :: two⟩ (three.take 2)
-- SCRIPT, OUR ORDER: one digest at the end. The format defines no element of that last list
-- (R4.11): this holds the library's own typing of it, not the format
#guard Id.run ((⟨unhex "4c8f647e061bdec97b7d94713be7502a78e1dc47c7f382aaeb9a0915a821a7e9"⟩ :
  KeyStm).idOkW hId declP declP.cfg ⟨sibB, two⟩ three [sibA]) &&
  !Id.run ((⟨id141⟩ : KeyStm).idOkW hId declP declP.cfg ⟨sibB, two⟩ three [sibA])
-- SCRIPT: another root
#guard idOk (unhex "36168db306645b85ecf3609022f18bd3a4e08bc8c94079986c6b96e08cecc7cf") declP
  declP.cfg ⟨sibA, two⟩ three && !idOk id141 declP declP.cfg ⟨sibA, two⟩ three
-- SCRIPT: a shape of six distinct words (the page's has 40 twice); the same with the third
-- and the sixth changed over; neither ID at the other's shape
#guard idOk (unhex "557faeb911826a6a64ccd19e1f9a4e046f72365c912c2cc41867a70753b0ef87") { declP
  with table := ⟨10, 512, 41, 9, 1, 48⟩ } declP.cfg ⟨sibB, two⟩ three && idOk (unhex
  "2cc8dfc99e4e26c67057672770c729331590a9068ecb236a7abd8aaed5db8529") { declP with table := ⟨10,
  512, 48, 9, 1, 41⟩ } declP.cfg ⟨sibB, two⟩ three
#guard !idOk (unhex "557faeb911826a6a64ccd19e1f9a4e046f72365c912c2cc41867a70753b0ef87") { declP
  with table := ⟨10, 512, 48, 9, 1, 41⟩ } declP.cfg ⟨sibB, two⟩ three && !idOk id141 { declP with
  table := ⟨10, 512, 41, 9, 1, 48⟩ } declP.cfg ⟨sibB, two⟩ three
-- SCRIPT: another digest, pattern(32), in both of its places (in front, and in the name:
-- R4.11)
#guard idOk (unhex "739f6fee4c3eb51345b53ab1c62d7638b9bf6dd3afb9481669741d61f183269f") declP cfgP
  ⟨sibB, two⟩ three && !idOk id141 declP cfgP ⟨sibB, two⟩ three
-- SCRIPT: the ID of a string with pattern(32) in front and the toy's digest in the name is
-- told at neither digest: the function puts one digest into both places
#guard hex (publishedID cfgP (declP.table.name declP.cfg sibB) three two []) =
    "c09f61d0397d724470b5f43885ec4737929555fbe9ef04e80b97c44acc31cf56" &&
  !idOk (unhex "c09f61d0397d724470b5f43885ec4737929555fbe9ef04e80b97c44acc31cf56") declP cfgP
  ⟨sibB, two⟩ three &&
  !idOk (unhex "c09f61d0397d724470b5f43885ec4737929555fbe9ef04e80b97c44acc31cf56") declP declP.cfg
    ⟨sibB, two⟩ three

/-! ## 3a. `TableShape.cube`, `seedsOk`, `toldOk`, `Declared.seedsW` -/

-- the least c with 2 ^ c not below the number of a message's entries
#guard [0, 1, 2, 3, 4, 5, 512, 513].map (fun n => ({ shapeP with message := n } : TableShape).cube)
  = [0, 0, 1, 2, 2, 3, 9, 10]
-- what is drawn at the page's shape: ten elements, with the form; it is what the library's
-- other function at the format's own hash gives from the name (`Known56.recordSeeds`,
-- Fmt/Rules56Known.lean), laid flat
#guard (drawn declP declP.cfg ⟨sibB, two⟩).length = 10 &&
  seedsOk .two shapeP (drawn declP declP.cfg ⟨sibB, two⟩) &&
  some (drawn declP declP.cfg ⟨sibB, two⟩) =
    (Known56.recordSeeds .two (recordStm declP declP.cfg ⟨sibB, two⟩) 9 1).map flatSeeds
-- of the table the drawing reads the root alone; another root, another digest, another shape:
-- other seeds
#guard drawn declP declP.cfg ⟨sibB, []⟩ = drawn declP declP.cfg ⟨sibB, two⟩ &&
  drawn declP declP.cfg ⟨sibA, two⟩ != drawn declP declP.cfg ⟨sibB, two⟩ &&
  drawn declP cfgP ⟨sibB, two⟩ != drawn declP declP.cfg ⟨sibB, two⟩ &&
  drawn { declP with table := { shapeP with tail := 41 } } declP.cfg ⟨sibB, two⟩ !=
    drawn declP declP.cfg ⟨sibB, two⟩
-- the field is the declared one: in the first field other elements, as many
#guard drawn { declP with setting := ⟨.one, 40, 8, 0, 1, 1⟩ } declP.cfg ⟨sibB, two⟩ !=
    drawn declP declP.cfg ⟨sibB, two⟩ &&
  (drawn { declP with setting := ⟨.one, 40, 8, 0, 1, 1⟩ } declP.cfg ⟨sibB, two⟩).length = 10
-- two answers to a row: two seeds, twenty elements, with the form
#guard (drawn { declP with table := { shapeP with answers := 2 } } declP.cfg ⟨sibB, two⟩).length =
    20 &&
  seedsOk .two { shapeP with answers := 2 }
    (drawn { declP with table := { shapeP with answers := 2 } } declP.cfg ⟨sibB, two⟩)
-- `seedsOk` refuses: three elements, none, one too few, one too many, under a shape that says ten;
-- an element whose first word is p (and takes p - 1)
#guard !seedsOk .two shapeP three && !seedsOk .two shapeP [] &&
  !seedsOk .two shapeP (drawn declP declP.cfg ⟨sibB, two⟩).tail &&
  !seedsOk .two shapeP ((1, 2, 3) :: drawn declP declP.cfg ⟨sibB, two⟩) &&
  !seedsOk .two shapeP ((18446744069414584321, 0, 0) :: (drawn declP declP.cfg ⟨sibB, two⟩).tail) &&
  seedsOk .two shapeP ((18446744069414584320, 0, 0) :: (drawn declP declP.cfg ⟨sibB, two⟩).tail)
-- `toldOk`: 32 bytes each
#guard toldOk [] && toldOk [sibA, sibB] && !toldOk [sibA, pattern 31] && !toldOk [pattern 33] &&
  !toldOk [ByteArray.empty]

/-! ## 4. `recordStm` -/

-- PAGE 139: "root pattern(32) with 13 i + 4, the configuration above, a = 10, 512 entries, tail 40,
-- 2^9 rows, 1 answer, salt 40": a stored table's name, 112 bytes. That the name is the statement of
-- the chain of the record's seeds is R4.8's word
#guard hex (recordStm declP declP.cfg ⟨sibB, []⟩) =
  "04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9ce7b508817ead50bb3f386f68d442b114\
      119e93e8ef2b14a7d70190075348db5f0a00000000000000000200000000000028000000000000000900000000000\
      00001000000000000002800000000000000" && (recordStm declP declP.cfg ⟨sibB, []⟩).size = 112
-- the answers are not in the name (R4.10)
#guard recordStm declP declP.cfg ⟨sibB, two⟩ = recordStm declP declP.cfg ⟨sibB, []⟩
-- SCRIPT: six distinct words; the third and the sixth changed over
#guard hex (recordStm { declP with table := ⟨10, 512, 41, 9, 1, 48⟩ } declP.cfg ⟨sibB, []⟩) =
  "04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9ce7b508817ead50bb3f386f68d442b114\
      119e93e8ef2b14a7d70190075348db5f0a00000000000000000200000000000029000000000000000900000000000\
      00001000000000000003000000000000000"
#guard hex (recordStm { declP with table := ⟨10, 512, 48, 9, 1, 41⟩ } declP.cfg ⟨sibB, []⟩) =
  "04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9ce7b508817ead50bb3f386f68d442b114\
      119e93e8ef2b14a7d70190075348db5f0a00000000000000000200000000000030000000000000000900000000000\
      00001000000000000002900000000000000"
-- PAGE 36, 37: "record seed of the name with root pattern(32) with 13 i + 4, the configuration of
-- one file 'toy' and a line feed, a = 10, 3 entries, tail 40, 2^9 rows, 1 answer, salt 40; two
-- coordinates: the point"; "the same: the factor". The chain is the library's
-- (`Known56.recordSeeds`, Fmt/Rules56Known.lean); its statement is ours
#guard Known56.recordSeeds .two (recordStm { declP with table := ⟨10, 3, 40, 9, 1, 40⟩ } declP.cfg
  ⟨sibB, []⟩) 2 1 = some [([(9697749137137958355, 613613959841214928, 8403959380172774020),
  (15526148976690303146, 2032215208828410348, 4053187377642565227)], (14917727018641805655,
  3966560771581124203, 17230899846445233913))]
-- another root: other seeds
#guard Known56.recordSeeds .two (recordStm { declP with table := ⟨10, 3, 40, 9, 1, 40⟩ } declP.cfg
  ⟨sibA, []⟩) 2 1 != some [([(9697749137137958355, 613613959841214928, 8403959380172774020),
  (15526148976690303146, 2032215208828410348, 4053187377642565227)], (14917727018641805655,
  3966560771581124203, 17230899846445233913))]

/-! ## 5. `keyStmAt` -/

-- The page: "the item named 'table' of a table with that root and the one answer (1, 2, 3)": a
-- one-time chain's statement (R13.5)
#guard hex (keyStmAt ⟨sibB, [(1, 2, 3)]⟩ sealP sibA seal2P .first) =
  "05000000000000007461626c654800000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1\
      ee000d1a2734414e5b6875828f9c0100000000000000010000000000000002000000000000000300000000000000"
-- SCRIPT: with line 141's two answers: 117 bytes
#guard hex (keyStmAt ⟨sibB, two⟩ sealP sibA seal2P .first) =
  "05000000000000007461626c656000000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1ee\
      000d1a2734414e5b6875828f9c0200000000000000010000000000000002000000000000000300000000000000040\
      000000000000005000000000000000600000000000000"
-- SCRIPT, OUR ORDER: the shared chain: "table", then "the binding tree's root": with the two
-- answers (188 bytes)
#guard hex (keyStmAt ⟨sibB, two⟩ sealP sibA seal2P .shared) =
  "05000000000000007461626c656000000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1ee\
      000d1a2734414e5b6875828f9c0200000000000000010000000000000002000000000000000300000000000000040\
      00000000000000500000000000000060000000000000017000000000000007468652062696e64696e672074726565\
      277320726f6f742000000000000000020d18232e39444f5a65707b86919ca7b2bdc8d3dee9f4040f1a25303b46515\
      c"
-- SCRIPT, OUR ORDER: the second chain: the one-time chain's seal, then the shared chain's; and with
-- the two changed over
#guard hex (keyStmAt ⟨sibB, two⟩ sealP sibA seal2P .second) =
  "1c00000000000000746865207365616c206f6620616e206561726c69657220636861696e200000000000000001060b10\
      151a1f24292e33383d42474c51565b60656a6f74797e83888d92979c1c00000000000000746865207365616c206f6\
      620616e206561726c69657220636861696e200000000000000003101d2a3744515e6b7885929facb9c6d3e0edfa0c\
      192633404d5a6774818e9b"
#guard hex (keyStmAt ⟨sibB, two⟩ seal2P sibA sealP .second) =
  "1c00000000000000746865207365616c206f6620616e206561726c69657220636861696e200000000000000003101d2a\
      3744515e6b7885929facb9c6d3e0edfa0c192633404d5a6774818e9b1c00000000000000746865207365616c206f6\
      620616e206561726c69657220636861696e200000000000000001060b10151a1f24292e33383d42474c51565b6065\
      6a6f74797e83888d92979c"

/-! ## 6. `proofStmAt` -/

-- The page: "the statement of its first chain: the table's root pattern(32), the one answer
-- (1, 2, 3); the copy 1;
-- the request 01 02 03 04; the request file's words 05 06 07 08". Its last 52 bytes are written
-- once, as `wordsPHex`; so in the tests under SCRIPT of this block and of block 8, all at these
-- four bytes for the request file's
#guard hex (proofStmAt stmP sealP sibA seal2P .first) =
  "05000000000000007461626c6548000000000000002000000000000000030a11181f262d343b424950575e656c737a\
      81888f969da4abb2b9c0c7ced5dc0100000000000000010000000000000002000000000000000300000000000000\
      0b0000000000000073746f72656420636f7079080000000000000001000000000000000700000000000000726571\
      756573740c00000000000000040000000000000001020304" ++
  wordsPHex
-- the reply is no item (R14.8): another reply, the same bytes
#guard proofStmAt { stmP with reply := (6, 0, 0) } sealP sibA seal2P .first = proofStmAt stmP sealP
  sibA seal2P .first
-- SCRIPT: line 184 with one thing turned: the copy 2; the request's last byte 05
#guard hex (proofStmAt { stmP with copy := 2 } sealP sibA seal2P .first) =
  "05000000000000007461626c6548000000000000002000000000000000030a11181f262d343b424950575e656c737a\
      81888f969da4abb2b9c0c7ced5dc0100000000000000010000000000000002000000000000000300000000000000\
      0b0000000000000073746f72656420636f7079080000000000000002000000000000000700000000000000726571\
      756573740c00000000000000040000000000000001020304" ++
  wordsPHex
#guard hex (proofStmAt { stmP with request := ⟨#[1, 2, 3, 5]⟩ } sealP sibA seal2P .first) =
  "05000000000000007461626c6548000000000000002000000000000000030a11181f262d343b424950575e656c737a\
      81888f969da4abb2b9c0c7ced5dc0100000000000000010000000000000002000000000000000300000000000000\
      0b0000000000000073746f72656420636f7079080000000000000001000000000000000700000000000000726571\
      756573740c00000000000000040000000000000001020305" ++
  wordsPHex
-- SCRIPT: the copy 0 and an empty request; two answers, the greatest copy 2 ^ 32 - 1, a request of
-- 12 bytes
#guard hex (proofStmAt { stmP with copy := 0, request := ByteArray.empty } sealP sibA seal2P
  .first) =
  "05000000000000007461626c6548000000000000002000000000000000030a11181f262d343b424950575e656c737a\
      81888f969da4abb2b9c0c7ced5dc0100000000000000010000000000000002000000000000000300000000000000\
      0b0000000000000073746f72656420636f7079080000000000000000000000000000000700000000000000726571\
      7565737408000000000000000000000000000000" ++
  wordsPHex
#guard hex (proofStmAt ⟨⟨sibB, two⟩, 4294967295, pattern 12, wordsP, (5, 0, 0)⟩ sealP sibA seal2P
  .first) =
  "05000000000000007461626c656000000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1ee\
      000d1a2734414e5b6875828f9c0200000000000000010000000000000002000000000000000300000000000000040\
      0000000000000050000000000000006000000000000000b0000000000000073746f72656420636f70790800000000\
      000000ffffffff0000000007000000000000007265717565737414000000000000000c00000000000000030a11181\
      f262d343b424950" ++
  wordsPHex
-- SCRIPT, OUR ORDER: the shared chain and the second chain: the same strings as a key's (R14.9,
-- R14.10)
#guard hex (proofStmAt ⟨⟨sibB, two⟩, 1, pattern 12, wordsP, (5, 0, 0)⟩ sealP sibA seal2P .shared) =
  "05000000000000007461626c656000000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1ee\
      000d1a2734414e5b6875828f9c0200000000000000010000000000000002000000000000000300000000000000040\
      00000000000000500000000000000060000000000000017000000000000007468652062696e64696e672074726565\
      277320726f6f742000000000000000020d18232e39444f5a65707b86919ca7b2bdc8d3dee9f4040f1a25303b46515\
      c"
#guard hex (proofStmAt ⟨⟨sibB, two⟩, 1, pattern 12, wordsP, (5, 0, 0)⟩ sealP sibA seal2P .second) =
  "1c00000000000000746865207365616c206f6620616e206561726c69657220636861696e200000000000000001060b10\
      151a1f24292e33383d42474c51565b60656a6f74797e83888d92979c1c00000000000000746865207365616c206f6\
      620616e206561726c69657220636861696e200000000000000003101d2a3744515e6b7885929facb9c6d3e0edfa0c\
      192633404d5a6774818e9b"
#guard hex (proofStmAt ⟨⟨sibB, two⟩, 1, pattern 12, wordsP, (5, 0, 0)⟩ seal2P sibA sealP .second) =
  "1c00000000000000746865207365616c206f6620616e206561726c69657220636861696e200000000000000003101d2a\
      3744515e6b7885929facb9c6d3e0edfa0c192633404d5a6774818e9b1c00000000000000746865207365616c206f6\
      620616e206561726c69657220636861696e200000000000000001060b10151a1f24292e33383d42474c51565b6065\
      6a6f74797e83888d92979c"

/-! ## 7. Two readers of Fmt/ChainStmRead.lean at the page's own bytes -/

-- PAGE 143 and PAGE 184 under the page's shape itself, which says 512 answers: both are refused
#guard TableSt.readItem .two shapeP (unhex
  "05000000000000007461626c653000000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1ee\
      000d1a2734414e5b6875828f9c0000000000000000") = none &&
  ProofStm.read .two shapeP (unhex ("0500\
      0000000000007461626c6530000000000000002000000000000000030a11181f262d343b424950575e656c737a818\
      88f969da4abb2b9c0c7ced5dc00000000000000000b0000000000000073746f72656420636f707908000000000000\
      0001000000000000000700000000000000726571756573740c00000000000000040000000000000001020304\
      " ++ wordsPHex)) = none

/-! ## 8. The closed forms -/

namespace ChainStmKnown

/-- the page's shape with 2 ^ 1 rows: two answers -/
def shapeC : TableShape := ⟨10, 512, 40, 1, 1, 40⟩

/-- the parameter item "binding tree" (R13.5, R14.6): two words, the depth and the bytes of a salt
-/
def bindItem (depth salt : Nat) : String × ByteArray := ("binding tree", u64n depth ++ u64n salt)

/-- a chain of which the parameter items behind "configuration" alone are set -/
def chainOf (others : List (String × ByteArray)) : ChainDecl :=
  { (default : ChainDecl) with others := others }

/-- `declP` with that shape, and with these parameter items in the first chain of a key and of a
proof. All else of the chains is the type's default: the closed forms read nothing else of them. -/
def declAt (key proof : List (String × ByteArray)) : Declared :=
  { declP with
    table := shapeC
    key := { (default : ThreeDecl) with first := chainOf key }
    proof := { (default : ThreeDecl) with first := chainOf proof } }

/-- a key's binding tree of depth 0 and a proof's of depth 2 (line 187: "depth 2, salts of 40
bytes") -/
def declC : Declared := declAt [bindItem 0 40] [bindItem 2 40]

/-- `declC` with other numbers in the two fields `ThreeDecl.bind` -/
def declB : Declared :=
  { declC with
    key := { declC.key with bind := ⟨5, 48⟩ }
    proof := { declC.proof with bind := ⟨7, 64⟩ } }

/-- 48 and 49 digests for a deep path: digest i is pattern(32) with (i + 1) j + 2 -/
def deep (n : Nat) : List ByteArray := (List.range n).map fun i => pattern 32 (i + 1) 2

def tableC : TableSt := ⟨sibB, two⟩

/-- a key file of which the table and the slot are set; the closed forms read nothing else -/
def keyC : KeyParsed := { (default : KeyParsed) with table := tableC, slot := ⟨0, saltP, []⟩ }

def stmC : ProofStm := ⟨tableC, 1, ⟨#[1, 2, 3, 4]⟩, wordsP, (5, 0, 0)⟩

/-- a proof file of which the head's number and the slot are set; the closed forms read nothing else
-/
def proofC (s : SlotParsed) : ProofParsed := { (default : ProofParsed) with copy := 1, slot := s }

/-- The format's own hash, but under the number 169 (the configuration's digest, R4.9; the closed
forms make no other call under it) it answers pattern(32). Lines 188 to 191 take pattern(32) as the
configuration's digest, which is the digest of no known files; a closed form computes the digest
from the declared files. Under this stand-in it can be held at the page's four roots. -/
def hPage : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray :=
  fun n t i s b => if n == 169 then pure cfgP else hId n t i s b

/-- The format's own hash, which writes down each call's number, index and number of bytes. (A tool
like `RequestItemTest.noted`, Fmt/TestRequestItem.lean, which is for a hash of two arguments.) -/
def hNoted (n t i : Nat) (s b : ByteArray) : StateM (List (Nat × Nat × Nat)) ByteArray := do
  modify (· ++ [(n, i, b.size)])
  pure (formatHash n t i s b)

/-- the calls that were written down -/
def callsOf {α : Type} (x : StateM (List (Nat × Nat × Nat)) α) : List (Nat × Nat × Nat) :=
  (Id.run (x.run [])).2

/-- the value beside them -/
def valueOf {α : Type} (x : StateM (List (Nat × Nat × Nat)) α) : α := (Id.run (x.run [])).1

/-- a hash that answers every call with the same n bytes -/
def hConst (n : Nat) : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray :=
  fun _ _ _ _ _ => pure (pattern n)

/-- The format's own hash, but under the number 160 (a chain's first value; of the functions under
test here `Declared.seedsW` alone calls it) it answers 31 bytes. -/
def hShort : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray :=
  fun n t i s b => if n == 160 then pure (pattern 31) else hId n t i s b

/-- which of the three statements are something -/
def keySome (D : Declared) (F : KeyParsed) (s1 s2 : ByteArray) : List Bool :=
  [Which.first, .shared, .second].map fun w => (F.stmAt D s1 s2 w).isSome

def proofSome (D : Declared) (x : ProofStm) (F : ProofParsed) (s1 s2 : ByteArray) : List Bool :=
  [Which.first, .shared, .second].map fun w => (F.stmAt D x s1 s2 w).isSome

/-- Slots that differ from `slotP 0` in one thing each: the place 2 ^ 2; a salt one byte short, one
byte long; a path one digest short, one long; the upper sibling of 31 bytes, the lower of 33. -/
def badSlots : List SlotParsed :=
  [slotP 4, ⟨0, pattern 39 3 9, [sibA, sibB]⟩, ⟨0, pattern 41 3 9, [sibA, sibB]⟩,
    ⟨0, saltP, [sibA]⟩, ⟨0, saltP, [sibA, sibB, sibC]⟩, ⟨0, saltP, [sibA, pattern 31 13 4]⟩,
    ⟨0, saltP, [pattern 33 11 2, sibB]⟩]

/-- Slots that differ from a key's slot ⟨0, saltP, []⟩ in one thing each: the place 2 ^ 0; a salt
one byte short; a path one digest long. -/
def badKeySlots : List SlotParsed := [⟨1, saltP, []⟩, ⟨0, pattern 39 3 9, []⟩, ⟨0, saltP, [sibA]⟩]

end ChainStmKnown

-- the values have the forms that the closed forms ask
#guard shapeC.count = 2 && shapeC.fitsWord && tableC.ok .two shapeC && stmC.ok declC && (proofC
  (slotP 0)).copyFits stmC && keyC.slot.fits ⟨0, 40⟩ && (slotP 0).fits ⟨2, 40⟩ &&
  declC.cfg = declP.cfg
-- the declared structure is made up: it passes neither of the tests on a key's and a proof's chains
#guard !declC.keyFormOk && !declC.proofFormOk

-- A KEY FILE, accepted. SCRIPT: the one-time chain's statement. SCRIPT, OUR ORDER: the second
-- chain's
#guard (keyC.stmAt declC sealP seal2P .first).map hex = some
  "05000000000000007461626c656000000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1ee\
      000d1a2734414e5b6875828f9c0200000000000000010000000000000002000000000000000300000000000000040\
      000000000000005000000000000000600000000000000"
#guard (keyC.stmAt declC sealP seal2P .second).map hex = some
  "1c00000000000000746865207365616c206f6620616e206561726c69657220636861696e200000000000000001060b10\
      151a1f24292e33383d42474c51565b60656a6f74797e83888d92979c1c00000000000000746865207365616c206f6\
      620616e206561726c69657220636861696e200000000000000003101d2a3744515e6b7885929facb9c6d3e0edfa0c\
      192633404d5a6774818e9b"
-- the shared chain's: the open form at the root that the file's slot, the first seal and the
-- declared files' digest give at depth 0
#guard keyC.stmAt declC sealP seal2P .shared = some (keyStmAt tableC sealP (keyC.slot.root 0
  declC.cfg sealP) seal2P .shared)
-- SCRIPT for the root (depth 0, configuration pattern(32)), under `hPage`
#guard Id.run (keyC.stmAtW hPage declC sealP seal2P .shared) = some (sharedStm tableC (unhex
  "bc5ae2c2e8f9d9132c00655ac03fd8e11daad1a1a75d0088c8fc6cbd3081bb0e"))
-- the three parts by their own names
#guard keyC.firstStm declC = keyC.stmAt declC sealP seal2P .first && Id.run (keyC.sharedStmW hId
  declC sealP) = keyC.stmAt declC sealP seal2P .shared && secondStm sealP seal2P = keyC.stmAt declC
  sealP seal2P .second && Id.run (sharedStmOfW hId declC ⟨0, 40⟩ tableC ⟨0, saltP, []⟩ sealP) =
  keyC.stmAt declC sealP seal2P .shared

-- A PROOF FILE, accepted. SCRIPT: the first chain's statement. SCRIPT, OUR ORDER: the second
-- chain's
#guard ((proofC (slotP 0)).stmAt declC stmC sealP seal2P .first).map hex = some (
  "05000000000000007461626c656000000000000000200000000000000004111e2b3845525f6c798693a0adbac7d4e1ee\
      000d1a2734414e5b6875828f9c0200000000000000010000000000000002000000000000000300000000000000040\
      0000000000000050000000000000006000000000000000b0000000000000073746f72656420636f70790800000000\
      00000001000000000000000700000000000000726571756573740c0000000000000004000000000000000102030\
      4" ++ wordsPHex)
#guard ((proofC (slotP 0)).stmAt declC stmC sealP seal2P .second).map hex = some
  "1c00000000000000746865207365616c206f6620616e206561726c69657220636861696e200000000000000001060b10\
      151a1f24292e33383d42474c51565b60656a6f74797e83888d92979c1c00000000000000746865207365616c206f6\
      620616e206561726c69657220636861696e200000000000000003101d2a3744515e6b7885929facb9c6d3e0edfa0c\
      192633404d5a6774818e9b"
-- the shared chain's, at the four places: the open form at the root that the slot, the first seal
-- and the declared files' digest give at depth 2
#guard (List.range 4).all fun p => (proofC (slotP p)).stmAt declC stmC sealP seal2P .shared = some
  (proofStmAt stmC sealP ((slotP p).root 2 declC.cfg sealP) seal2P .shared)
-- PAGE 188 to 191 for the root, under `hPage`
#guard (List.range 4).map (fun p => Id.run ((proofC (slotP p)).stmAtW hPage declC stmC sealP seal2P
  .shared)) = ["11849a2d11ba514292eb743d1e64ec3db561ca1f9bcc827f4a42f6dc0d068f4e",
  "dc8b600e35209b9d3d4cbe8d7703cb42866eebbf8fdf55069f5f16e6c929f88f",
  "8867ccb5e2fdefae951fc542ca447b1eff22c42267ddb65eba7f07faced2c7a9",
  "174a65e766c3f047d96c6cc49696f24b1dbdbb88e83063f5a007e31060ef2a0a"].map fun r => some (sharedStm
  tableC (unhex r))
-- the parts by their own names
#guard (proofC (slotP 0)).firstStm declC stmC = (proofC (slotP 0)).stmAt declC stmC sealP seal2P
  .first && Id.run ((proofC (slotP 0)).sharedStmW hId declC stmC sealP) = (proofC (slotP 0)).stmAt
  declC stmC sealP seal2P .shared && Id.run (sharedStmOfW hId declC ⟨2, 40⟩ tableC (slotP 0) sealP)
  = (proofC (slotP 0)).stmAt declC stmC sealP seal2P .shared

-- WHAT EACH STATEMENT HANGS ON. SCRIPT for the root, under `hPage`: the first seal's first byte
-- turned: another shared statement
#guard Id.run ((proofC (slotP 0)).stmAtW hPage declC stmC (turn sealP 0) seal2P .shared) = some
  (sharedStm tableC (unhex "ae2fdae9e28eb0ee67b0d8d953065ed68adc77b6f2dc79cf4801fb422ffe9e6b"))
#guard (proofC (slotP 0)).stmAt declC stmC (turn sealP 0) seal2P .shared != (proofC (slotP
  0)).stmAt declC stmC sealP seal2P .shared && keyC.stmAt declC (turn sealP 0) seal2P .shared !=
  keyC.stmAt declC sealP seal2P .shared
-- the first statement hangs on no seal, the shared one not on the second: handed empty strings
#guard (proofC (slotP 0)).stmAt declC stmC ByteArray.empty ByteArray.empty .first = (proofC (slotP
  0)).stmAt declC stmC sealP seal2P .first && keyC.stmAt declC ByteArray.empty ByteArray.empty
  .first = keyC.stmAt declC sealP seal2P .first
#guard (proofC (slotP 0)).stmAt declC stmC sealP ByteArray.empty .shared = (proofC (slotP 0)).stmAt
  declC stmC sealP seal2P .shared && keyC.stmAt declC sealP ByteArray.empty .shared = keyC.stmAt
  declC sealP seal2P .shared

-- REFUSED. All three are something at the accepted values
#guard keySome declC keyC sealP seal2P = [true, true, true] && proofSome declC stmC (proofC (slotP
  0)) sealP seal2P = [true, true, true]
-- a slot without the declared form (`badSlots`, `badKeySlots`: one thing each): the shared
-- statement alone is nothing
#guard badSlots.map (fun s => proofSome declC stmC (proofC s) sealP seal2P) = List.replicate 7
  [true, false, true]
#guard badKeySlots.map (fun s => keySome declC { keyC with slot := s } sealP seal2P) =
  List.replicate 3 [true, false, true]
-- the first seal of 31 bytes, of 33: the shared and the second are nothing; the second seal of 31
-- bytes: the second alone
#guard [pattern 31 5 1, pattern 33 5 1].map (fun s => (proofSome declC stmC (proofC (slotP 0)) s
  seal2P, keySome declC keyC s seal2P)) = List.replicate 2 ([true, false, false], [true, false,
  false])
#guard proofSome declC stmC (proofC (slotP 0)) sealP (pattern 31 13 3) = [true, true, false] &&
  keySome declC keyC sealP (pattern 31 13 3) = [true, true, false]
-- a table with one answer where the shape says two; with a root of 31 bytes; with an answer that is
-- not canonical (its first word is the field's p): the first and the shared are nothing
#guard [⟨sibB, [(1, 2, 3)]⟩, ⟨pattern 31 13 4, two⟩, ⟨sibB, [(18446744069414584321, 2, 3), (4, 5,
  6)]⟩].map (fun (t : TableSt) => (proofSome declC { stmC with table := t } (proofC (slotP 0))
  sealP seal2P, keySome declC { keyC with table := t } sealP seal2P)) = List.replicate 3 ([false,
  false, true], [false, false, true])
-- a proof: the head's number is not the outer statement's (R14.2); the reply is not canonical
#guard proofSome declC stmC { proofC (slotP 0) with copy := 2 } sealP seal2P = [false, false, true]
#guard proofSome declC { stmC with reply := (18446744069414584321, 0, 0) } (proofC (slotP 0)) sealP
  seal2P = [false, false, true]
-- A shape without `TableShape.fitsWord`: the first and the shared are nothing. THIS TEST DOES NOT
-- REACH THAT CLAUSE ALONE: the shape says 2 ^ 70 answers, no table of that form can be made here,
-- so `TableSt.ok` fails too. No #guard can tell whether the closed forms ask `TableShape.fitsWord`
#guard !(⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 30, 40⟩ : TableShape).fitsWord && proofSome { declC with table
  := ⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 30, 40⟩ } stmC (proofC (slotP 0)) sealP seal2P = [false, false,
  true] && keySome { declC with table := ⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 30, 40⟩ } keyC sealP seal2P =
  [false, false, true]
-- a hash whose answers have 31 bytes: the root has not 32, and the shared statement is nothing; at
-- 32 bytes it is something
#guard Id.run (keyC.stmAtW (hConst 31) declC sealP seal2P .shared) = none && Id.run (keyC.stmAtW
  (hConst 32) declC sealP seal2P .shared) = some (sharedStm tableC (pattern 32))

-- THE CALLS OF THE HASH (number, index, bytes). A key's shared statement: the configuration's
-- digest (169, index 2; 8 + 8 + 4 bytes), the leaf (173, index 2 ^ 0 + 0; 32 + 40 bytes). A proof's
-- at place 1: the digest, the leaf (index 2 ^ 2 + 1), two vertices (178; 64 bytes)
#guard callsOf (keyC.stmAtW hNoted declC sealP seal2P .shared) = [(169, 2, 20), (173, 1, 72)]
#guard callsOf ((proofC (slotP 1)).stmAtW hNoted declC stmC sealP seal2P .shared) = [(169, 2, 20),
  (173, 5, 72), (178, 0, 64), (178, 0, 64)]
-- the values beside them are those at `hId`
#guard valueOf (keyC.stmAtW hNoted declC sealP seal2P .shared) = keyC.stmAt declC sealP seal2P
  .shared && valueOf ((proofC (slotP 1)).stmAtW hNoted declC stmC sealP seal2P .shared) = (proofC
  (slotP 1)).stmAt declC stmC sealP seal2P .shared
-- no call for a first and for a second statement
#guard [Which.first, .second].map (fun w => (callsOf (keyC.stmAtW hNoted declC sealP seal2P w),
  callsOf ((proofC (slotP 1)).stmAtW hNoted declC stmC sealP seal2P w))) = List.replicate 2 ([], [])
-- no call where the shared statement is nothing for form: the seven slots; the three of a key; the
-- first seal of 31 bytes; a table with one answer; the head's other number
#guard (badSlots.map fun s => callsOf ((proofC s).stmAtW hNoted declC stmC sealP seal2P .shared)) =
  List.replicate 7 []
#guard (badKeySlots.map fun s => callsOf (({ keyC with slot := s } : KeyParsed).stmAtW hNoted declC
  sealP seal2P .shared)) = List.replicate 3 []
#guard callsOf ((proofC (slotP 0)).stmAtW hNoted declC stmC (pattern 31 5 1) seal2P .shared) = []
  && callsOf (keyC.stmAtW hNoted declC (pattern 31 5 1) seal2P .shared) = []
#guard callsOf ((proofC (slotP 0)).stmAtW hNoted declC { stmC with table := ⟨sibB, [(1, 2, 3)]⟩ }
  sealP seal2P .shared) = [] && callsOf (({ keyC with table := ⟨sibB, [(1, 2, 3)]⟩ } :
  KeyParsed).stmAtW hNoted declC sealP seal2P .shared) = []
#guard callsOf (({ proofC (slotP 0) with copy := 2 } : ProofParsed).stmAtW hNoted declC stmC sealP
  seal2P .shared) = []

-- `KeyStm.idOkW` asks the form of the caller's ID: under a hash whose answers have 31 bytes, an ID
-- of these 31 bytes is not told; under one of 32 bytes it is
#guard !Id.run ((⟨pattern 31⟩ : KeyStm).idOkW (hConst 31) declP declP.cfg ⟨sibB, two⟩ three []) &&
  Id.run ((⟨pattern 32⟩ : KeyStm).idOkW (hConst 32) declP declP.cfg ⟨sibB, two⟩ three [])
-- its one call: under 179, index 0, on 32 + 8 + 112 + 8 + 72 + 8 + 48 + 8 bytes; no call where the
-- ID has 31 bytes
#guard callsOf ((⟨id141⟩ : KeyStm).idOkW hNoted declP declP.cfg ⟨sibB, two⟩ three []) =
    [(179, 0, 296)] &&
  valueOf ((⟨id141⟩ : KeyStm).idOkW hNoted declP declP.cfg ⟨sibB, two⟩ three [])
#guard callsOf ((⟨pattern 31⟩ : KeyStm).idOkW hNoted declP declP.cfg ⟨sibB, two⟩ three []) = []

-- THE HASHED ITEM "binding tree". `ChainDecl.bindShape`: the item's two words; among other items
#guard (chainOf [bindItem 2 40]).bindShape = some ⟨2, 40⟩ &&
  (chainOf [("codes", pattern 8), bindItem 2 40, ("layout", pattern 8)]).bindShape = some ⟨2, 40⟩
-- line 187: "the item binding tree: depth 2, salts of 40 bytes": PAGE for the item's value
#guard hex (bindItem 2 40).2 = "02000000000000002800000000000000"
-- no item; an item of another name; the value with 15, 17, 24 bytes, and with none
#guard [[], [("binding trees", u64n 2 ++ u64n 40)], [("binding tree", (u64n 2 ++ u64n 40).extract 0
  15)],
  [("binding tree", u64n 2 ++ u64n 40 ++ zeroBytes 1)], [("binding tree", u64n 2 ++ u64n 40 ++ u64n
      0)],
  [("binding tree", ByteArray.empty)]].map (fun l => (chainOf l).bindShape) = List.replicate 6 none
-- the depth: 0 and 48 are admitted, 49 is not (R14.6)
#guard [0, 48, 49].map (fun d => (chainOf [bindItem d 40]).bindShape) =
  [some ⟨0, 40⟩, some ⟨48, 40⟩, none]
-- the salt's length: 40, 48, 56, 64 are admitted; 0, 32, 39, 41, 72 are not (R7.3)
#guard [40, 48, 56, 64].map (fun s => (chainOf [bindItem 2 s]).bindShape) =
  [40, 48, 56, 64].map fun s => some ⟨2, s⟩
#guard [0, 32, 39, 41, 72].map (fun s => (chainOf [bindItem 2 s]).bindShape) = List.replicate 5 none
-- of two items of the name the one in front is read
#guard (chainOf [bindItem 2 40, bindItem 3 48]).bindShape = some ⟨2, 40⟩
-- at the tests' declared structure; `Declared.proofDepth`, and 0 where the item gives no shape
#guard declC.key.first.bindShape = some ⟨0, 40⟩ && declC.proof.first.bindShape = some ⟨2, 40⟩ &&
  declC.proofDepth = 2 && (declAt [bindItem 0 40] [bindItem 5 40]).proofDepth = 5 &&
  (declAt [bindItem 0 40] []).proofDepth = 0 && (declAt [bindItem 0 40] [bindItem 49
      40]).proofDepth = 0
-- the six statements do not hang on the field `ThreeDecl.bind`: with other numbers in both fields
-- they are the same
#guard declB.key.bind != declC.key.bind && declB.proof.bind != declC.proof.bind &&
  [Which.first, .shared, .second].all fun w =>
    keyC.stmAt declB sealP seal2P w = keyC.stmAt declC sealP seal2P w &&
    (proofC (slotP 1)).stmAt declB stmC sealP seal2P w =
      (proofC (slotP 1)).stmAt declC stmC sealP seal2P w
-- the key's item is not read for a proof, nor the proof's for a key
#guard proofSome (declAt [] [bindItem 2 40]) stmC (proofC (slotP 0)) sealP seal2P = [true, true,
  true] &&
  keySome (declAt [bindItem 0 40] []) keyC sealP seal2P = [true, true, true]
-- REFUSED, a proof: no item; the value with 15, 17, 24 bytes: the shared statement alone is
-- nothing, and the hash is not called
#guard [[], [("binding tree", (u64n 2 ++ u64n 40).extract 0 15)],
  [("binding tree", u64n 2 ++ u64n 40 ++ zeroBytes 1)], [("binding tree", u64n 2 ++ u64n 40 ++ u64n
      0)]].map
  (fun l => (proofSome (declAt [bindItem 0 40] l) stmC (proofC (slotP 0)) sealP seal2P,
    callsOf ((proofC (slotP 0)).stmAtW hNoted (declAt [bindItem 0 40] l) stmC sealP seal2P
        .shared))) =
  List.replicate 4 ([true, false, true], [])
-- depth 49 with a slot that fits it: nothing, no call. SCRIPT for the root, under `hPage`: depth 48
-- with a slot that fits it
#guard (⟨0, saltP, deep 49⟩ : SlotParsed).fits ⟨49, 40⟩ &&
  proofSome (declAt [] [bindItem 49 40]) stmC (proofC ⟨0, saltP, deep 49⟩) sealP seal2P = [true,
      false, true] &&
  callsOf ((proofC ⟨0, saltP, deep 49⟩).stmAtW hNoted (declAt [] [bindItem 49 40]) stmC sealP
      seal2P .shared) = []
#guard Id.run ((proofC ⟨0, saltP, deep 48⟩).stmAtW hPage (declAt [] [bindItem 48 40]) stmC sealP
  seal2P .shared) =
  some (sharedStm tableC (unhex "80d2025dd02fd910c7dbb0a3230289dc97ce5c51be9f0d69ef70ae4ef44dcc00"))
-- a salt's length that no leaf can have, 0, 39, 41, 32, 72, each with a slot that fits it: nothing,
-- no call
#guard [0, 39, 41, 32, 72].map (fun n => ((⟨0, pattern n 3 9, [sibA, sibB]⟩ : SlotParsed).fits ⟨2,
  n⟩,
    proofSome (declAt [] [bindItem 2 n]) stmC (proofC ⟨0, pattern n 3 9, [sibA, sibB]⟩) sealP
        seal2P,
    callsOf ((proofC ⟨0, pattern n 3 9, [sibA, sibB]⟩).stmAtW hNoted (declAt [] [bindItem 2 n])
        stmC sealP seal2P
      .shared))) = List.replicate 5 (true, [true, false, true], [])
-- SCRIPT for the roots, under `hPage`: salts of 48 and of 64 bytes, each with a slot that fits it
#guard [48, 64].map (fun n => Id.run ((proofC ⟨0, pattern n 3 9, [sibA, sibB]⟩).stmAtW hPage
    (declAt [] [bindItem 2 n]) stmC sealP seal2P .shared)) =
  ["67cd5dc1d51e5249c921fbf3ab275d8b0374ffaef13a74875422538908135999",
    "73b6eed80a914bc6696fccb72ef96409ca690032a52a5d935aa9c9c12aac94de"].map fun r => some
        (sharedStm tableC (unhex r))
-- REFUSED, a key: no item; an item of depth 1 with a slot that fits depth 1 (R13.5: a key's depth
-- is 0): nothing, no call
#guard keySome (declAt [] [bindItem 2 40]) keyC sealP seal2P = [true, false, true] &&
  callsOf (keyC.stmAtW hNoted (declAt [] [bindItem 2 40]) sealP seal2P .shared) = []
#guard (⟨0, saltP, [sibA]⟩ : SlotParsed).fits ⟨1, 40⟩ &&
  keySome (declAt [bindItem 1 40] []) { keyC with slot := ⟨0, saltP, [sibA]⟩ } sealP seal2P =
      [true, false, true] &&
  callsOf (({ keyC with slot := ⟨0, saltP, [sibA]⟩ } : KeyParsed).stmAtW hNoted (declAt [bindItem 1
      40] []) sealP
    seal2P .shared) = []

-- `Declared.seedsW` under the tests' shape: its calls: the first value of the record's chain (under
-- 160, the label 2 ^ 32, on 168 bytes), then that chain's one round: 26 calls under 162, of two
-- blocks each: a block for the chain's next value and 50 for the 198 words that one seed of nine
-- coordinates can use at most
#guard callsOf (declC.seedsW hNoted declC.cfg tableC) =
    (160, 2 ^ 32, 168) :: List.replicate 26 (162, 1, 16) &&
  valueOf (declC.seedsW hNoted declC.cfg tableC) = drawn declC declC.cfg tableC &&
  seedsOk .two shapeC (drawn declC declC.cfg tableC)

-- THE CLOSED FORM OF THE TEST ON THE ID, `KeyParsed.idOkW`. SCRIPT: the ID of the file's
-- table under the tests' shape (two answers) and the digest of the declared file, with the seed
-- drawn from that table's name and no digest at the end
#guard Id.run (keyC.idOkW hId declC ⟨unhex
  "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594"⟩)
-- it is the open form at the drawn seed, and not at another list
#guard idOk (unhex "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594") declC
  declC.cfg tableC (drawn declC declC.cfg tableC) &&
  !idOk (unhex "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594") declC declC.cfg
    tableC [] &&
  !idOk (unhex "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594") declC declC.cfg
    tableC (drawn declC declC.cfg tableC).reverse
-- its calls: the configuration's digest, the drawing's, then the ID on 32 + 8 + 112 + 8 + 240 + 8 +
-- 48 + 8 bytes
#guard callsOf (keyC.idOkW hNoted declC ⟨unhex
  "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594"⟩) = [(169, 2, 20)] ++
  callsOf (declC.seedsW hNoted declC.cfg tableC) ++ [(179, 0, 464)]
-- that ID with its first byte turned, with its last; at a file with another root; under another
-- public file
#guard !Id.run (keyC.idOkW hId declC ⟨turn (unhex
  "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594") 0⟩) &&
  !Id.run (keyC.idOkW hId declC ⟨turn (unhex
      "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594") 31⟩) &&
  !Id.run (({ keyC with table := ⟨sibA, two⟩ } : KeyParsed).idOkW hId declC ⟨unhex
      "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594"⟩) &&
  !Id.run (keyC.idOkW hId { declC with files := [ascii "toy"] } ⟨unhex
      "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594"⟩)
-- a table without the form (one answer); an ID of 31 bytes: false, and no call
#guard !valueOf (({ keyC with table := ⟨sibB, [(1, 2, 3)]⟩ } : KeyParsed).idOkW hNoted declC
  ⟨unhex "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594"⟩) &&
  callsOf (({ keyC with table := ⟨sibB, [(1, 2, 3)]⟩ } : KeyParsed).idOkW hNoted declC ⟨unhex
      "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594"⟩) = []
#guard !valueOf (keyC.idOkW hNoted declC ⟨pattern 31⟩) && callsOf (keyC.idOkW hNoted declC
  ⟨pattern 31⟩) = []
-- ON A REFUSAL. Under `hShort` the first value of the record's chain has 31 bytes and the chain's
-- step refuses: no element is drawn, which has not the form; the closed form goes on and tells
-- (SCRIPT) the ID of the string with no seed, and not the ID above
#guard Id.run (declC.seedsW hShort declC.cfg tableC) = [] && !seedsOk .two shapeC [] &&
  Id.run (keyC.idOkW hShort declC ⟨unhex
      "9ab89fd0c86daa1b3e2787a7b714faf2aba7df3d47a5e53e1ad62287dfd8a4ee"⟩) &&
  idOk (unhex "9ab89fd0c86daa1b3e2787a7b714faf2aba7df3d47a5e53e1ad62287dfd8a4ee") declC declC.cfg
    tableC [] &&
  !Id.run (keyC.idOkW hShort declC ⟨unhex
      "ba711efc9ff885cb2792e532a489cf41985333edd72885419a7cdb3d78752594"⟩)
-- THE THIRD ID (PAGE 142) IS NOT TOLD BY THE CLOSED FORM: the page's table has two answers under
-- a shape that says 512, so it has not the form, and the answer is false without a call. The open
-- form tells it (block 3)
#guard !valueOf (keyC.idOkW hNoted declP ⟨idDrawn⟩) && callsOf (keyC.idOkW hNoted declP
  ⟨idDrawn⟩) = [] &&
  keyC.table = ⟨sibB, two⟩ && idOk idDrawn declP declP.cfg keyC.table (drawn declP declP.cfg
    keyC.table)

-- `Declared.recordStmW`. PAGE 139: the name under the digest of the declared file
#guard hex (Id.run (declP.recordStmW hId ⟨sibB, []⟩)) =
  "04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9ce7b508817ead50bb3f386f68d442b114\
      119e93e8ef2b14a7d70190075348db5f0a00000000000000000200000000000028000000000000000900000000000\
      00001000000000000002800000000000000"
-- its one call
#guard callsOf (declP.recordStmW hNoted ⟨sibB, []⟩) = [(169, 2, 20)]
-- under `hPage` the digest in the name is pattern(32)
#guard Id.run (declP.recordStmW hPage ⟨sibB, []⟩) = recordStm declP cfgP ⟨sibB, []⟩ &&
  Id.run (declP.recordStmW hPage ⟨sibB, []⟩) != Id.run (declP.recordStmW hId ⟨sibB, []⟩)
end

/-! # C. The tests of Fmt/ChainStmMore.lean -/

section
open ChainStmTest

namespace ChainStmMoreTest

/-- a made-up configuration's digest -/
def cfgT : ByteArray := pattern 32 17 4

/-- a second table of the tests' shape: another root, other answers -/
def table2 : TableSt :=
  ⟨pattern 32 19 6, (List.range 256).map fun i => (UInt64.ofNat (3 * i + 2), pLast, UInt64.ofNat i)⟩

def entry : EntryStm := ⟨table, table2⟩

/-- the tests' shape with the value v in its word number k, from 0 -/
def shapeAt (k v : Nat) : TableShape :=
  match k with
  | 0 => { shape with a := v }
  | 1 => { shape with message := v }
  | 2 => { shape with tail := v }
  | 3 => { shape with logRows := v }
  | 4 => { shape with answers := v }
  | _ => { shape with saltBytes := v }

/-- the tests' name -/
def nameT : ByteArray := recordStm decl cfgT table

/-- the elements of the seed that is drawn from that name: a point of ten coordinates and a factor
-/
def seedsT : List Ext := Id.run (decl.seedsW hId cfgT table)

def item1 : ByteArray := tableItem "the first table" table.root table.answers
def item2 : ByteArray := tableItem "the further table" table2.root table2.answers

end ChainStmMoreTest

open ChainStmMoreTest

-- the premises of the laws hold at these values
#guard shape.wordsFit && shape.ok && shape.fitsWord && table.root.size = 32 && cfgT.size = 32
#guard entry.ok decl && table2.ok .two shape && decide (table ≠ table2)
  && decide (table.root ≠ table2.root)
#guard decl.table = shape && decl.setting.field = .two
-- 2 ^ 40 rows with 2 ^ 30 answers each: wordsFit, and no fitsWord
#guard (⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 30, 40⟩ : TableShape).wordsFit
  && !(⟨32, 2 ^ 32 - 1, 1, 40, 2 ^ 30, 40⟩ : TableShape).fitsWord

-- the chain of a record's seeds
#guard rdRecordStm nameT = some (table.root, cfgT, shape)
#guard nameT.size = 112 && shape.wordsBytes.size = 48
-- put together here, without the writer: six different words, each in its place; the reader tests
-- no range
#guard rdRecordStm (table.root ++ cfgT ++ u64n 1 ++ u64n 2 ++ u64n 3 ++ u64n 4 ++ u64n 5 ++ u64n 6)
  = some (table.root, cfgT, ⟨1, 2, 3, 4, 5, 6⟩) && !(⟨1, 2, 3, 4, 5, 6⟩ : TableShape).ok
-- the string of base 16 of the library's test of tableName (Fmt/Rules4.lean)
#guard rdRecordStm (unhex ("04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9c" ++
  "e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f" ++
  "0a0000000000000000020000000000002800000000000000" ++
  "090000000000000001000000000000002800000000000000")) =
  some (pattern 32 13 4, Toy4.cfg, ⟨10, 512, 40, 9, 1, 40⟩)
-- a byte behind; the last byte gone; the empty string
#guard rdRecordStm (oneMore nameT) = none
#guard rdRecordStm (cutLast nameT) = none
#guard rdRecordStm ByteArray.empty = none
-- five words; seven words
#guard rdRecordStm (table.root ++ cfgT ++ u64n 1 ++ u64n 2 ++ u64n 3 ++ u64n 4 ++ u64n 5) = none
#guard rdRecordStm (table.root ++ cfgT ++ u64n 1 ++ u64n 2 ++ u64n 3 ++ u64n 4 ++ u64n 5 ++ u64n 6
  ++ u64n 7) = none
-- a root of 31 bytes, of 33 bytes; a digest of 31 bytes, of 33 bytes
#guard rdRecordStm (shape.name cfgT (pattern 31)) = none
  && rdRecordStm (shape.name cfgT (pattern 33)) = none
#guard rdRecordStm (shape.name (pattern 31 17 4) table.root) = none
  && rdRecordStm (shape.name (pattern 33 17 4) table.root) = none
-- a root of 33 bytes with a digest of 31: 112 bytes, read as another root and another digest
#guard rdRecordStm (shape.name (pattern 31 17 4) (pattern 33))
  = some (pattern 32, (pattern 33).extract 32 33 ++ pattern 31 17 4, shape)
-- each of the six words at 2 ^ 64 - 1: wordsFit, and read back
#guard (List.range 6).all fun k => (shapeAt k (2 ^ 64 - 1)).wordsFit && decide
  (rdRecordStm ((shapeAt k (2 ^ 64 - 1)).name cfgT table.root)
  = some (table.root, cfgT, shapeAt k (2 ^ 64 - 1)))
-- each at 2 ^ 64: no wordsFit; the name is that of the shape with 0 there, and is read as that
-- shape
#guard (List.range 6).all fun k => !(shapeAt k (2 ^ 64)).wordsFit
  && decide ((shapeAt k (2 ^ 64)).name cfgT table.root = (shapeAt k 0).name cfgT table.root)
  && decide (rdRecordStm ((shapeAt k (2 ^ 64)).name cfgT table.root)
  = some (table.root, cfgT, shapeAt k 0))
-- the six are six different shapes
#guard ((List.range 6).map fun k => shapeAt k 0).eraseDups.length = 6
-- the answers are not in the name: another table with the same root
#guard recordStm decl cfgT { table with answers := table2.answers } = nameT
  && decide (table.answers ≠ table2.answers)
-- another root, another digest, another shape: another name
#guard decide (recordStm decl cfgT table2 ≠ nameT)
  && decide (recordStm decl (pattern 32 17 5) table ≠ nameT)
  && decide (recordStm { decl with table := shapeAt 5 48 } cfgT table ≠ nameT)
-- no statement of another chain
#guard rdRecordStm table.item = none && rdRecordStm (sealItems [seal1, seal2]) = none
  && rdRecordStm entry.bytes = none

-- the string of the commitment ID: the forms of its two further lists; its length
#guard shape.cube = 10 && seedsT.length = 11 && seedsOk .two shape seedsT && toldOk [seal1, seal2]
#guard (idString decl cfgT table seedsT []).size = 80 + 2 * 32 + 32 + 24 * 11 + 24 * 256 &&
  (idString decl cfgT table seedsT [seal1, seal2]).size =
    80 + 2 * 32 + 32 + 24 * 11 + 24 * 256 + 2 * 32
-- other answers under the same root (the name is the same: above): another string
#guard decide (idString decl cfgT { table with answers := table2.answers } seedsT [] ≠
  idString decl cfgT table seedsT [])
-- other seeds' elements with the form; another list of digests: one more, another, the other order
#guard seedsOk .two shape seedsT.reverse &&
  decide (idString decl cfgT table seedsT.reverse [] ≠ idString decl cfgT table seedsT []) &&
  decide (idString decl cfgT table seedsT [seal1] ≠ idString decl cfgT table seedsT []) &&
  decide (idString decl cfgT table seedsT [seal1] ≠ idString decl cfgT table seedsT [seal2]) &&
  decide (idString decl cfgT table seedsT [seal1, seal2] ≠
    idString decl cfgT table seedsT [seal2, seal1])
-- another root; another digest; another shape with as many answers and seeds' elements
#guard decide (idString decl cfgT { table with root := table2.root } seedsT [] ≠
    idString decl cfgT table seedsT [])
  && decide (idString decl (pattern 32 17 5) table seedsT [] ≠ idString decl cfgT table seedsT [])
  && decide (idString { decl with table := shapeAt 5 48 } cfgT table seedsT [] ≠
    idString decl cfgT table seedsT [])
  && table.ok .two (shapeAt 5 48) && seedsOk .two (shapeAt 5 48) seedsT
-- without wordsFit: two shapes, the table and the seeds' elements have the form under both, one
-- string
#guard idString { decl with table := shapeAt 0 (2 ^ 64) } cfgT table seedsT []
  = idString { decl with table := shapeAt 0 0 } cfgT table seedsT []
  && table.ok .two (shapeAt 0 (2 ^ 64)) && table.ok .two (shapeAt 0 0)
  && seedsOk .two (shapeAt 0 (2 ^ 64)) seedsT && seedsOk .two (shapeAt 0 0) seedsT
  && decide (shapeAt 0 (2 ^ 64) ≠ shapeAt 0 0)
-- without toldOk: two lists of digests, one string
#guard idString decl cfgT table seedsT [(pattern 64).extract 0 31, (pattern 64).extract 31 64]
  = idString decl cfgT table seedsT [(pattern 64).extract 0 32, (pattern 64).extract 32 64]
  && !toldOk [(pattern 64).extract 0 31, (pattern 64).extract 31 64]
  && toldOk [(pattern 64).extract 0 32, (pattern 64).extract 32 64]
-- the library's start of a chain gives a head, with random bytes and without
#guard (startChain 7 (paramsDigest nameT) entry.bytes (some seal1)).isSome
  && (startChain 7 (paramsDigest nameT) entry.bytes none).isSome

-- an entry's link
#guard EntryStm.read .two shape entry.bytes = some (table, table2)
#guard entry.bytes = item1 ++ item2
-- put together here, without the writers of a table's item
#guard EntryStm.read .two shape (item "the first table" (text table.root ++ u64n 256
  ++ cat (table.answers.map ext)) ++ item "the further table" (text table2.root ++ u64n 256
  ++ cat (table2.answers.map ext))) = some (table, table2)
-- the tables' order is kept; one table twice
#guard EntryStm.read .two shape (EntryStm.bytes ⟨table2, table⟩) = some (table2, table)
#guard EntryStm.read .two shape (EntryStm.bytes ⟨table, table⟩) = some (table, table)
-- the items in the other order
#guard EntryStm.read .two shape (item2 ++ item1) = none
-- the first item alone; the second alone; a third item behind
#guard EntryStm.read .two shape item1 = none && EntryStm.read .two shape item2 = none
  && EntryStm.read .two shape (item1 ++ item2 ++ item2) = none
-- the second item under the first's name; the first under the second's; the first under "table"
#guard EntryStm.read .two shape (item1 ++ tableItem "the first table" table2.root table2.answers)
  = none
#guard EntryStm.read .two shape (tableItem "the further table" table.root table.answers ++ item2)
  = none
#guard EntryStm.read .two shape (table.item ++ item2) = none
-- a byte behind; the last byte gone; the empty string
#guard EntryStm.read .two shape (oneMore entry.bytes) = none
#guard EntryStm.read .two shape (cutLast entry.bytes) = none
#guard EntryStm.read .two shape ByteArray.empty = none
-- a root of 31 bytes, of 33 bytes: the first table's, the further table's
#guard EntryStm.read .two shape (EntryStm.bytes ⟨{ table with root := pattern 31 }, table2⟩) = none
  && EntryStm.read .two shape (EntryStm.bytes ⟨{ table with root := pattern 33 }, table2⟩) = none
#guard EntryStm.read .two shape (EntryStm.bytes ⟨table, { table2 with root := pattern 31 19 6 }⟩)
  = none && EntryStm.read .two shape (EntryStm.bytes ⟨table,
  { table2 with root := pattern 33 19 6 }⟩) = none
-- 255 answers under the shape of 256: the first table, the further table
#guard EntryStm.read .two shape (EntryStm.bytes
  ⟨{ table with answers := table.answers.tail }, table2⟩) = none
#guard EntryStm.read .two shape (EntryStm.bytes ⟨table,
  { table2 with answers := table2.answers.tail }⟩) = none
-- both with 255 answers, under a shape of 255
#guard (EntryStm.read .two { shape with logRows := 0, answers := 255 } (EntryStm.bytes
  ⟨{ table with answers := table.answers.tail },
  { table2 with answers := table2.answers.tail }⟩)).isSome
-- the further table's first answer's first word is p, and p - 1
#guard EntryStm.read .two shape (EntryStm.bytes ⟨table,
  { table2 with answers := (pLast + 1, pLast, 0) :: table2.answers.tail }⟩) = none
#guard (EntryStm.read .two shape (EntryStm.bytes ⟨table,
  { table2 with answers := (pLast, pLast, 0) :: table2.answers.tail }⟩)).isSome
-- the same bytes in the first field, where p is smaller
#guard EntryStm.read .one shape entry.bytes = none
-- the first item's word one too great: the value would take the next item's first byte
#guard EntryStm.read .two shape (textS "the first table" ++ u64n (48 + 24 * 256 + 1)
  ++ (text table.root ++ list ext table.answers) ++ item2) = none
#guard EntryStm.read .two shape (textS "the first table" ++ u64n (48 + 24 * 256) ++ (text table.root
  ++ list ext table.answers) ++ item2) = some (table, table2)
-- no statement of another chain
#guard EntryStm.read .two shape (sharedStm table broot) = none
  && EntryStm.read .two shape stm.bytes = none && EntryStm.read .two shape nameT = none
  && rdSharedStm .two shape entry.bytes = none

end

/-! # E. What three laws of Fmt/ChainStmMore.lean require of their parameter h (any function in the
hash's place) can be met -/

-- each law at the format's own hash, its premises on h proved from the library's theorem on that
-- hash's length (`size_H`, Fmt/Rules23Laws.lean): the answers under 172; under 169 and 160; one
-- under 160
example := startChainW_rest hId fun t i s b => size_H 172 t i s b
example := Declared.idString_closed_inj hId (fun t i s b => size_H 169 t i s b)
  fun t i s b => size_H 160 t i s b
example (D : Declared) (cfg : ByteArray) (t : TableSt) :=
  Declared.seedsW_ok_of_size hId D cfg t (size_H 160 0 recordLabel zero32 _)

end Fmt

/-
Notes in full.

Fmt/TestChainStm.lean: the tests (#guard) on the statements of the chains of a key file, an entry
file and a proof file, and the values that the tests need. No theorem. Two other files of tests use
values of its namespace `ChainStmKnown`.

Five parts.
  A. The readers of Fmt/ChainStmRead.lean at made-up values of full size: 55 tests.
  B. Fmt/ChainStm.lean (the statements, the binding tree's root, the test on the commitment ID):
     blocks 0 to 8 and 3a, 140 tests. Some of them stand under a comment PAGE: they hold a value or
     bytes that the format page prints (one of block 8's holds that the closed form does
     NOT tell the page's ID). The others hold a value of the page's script or one of this file's
     own.

  C. The tests of Fmt/ChainStmMore.lean: 54.
  D. OnBytes/Entry/TestRecordToyDeclared.lean: the premises of Fmt/ChainStmSmall.lean's theorems.
  E. What three laws of Fmt/ChainStmMore.lean ask of their letter h is met by the format's own hash:
     3 examples (no #guard).
Fmt.TestRecordSeeds and Fmt.TestRequestItem are imported so that whoever builds this file builds
these two files of tests too; nothing here calls them.

PART B's EXPECTED VALUES.

Three kinds of expected value from outside this library (PAGE; SCRIPT; SCRIPT, OUR ORDER); a test's
comment says which it has. A test whose comment names none of the three has an expected value of
this file's own: a refusal, the equality of two calls, a list of the hash's calls.
  PAGE: a known answer that the format page prints: a line of docs/format/format-vectors.txt, named
    by its number. The inputs are taken from that line's own words, and from the file's head for
    "pattern".
  SCRIPT: the page prints no such value. It was made by the page's own script
    (docs/format/format_rules.py), called by a small program that imports it and has no hash and no
    spelling of its own [that program is not in this library]. Such a value was computed by
    another implementation than this library's, and is
    NO KNOWN ANSWER OF THE PAGE. That program also makes again the fifteen lines whose values stand
    below as PAGE (11, 36, 37, 112, 139 to 143, 184, 187 to 191) and compares each with the file's
    line, whole. The script's function for the commitment ID takes the seeds as pairs (a point's
    elements, a factor); a made-up flat list of k elements the program hands over as one pair (the
    first k - 1, the last): where the pairs are cut does not enter the string. Tests under
    SCRIPT (in block 6 and block 8) and under PAGE 184 end in `wordsPHex`, the last 52
    bytes of line 184, written once: the value held is the whole string.
  SCRIPT, OUR ORDER: the script has no function for the thing (a shared chain's statement, a second
    chain's, a climb with a sibling on the wrong side, a commitment ID with a digest at the end of
    its string). The program puts the script's item(), or its binding_leaf() and binding_vertex(),
    or for that ID its string(), u64() and ext() under its H(179, ...) in R4.11's order, together
    (the script's own function for the ID lays the word 0 at the end and takes no digests); names
    and order of a statement's items are read off the page's words (09-key-and-leaf-files.md,
    R13.5's table; 10-proof-file.md, R14.9, R14.10). So the order in these values is that program's
    reading of the page, not the script's.

PART A. At one made-up value of each kind with the sizes of a full-size one: a table of 256 answers
(the source: at the tests' shape) with a root of 32 bytes, a value of the item "request" of 708
bytes (177 words of four bytes: Decl/Declared.lean, `ProofStm.request`), a request file of 4,104
bytes (`ProofStm.words`). The forms (`TableSt.ok`, `ProofStm.ok`, `sealsOk`)
and `TableShape.fitsWord` hold there, and each reader gives the values back. Refusals: each string
that is refused differs from one that is accepted in the one thing that its comment names; but one
test hands the accepted string to a reader that is told the other field, one hands a reader the
empty string, and the last two tests of the last line on a proof's first chain hand a reader the
whole statement of another chain.

PART B. Which declaration of Fmt/ChainStm.lean is held by which block:
    `climbW`: block 1 (PAGE 11, 188 to 191; SCRIPT).
    `SlotParsed.rootW`, `SlotParsed.root`: block 2 (PAGE 112, 188 to 191; SCRIPT).
    `KeyStm.ok`, `UserStm.keyStm`, `KeyStm.idOkW`: block 3 (PAGE 139 to 142; SCRIPT;
    SCRIPT, OUR ORDER); three tests in block 8.
    `TableShape.cube`, `seedsOk`, `toldOk`, `Declared.seedsW`: block 3a; PAGE 142 in block 3;
    three tests in block 8 (the calls of the hash; a refusal).
    `recordStm`: block 4 (PAGE 139, 36, 37; SCRIPT).
    `keyStmAt`: block 5 (PAGE 143; SCRIPT; SCRIPT, OUR ORDER).
    `proofStmAt`: block 6 (PAGE 184; SCRIPT; SCRIPT, OUR ORDER).
    The closed forms (`KeyParsed.firstStm`, `ProofParsed.firstStm`, `secondStm`, `sharedStmOfW`,
    `KeyParsed.sharedStmW`, `ProofParsed.sharedStmW`, `KeyParsed.stmAtW`, `ProofParsed.stmAtW`,
    `KeyParsed.stmAt`, `ProofParsed.stmAt`, `ChainDecl.bindShape`, `Declared.proofDepth`,
    `KeyParsed.idOkW`, `Declared.recordStmW`): block 8 (PAGE 188 to 191 under a stand-in for the
    configuration's digest; PAGE 139, 187; SCRIPT; refusals; the calls of the hash).
  Block 0 holds the library's `pattern` at the page. Block 7 hands the page's own bytes to two
  readers of Fmt/ChainStmRead.lean.

PART C. At the made-up values of the namespace ChainStmTest (a table of 256 answers, its
shape, its declared structure), a made-up digest and a second table. The forms hold there, and each
reader gives the values back: from the writer's bytes, from bytes put together in the test without
the writer, and (a name) from the string of base 16 in the library's own test of `tableName`
(Fmt/Rules4.lean). Refusals: each string that is refused differs from one that is accepted in the
one thing that its comment names; but two tests hand a reader the empty string, one hands the
accepted string to a reader that is told the other field, and the tests under "no statement of
another chain" hand a reader the whole statement of another chain. On the string of the commitment
ID: the forms of its lists; its length; that it differs where the answers, the seeds' elements, the
digests at the end, the root, the digest or the shape differ; two shapes without
`TableShape.wordsFit` that give one string; two lists without `toldOk` that give one string.
`startChain` gives a head at made-up values. The test "fewer than 2 ^ 64 bytes" (`wholeStm`) is
reached by no #guard: no such string can be made.

What is not claimed.
   Part A's declared structure has no public file and no chain: `ProofStm.ok` reads its field and
   its tables' shape alone.
   The test "fewer than 2 ^ 64 bytes" (`wholeStm`) is reached by no #guard: no such string can be
   made. What it does is told by the laws alone (Fmt/ChainStmLaws.lean).
   Part D's tests are at a link's chain: no description of a key's or a proof's chain is tried.
   Of part B:
   Some tests hold by a definition or by a theorem of the neighbouring files, and can fail only if
   that definition is turned: the four roots of `SlotParsed.rootW` beside those of
   `SlotParsed.root`;
   `UserStm.keyStm`; "the parts by their own names"; the answers are not in the name; the reply is
   no item. Where a closed form is held against the open form at `SlotParsed.root`, what the test
   shows is that the closed form is something; the tests under `hPage` and on the calls hold the
   value. The page has no known answer for: a root at another depth than 2; a shared chain's
   statement; a second chain's. The page's two IDs are at a shape of 2 ^ 9 rows with one answer
   each, and at a table of two answers: these tables have not the form `TableSt.ok` at that shape.
   The seeds' elements of the ID with three elements have not the form `seedsOk` there; those of
   the ID whose seed is drawn from the name have it.
   `KeyStm.idOkW` does not ask that form. `KeyParsed.idOkW` asks it: so the closed form of the
   test on the ID is held at no known answer of the page, and at one value alone, which is SCRIPT.
   In block 2 two slots do not fit the depth at which their root is asked (`SlotParsed.fits`), and
   `SlotParsed.root` answers all the same: it asks no form. Each of the two tests says so.
   In blocks 0 to 7 every hash is the format's own (`hId`, Fmt/Rules7.lean). Block 8 has four
   stand-ins beside it, each told at its definition.
   Several seeds of one record are held against `Known56.recordSeeds` (Fmt/Rules56Known.lean) alone,
   in Fmt/TestRecordSeeds.lean, and here by their number and form: the page's one drawn seed is one.
   That the closed forms ask `TableShape.fitsWord` is reached by no test: a shape without it says
   more answers than a table can be given here, so `TableSt.ok` fails there too.
   The last clause of `ProofStm.ok` (fewer than 2 ^ 64 bytes) is reached by no test either: no such
   request or table can be made here.
   Of the chains of the closed forms' declared structure one parameter item alone is set: it passes
   neither `Declared.keyFormOk` nor `Declared.proofFormOk` (Fmt/Parsed.lean; a test in block 8),
   which the closed forms do not ask.
-/

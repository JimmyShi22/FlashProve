-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ChainStmRead.lean: readers of the bytes of the statements of a key file's and a proof file's
chains. Definitions.
It stands on Fmt/ChainStm.lean, Decl/Declared.lean, Fmt/Parsed.lean and Fmt/ParsedRead.lean.

The bytes of a chain's statement enter the chain's first query, behind a word for their length
(R4.6: `firstBytes`, Fmt/Rules4.lean). The writers lie already:
`TableSt.item`, `sharedStm`, `ProofStm.bytes` (Fmt/Parsed.lean), `sealItems` (Fmt/Rules4.lean);
which of them is the statement of which chain: `keyStmAt`, `proofStmAt` (Fmt/ChainStm.lean). Here is
the other side: total functions from bytes to the values from which such bytes are written, or a
refusal. They are here so that laws can say that a statement's bytes fix these values
(Fmt/ChainStmLaws.lean).

How. The readers of the parts (`Rd`, Fmt/Rules1.lean) are put together from the library's (`rdText`,
`rdList`, `rdExt`, `rdDigest`, `rdEnum`, `rdPair`, Fmt/Rules1.lean; `rdItem`, Fmt/ParamsRead.lean),
`rdMap` (Fmt/ParsedRead.lean) and two of this file, `rdIf` and `rdNamed`. The four readers
of a statement run such a reader on the whole string (`wholeStm`, over `whole`, Fmt/Rules1.lean). No
Mathlib, neither directly nor through the imports.

What a reader is told. The field f and the tables' shape s, the two arguments of `TableSt.ok`. The
number of a table's answers stands in the bytes, as the word in front of the list (`list`,
Fmt/Rules1.lean; `tableItem`, Fmt/Rules4.lean), and it follows from the shape (`TableShape.count`).
The reader reads as many answers as the bytes' own word says and then refuses unless that is the
shape's number: the test is `TableSt.ok` itself. Of the shape's six words the readers use that
number alone.

Rule numbers (R…) are the format page's.

1. What the file contains.
    `rdIf`: a reader, refused where a test on its value fails.
    `rdNamed`: an item of a given name, whose value a given reader reads whole.
    `wholeStm`: a reader on a whole statement of fewer than 2 ^ 64 bytes.
    `rdTableValue`, `rdTableItem`: the value and the item of a table (R4.6).
    `TableSt.readItem`: the statement of a key file's one-time chain (R13.5).
    `rdSharedStm`: the statement of a shared chain (R13.5, R14.9).
    `sealName`, `rdSealItems`: the statement of a second chain: two seals (R13.5, R14.10).
    `copyOf`, `rdStoredCopy`, `wordsName`, `ProofStm.hashed`, `ProofStm.read`: the statement of a
      proof file's first chain (R14.3).
    `firstName`, `Which.firstName`: the name of a statement's first item.

2. What is checked when the file compiles. Nothing but the types. Tests: Fmt/TestChainStm.lean.

3. Theorems. None. Fmt/ChainStmLaws.lean.

4. What is not claimed.
   No reader is a verifier, and no verifier calls one. A statement's bytes are computed by whoever
   checks a chain, from values that it has.
   The reply (`ProofStm.reply`) is no item of a statement (R14.8): `ProofStm.bytes` does not read
   that field, and `ProofStm.read` gives the four other fields alone (`ProofStm.hashed`).
   Two of the four are strings of bytes: `request` is the VALUE OF THE ITEM "request" (what the
   function of Fmt/RequestItem.lean makes of the parameter file, the scale file and the request
   file), `words` is THE REQUEST FILE's OWN BYTES. No reader here holds one against the other.
   `UserStm.request` (Decl/Declared.lean) has that file as a list of words of four bytes; that
   `words` spells that list is said nowhere here.
   `rdSealItems` reads two seals, as many as a second chain's statement has;
   `sealItems` writes any number.
   The test "fewer than 2 ^ 64 bytes" (`wholeStm`) is reached by no test: no such string can be
   made. What it does is told by the laws alone.
   Nothing here on the statement of the chain of a record's seeds (`recordStm`, Fmt/ChainStm.lean: a
   table's name, and no list of items) nor on that of an entry's link (`EntryStm.bytes`): their
   readers are in Fmt/ChainStmMore.lean.
   Inside a declaration whose name begins with TableSt., the bare names item, readItem and item_size
   mean `TableSt.item`, `TableSt.readItem` and `TableSt.item_size` (Fmt/ChainStmLaws.lean), not the
   library's `item` (Fmt/Rules4.lean), `readItem` (Fmt/Rules8.lean) and `item_size`
   (Fmt/ParamsReadLawsProofs.lean).

-/
import Fmt.ChainStm
import Fmt.ParsedRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-! ## Three tools of no one type -/

/-- A reader, refused where the test p on its value fails. -/
def rdIf {α : Type} (p : α → Bool) (r : Rd α) : Rd α := fun b i =>
  match r b i with
  | some (x, j) => if p x then some (x, j) else none
  | none => none

/-- An item (R4.1) of the name "name". The item is read by the library's reader `rdItem`; refused
at another name; then r reads the item's value from its first byte, and is refused unless it ends
behind the value's last byte (`whole`). -/
def rdNamed {α : Type} (name : String) (r : Rd α) : Rd α := fun b i =>
  match rdItem b i with
  | some (x, j) => if x.1 == name then (whole r x.2).map fun y => (y, j) else none
  | none => none

/-- A reader on a whole statement. Refused if the string has 2 ^ 64 bytes or more: a statement's
length is one word in the first query (`firstBytes`, Fmt/Rules4.lean). This is the bound of the
spelling (`u64n` takes a number modulo 2 ^ 64), not the format's: the page admits at most 2 ^ 32 -
144 bytes of hashed string (R2.3, R2.7; `Spec.small`, Fmt/Rules8.lean). Refused if bytes are left
(`whole`). -/
def wholeStm {α : Type} (r : Rd α) (b : ByteArray) : Option α :=
  if b.size < 2 ^ 64 then whole r b else none

/-! ## A table -/

/-- The value of a table's item (R4.6): the root as a string of bytes, then the list of the answers,
each refused unless it is canonical in the field f (R1.4). Refused unless the table has the form
`TableSt.ok`: a root of 32 bytes, as many answers as the shape s says, and (tested a second time)
canonical answers. -/
def rdTableValue (f : Fld) (s : TableShape) : Rd TableSt :=
  rdIf (TableSt.ok f s) (rdMap (fun x => ⟨x.1, x.2⟩) (rdPair rdText (rdList (rdExt f))))

/-- The item of a table under a given name: the reader of `tableItem` (Fmt/Rules4.lean). -/
def rdTableItem (name : String) (f : Fld) (s : TableShape) : Rd TableSt :=
  rdNamed name (rdTableValue f s)

/-! ## The four statements -/

/-- The statement of a key file's one-time chain (R13.5): the reader of `TableSt.item`. One item,
"table", and no byte behind it; fewer than 2 ^ 64 bytes. -/
def TableSt.readItem (f : Fld) (s : TableShape) : ByteArray → Option TableSt :=
  wholeStm (rdTableItem "table" f s)

/-- The statement of a shared chain (R13.5, R14.9): the reader of `sharedStm`. The item "table",
then the binding tree's root, of 32 bytes, and no byte behind it; fewer than 2 ^ 64 bytes. -/
def rdSharedStm (f : Fld) (s : TableShape) : ByteArray → Option (TableSt × ByteArray) :=
  wholeStm (rdPair (rdTableItem "table" f s) (rdNamed bindRootName rdDigest))

/-- The name of the item `sealItem` (Fmt/Rules4.lean), which has it as a literal. That the two are
the same name: `sealItem_name` (Fmt/ChainStmLaws.lean). -/
def sealName : String := "the seal of an earlier chain"

/-- The statement of a second chain (R13.5, R14.10): the reader of `sealItems` at two seals. Two
items of the name `sealName`, each with a value of 32 bytes, and no byte behind them. (The test on
2 ^ 64 bytes is made here too; what passes the others has 152 bytes.) -/
def rdSealItems : ByteArray → Option (ByteArray × ByteArray) :=
  wholeStm (rdPair (rdNamed sealName rdDigest) (rdNamed sealName rdDigest))

/-- The number of a stored copy from a word's value: refused from 2 ^ 32 on. -/
def copyOf (n : Nat) : Option UInt32 := if n < 2 ^ 32 then some (UInt32.ofNat n) else none

/-- The value of the item "stored copy": one word, below 2 ^ 32. -/
def rdStoredCopy : Rd UInt32 := rdEnum copyOf

/-- The name of the fourth item of the statement of a proof's first chain, which `ProofStm.bytes`
(Fmt/Parsed.lean) has as a literal. That the two are the same name: `ProofStm.bytes_pair`
(Fmt/ChainStmLaws.lean). Place: 10-proof-file.md 10.2, R14.3, item 4 of the statement. -/
def wordsName : String := "the request file's words"

/-- The four fields of which `ProofStm.bytes` is written: all but the reply, which is no item of a
statement (R14.8). In this order: the table; the stored copy's number; the value of the item
"request" (`request`); the request file's own bytes (`words`). -/
def ProofStm.hashed (x : ProofStm) : TableSt × UInt32 × ByteArray × ByteArray :=
  (x.table, x.copy, x.request, x.words)

/-- The statement of a proof file's first chain (R14.3): the reader of `ProofStm.bytes`. The items
"table", "stored copy", "request" and `wordsName`, in this order, and no byte behind them. The
values of the last two are strings of bytes: a word for the length, then as many bytes, and no byte
behind them. The third value returned is the item "request"'s, the fourth the request file's own
bytes. Fewer than 2 ^ 64 bytes in all. -/
def ProofStm.read (f : Fld) (s : TableShape) :
    ByteArray → Option (TableSt × UInt32 × ByteArray × ByteArray) :=
  wholeStm (rdPair (rdTableItem "table" f s)
    (rdPair (rdNamed "stored copy" rdStoredCopy)
      (rdPair (rdNamed "request" rdText) (rdNamed wordsName rdText))))

/-! ## The first item's name -/

/-- The name of the item at the beginning of a string, as the library's reader of items reads it. -/
def firstName (b : ByteArray) : Option String := (rdItem b 0).map fun x => x.1.1

/-- The name of the first item of the statement of each chain, in a key file and
in a proof file alike. -/
def Which.firstName : Which → String
  | .first => "table"
  | .shared => "table"
  | .second => sealName

end Fmt

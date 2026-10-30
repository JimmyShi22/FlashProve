-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Fmt/ParsedReadFile.lean: readers of a whole key file, entry file and proof file by the numbers:
from the declared structure and the numbers that hang on the draws to the record of what stands in
the file. Definitions only.

Fmt/ParsedRead.lean has a reader of one chain that is told the chain's numbers
(`ChainParsed.counts`). A file has more than its chains: a head, a table, a slot in a binding tree,
a word (Fmt/ParsedTypes.lean). All of these have lengths that the declared structure fixes. So a
reader of a whole file needs the declared structure and the numbers of the file's chains, and
nothing else. The readers here are the other side of the writers `EntryParsed.bytes`,
`KeyParsed.bytes` and `ProofParsed.bytes` (Fmt/Parsed.lean). Their laws:
Fmt/ParsedReadFileLaws.lean.

Sources. The format page that ships: docs/format/FORMAT.md (7.6, R13.1, R13.2; 7.7, R13.3; 7.8,
R14.1, R14.2). Rule numbers are that page's. No Mathlib, neither directly nor through the imports.

1. What the file contains.
    `ChainCounts`: a chain's numbers, as `ChainParsed.counts` gives them. `ThreeCounts`: three
      chains'.
    `EntryParsed.counts`, `KeyParsed.counts`, `ProofParsed.counts`: a file's numbers: its chains',
      in the file's order.
    `rdTable`: a table in a file: the root, bare; as many answers as the shape says (R13.2, R13.3).
    `rdSlot`: a slot in a binding tree: the word, the salt, one digest a level (R13.2, R14.1).
    `rdCopy`: the four bytes behind a proof file's first eight (R14.2).
    `rdThree`: the three chains of a key file or of a proof file, with the slot between the first
      two (R13.2, R14.1).
    `EntryParsed.rd`, `KeyParsed.rd`, `ProofParsed.rd`: the parts of a file, in the file's order,
      from a place on.
    `EntryParsed.read`, `KeyParsed.read`, `ProofParsed.read`: a whole file: the parts; refused
      unless the record fits the declared structure (`EntryParsed.fits` and its likes); refused if
      a byte is left.
    `EntryParsed.of`, `KeyParsed.of`, `ProofParsed.of`, with `threeOf`: a file's record, from the
      parts that are in no chain and what a reader of this library holds of each chain (`ChainOut`,
      Fmt/Rules8.lean; `ChainParsed.of`, Fmt/Parsed.lean).

2. What is checked when the file compiles. Only the types. Tests: Fmt/ParsedReadFileKnown.lean
[not in this library]; so here read: not tested in this library.

3. Theorems. None.

4. What is not claimed.
   These readers are no verifiers and no cuts of a file: whoever calls them must have the numbers,
   and the right numbers follow from the draws alone, chain by chain (Fmt/Rules8X.lean;
   Run/ParseLaxX.lean). At other numbers they cut the same bytes in another way, or refuse.
   They test the form (`fits`) and nothing else: no hash is called, no root, path, seal or proof of
   work is looked at. They do not test the declared structure.
   The first eight bytes are read as they stand and then held against the declared head by `fits`.
   The number of a table's answers, 2 ^ logRows times the answers of a row, is computed before
   anything is tested: the declared structure is the caller's own and no input.
   Stack: as in the head of Fmt/ParsedRead.lean, 4; a table's answers and a slot's path are read by
   `rdMany`.
   The same cuts in other readers of this library; none is tied to these by a statement, and files
   of Fmt/ import no file of OnBytes/ or Run/. A table: `OnBytes.readTable`
   (OnBytes/Entry/Table.lean), behind the head `OnBytes.Key.readTable` (OnBytes/Key/Table.lean). A
   slot, with the test "below 2 ^ depth" of `SlotParsed.fits`: `OnBytes.Proof.readPlace`
   (OnBytes/Proof/Place.lean), which hashes as it goes. The head and the four bytes:
   `OnBytes.Proof.readHead`, `word32At`, `readProofHead` (OnBytes/Proof/Head.lean). The first 40
   bytes of a file whose table has no stored answer: `M3.keyRoot` (Fmt/M3Entry.lean);
   `Run.PQ.readHead` (Run/PlanQXRun.lean).
   `•.of` takes the head, the table, the slot and the four bytes as they are given: it tests
   nothing.

Terms: lean/GLOSSARY.md.
-/
import Fmt.ParsedRead

namespace Fmt

/-- A chain's numbers, round by round: of listed positions; of each opening's columns and given
digests. -/
abbrev ChainCounts : Type := List (Nat × List (Nat × Nat))

/-- the numbers of the three chains of a key file or of a proof file, in the file's order -/
abbrev ThreeCounts : Type := ChainCounts × ChainCounts × ChainCounts

/-- an entry file's numbers: its link's -/
def EntryParsed.counts (F : EntryParsed) : ChainCounts := F.link.counts

/-- a key file's numbers: its three chains', in the file's order -/
def KeyParsed.counts (F : KeyParsed) : ThreeCounts :=
  (F.first.counts, F.shared.counts, F.second.counts)

/-- a proof file's numbers: its three chains', in the file's order -/
def ProofParsed.counts (F : ProofParsed) : ThreeCounts :=
  (F.first.counts, F.shared.counts, F.second.counts)

/-- A table in a file (R13.2, R13.3): the root, bare; the stored answers, as many as the shape
says. -/
def rdTable (f : Fld) (s : TableShape) : Rd TableSt :=
  rdMap (fun x => ⟨x.1, x.2⟩) (rdPair rdDigest (rdMany (rdExt f) s.count))

/-- A slot in a binding tree: the word, the salt, one digest for each level. -/
def rdSlot (s : BindShape) : Rd SlotParsed :=
  rdMap (fun x => ⟨x.1, x.2.1, x.2.2⟩)
    (rdPair rdWord (rdPair (rdBytes s.saltBytes) (rdMany rdDigest s.depth)))

/-- Four bytes as a number, the lowest first (R14.2). -/
def rdCopy : Rd UInt32 := rdMap UInt32.ofNat (readLE 4)

/-- The three chains of a key file or of a proof file, with the slot between the first two. N: the
chains' numbers. -/
def rdThree (D : Declared) (T : ThreeDecl) (N : ThreeCounts) :
    Rd (ChainParsed × SlotParsed × ChainParsed × ChainParsed) :=
  rdPair (ChainParsed.read D.setting T.first N.1)
    (rdPair (rdSlot T.bind)
      (rdPair (ChainParsed.read D.setting T.shared N.2.1)
        (ChainParsed.read D.setting T.second N.2.2)))

/-- An entry file's parts (R13.3): eight bytes, the further table, the link's chain. -/
def EntryParsed.rd (D : Declared) (N : ChainCounts) : Rd EntryParsed :=
  rdMap (fun x => ⟨x.1, x.2.1, x.2.2⟩)
    (rdPair (rdBytes 8)
      (rdPair (rdTable D.setting.field D.table) (ChainParsed.read D.setting D.link N)))

/-- A key file's parts (R13.2): eight bytes, the first table, the three chains with the slot. -/
def KeyParsed.rd (D : Declared) (N : ThreeCounts) : Rd KeyParsed :=
  rdMap (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩)
    (rdPair (rdBytes 8) (rdPair (rdTable D.setting.field D.table) (rdThree D D.key N)))

/-- A proof file's parts (R14.1, R14.2): eight bytes, four bytes, the three chains with the slot. -/
def ProofParsed.rd (D : Declared) (N : ThreeCounts) : Rd ProofParsed :=
  rdMap (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩)
    (rdPair (rdBytes 8) (rdPair rdCopy (rdThree D D.proof N)))

/-- A whole entry file, told its numbers: refused unless the record fits; refused if a byte is
left. -/
def EntryParsed.read (D : Declared) (N : ChainCounts) (file : ByteArray) : Option EntryParsed :=
  whole (rdFit (fun F => F.fits D) (EntryParsed.rd D N)) file

/-- A whole key file, told its numbers. -/
def KeyParsed.read (D : Declared) (N : ThreeCounts) (file : ByteArray) :
    Option KeyParsed :=
  whole (rdFit (fun F => F.fits D) (KeyParsed.rd D N)) file

/-- A whole proof file, told its numbers. -/
def ProofParsed.read (D : Declared) (N : ThreeCounts) (file : ByteArray) :
    Option ProofParsed :=
  whole (rdFit (fun F => F.fits D) (ProofParsed.rd D N)) file

/-! ## From a reader of this library -/

/-- An entry file's record: the head and the table as given; the link's chain from what a reader
holds of it. rand: the chain's random bytes, if they stand in the file. -/
def EntryParsed.of (D : Declared) (head : ByteArray) (t : TableSt) (rand : Option ByteArray)
    (o : ChainOut) : Option EntryParsed :=
  (ChainParsed.of (D.plan D.link) rand o).map fun c => ⟨head, t, c⟩

/-- The three chains of a key file or of a proof file, each from its random bytes in the file, if
any, and what a reader holds of it. -/
def threeOf (D : Declared) (T : ThreeDecl) (x1 x2 x3 : Option ByteArray × ChainOut) :
    Option (ChainParsed × ChainParsed × ChainParsed) :=
  (ChainParsed.of (D.plan T.first) x1.1 x1.2).bind fun a =>
    (ChainParsed.of (D.plan T.shared) x2.1 x2.2).bind fun b =>
      (ChainParsed.of (D.plan T.second) x3.1 x3.2).map fun c => (a, b, c)

/-- A key file's record. -/
def KeyParsed.of (D : Declared) (head : ByteArray) (t : TableSt) (s : SlotParsed)
    (x1 x2 x3 : Option ByteArray × ChainOut) : Option KeyParsed :=
  (threeOf D D.key x1 x2 x3).map fun y => ⟨head, t, y.1, s, y.2.1, y.2.2⟩

/-- A proof file's record. -/
def ProofParsed.of (D : Declared) (head : ByteArray) (copy : UInt32) (s : SlotParsed)
    (x1 x2 x3 : Option ByteArray × ChainOut) : Option ProofParsed :=
  (threeOf D D.proof x1 x2 x3).map fun y => ⟨head, copy, y.1, s, y.2.1, y.2.2⟩

end Fmt

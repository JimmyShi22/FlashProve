-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParsedTypes.lean: the records of what stands in a key file, an entry file and a proof file, and
of nothing else. Types only.

The programs (the C++ implementation that comes with this Lean code) write these files as bytes
without lengths, names or separators. A converter is a program that turns the bytes into typed
values; it need not be trusted. This file says into which values it first cuts them. Every field is
a part of a file as the format page lays it out, in the file's order, and its comment names its
place there ("Place").

Sources. The format page that ships: docs/format/FORMAT.md (sections 6.1, 6.3, 6.6, 7.2 to 7.8),
docs/format/09-key-and-leaf-files.md (9.4, 9.8) and docs/format/10-proof-file.md (R14.7). Rule
numbers are that page's. The file imports Decl/Declared.lean alone (for `TableSt`), below which
no Mathlib lies.

1. What the file contains.
    `OpenParsed`: one opening (R7.8).
    `RoundParsed`: what one round has in a file (R8.2, R8.7).
    `ChainParsed`: a chain (R8.1).
    `SlotParsed`: a slot in a binding tree (R13.2, R14.1, R14.7).
    `KeyParsed`, `EntryParsed`, `ProofParsed`: the three files (R13.2, R13.3, R14.1).

2. What is checked when the file compiles. Only the types.

3. Theorems. None.

4. What is not claimed, and what is not here.
   The functions on these types (writers, tests of form, what a reader of this library holds):
   Fmt/Parsed.lean.
   A parsed record is not the input of the compiled verifier (`OneProtocolProof`, Compile/Batch/Verifier.lean).
   Three things that the typed string holds stand in no file and are made with the hash: the run's
   values, each opening's list of positions, and whole paths. A salt in a parsed record is the
   file's: it has no prefix.
   A parsed record has more than the file's bytes: the cut itself. The kind of an item is not in
   the file (an element of E and an answer have 24 bytes alike, an element of F and a word 8); nor
   the number of rounds (a round without a byte is an empty member); nor where one list ends and
   the next begins, or whether eight bytes are a nonce or a listed position. All of it is the
   description's; `fits` (Fmt/Parsed.lean) holds the record against it in kinds, widths, canonical
   forms and the numbers that the declared structure fixes.
   Nothing of a parsed record is trusted by anybody: it is a converter's value.
   The plan's entry RECORD is no round, and nothing of it stands in a file (R13.15).
   The compiler's side has an opening with its depth and its list: `Run.OpenB` (Run/ParseBS.lean).

Terms: lean/GLOSSARY.md.

-/
import Decl.Declared

namespace Fmt

/-- One opening as it stands in a file. No position and no count stands there. -/
structure OpenParsed where
  /-- For each position of the opening's list, by increasing position: the column, elements of F,
  and that leaf's salt. The fill of a leaf is in no file.
  Place: FORMAT.md 6.3, R7.8; 6.1, R7.1, R7.3. -/
  cols  : List (List UInt64 × ByteArray)
  /-- The given digests, 32 bytes each, in the walk's order: level by level from the leaves up, in
  a level from left to right.
  Place: FORMAT.md 6.3, R7.8, R7.9. -/
  given : List ByteArray
  deriving DecidableEq, Inhabited

/-- What one round of a chain has in a file, in the file's order. -/
structure RoundParsed where
  /-- The prover's message, cut into its items; empty where the prover sends nothing. An item's
  kind is the description's and stands in no file.
  Place: FORMAT.md 7.2, R8.1, R8.2; 7.3, R8.8; 09-key-and-leaf-files.md 9.8, R13.10; 9.4, R12.9. -/
  vals   : List ItemValue
  /-- The nonce: there is one exactly where the plan's entry has proof-of-work bits. In the three
  files it has eight bytes.
  Place: FORMAT.md 7.2, R8.2; 7.4, R8.7. -/
  nonce  : Option UInt64
  /-- The listed positions, in increasing order, each once: one list for the round. Empty where the
  plan lists none or the round samples none.
  Place: FORMAT.md 7.2, R8.2; 7.4, R8.7; 6.6, R7.19. -/
  listed : List UInt64
  /-- The openings: the stored trees' first, in the order of the statement's items that hold their
  roots; then the other trees', by increasing place. An opening does not say of which tree it is:
  the order is content.
  Place: FORMAT.md 7.4, R8.7; 7.7; 6.6, R7.19. -/
  opens  : List OpenParsed
  deriving DecidableEq, Inhabited

/-- A chain as it stands in a file. -/
structure ChainParsed where
  /-- The chain's 32 random bytes, where they stand in the file: then they are its first item. They
  enter the run's value and no other hash.
  Place: FORMAT.md 7.2, R8.2; 4.1, R4.5 (a); 7.6, R13.2; 7.7, R13.3; 7.8, R14.1. -/
  rand   : Option ByteArray
  /-- The chain's rounds, in order. A round without a byte in the file is a member all the same:
  the number of rounds is the description's. The plan's entry under the name RECORD is no round
  (R13.15) and has no member.
  Place: FORMAT.md 7.2, R8.1; 09-key-and-leaf-files.md 9.8, R13.10. -/
  rounds : List RoundParsed
  deriving DecidableEq, Inhabited

/-- A slot in a binding tree, as it stands between a file's first chain and its shared chain. -/
structure SlotParsed where
  /-- the slot itself: one word.
  Place: FORMAT.md 7.6, R13.2; 7.8, R14.1; 09-key-and-leaf-files.md 9.7, R13.6; 10-proof-file.md
  10.4, R14.7. -/
  place : UInt64
  /-- the salt of that slot's leaf.
  Place: FORMAT.md 7.6, R13.2; 7.8; 10-proof-file.md 10.4, R14.7; R14.6. -/
  salt  : ByteArray
  /-- one digest for each level of the tree, the leaf's sibling first.
  Place: FORMAT.md 7.8; 10-proof-file.md 10.4, R14.7. -/
  path  : List ByteArray
  deriving DecidableEq, Inhabited

/-- A key file. -/
structure KeyParsed where
  /-- the eight bytes of the head: the kind CPIK, the version. Place: FORMAT.md 7.6, R13.1. -/
  head   : ByteArray
  /-- the first table (the anchor). Place: FORMAT.md 7.6, R13.2. -/
  table  : TableSt
  /-- the one-time chain. Place: FORMAT.md 7.6, R13.2. -/
  first  : ChainParsed
  /-- the slot. Place: FORMAT.md 7.6, R13.2. -/
  slot   : SlotParsed
  /-- the shared chain. Place: FORMAT.md 7.6, R13.2. -/
  shared : ChainParsed
  /-- the second chain. Place: FORMAT.md 7.6, R13.2. -/
  second : ChainParsed
  deriving DecidableEq, Inhabited

/-- An entry file (docs/format/ calls it the leaf file). Its one chain is the link. -/
structure EntryParsed where
  /-- The eight bytes of the head: the kind CPEN, the version. They enter no hash.
  Place: FORMAT.md 7.6, R13.1. -/
  head  : ByteArray
  /-- The further table (the leaf table): its root, then the stored answers of its record.
  Place: FORMAT.md 7.7, R13.3. -/
  table : TableSt
  /-- The link's chain, with which the file ends.
  Place: FORMAT.md 7.7, R13.3. -/
  link  : ChainParsed
  deriving DecidableEq, Inhabited

/-- A proof file. -/
structure ProofParsed where
  /-- the first eight bytes of the head: the kind CPPF, the version. Place: FORMAT.md 7.8, R14.2. -/
  head   : ByteArray
  /-- the head's last four bytes: the number under which the further table is kept on which the
  proof was made. Place: FORMAT.md 7.8, R14.2. -/
  copy   : UInt32
  /-- the request's first chain. Place: FORMAT.md 7.8, R14.1. -/
  first  : ChainParsed
  /-- the request's slot in its batch. Place: FORMAT.md 7.8, R14.1. -/
  slot   : SlotParsed
  /-- the batch's shared chain. Place: FORMAT.md 7.8, R14.1. -/
  shared : ChainParsed
  /-- the request's second chain. Place: FORMAT.md 7.8, R14.1. -/
  second : ChainParsed
  deriving DecidableEq, Inhabited

end Fmt

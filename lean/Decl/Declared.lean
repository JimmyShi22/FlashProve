-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Decl/Declared.lean: the declared structure: what is public before any proof, and the statements.
Types, and the functions from a round's name to its kind, from an entry to the cut of its message,
and from the declared rounds to a plan.

The programs (the C++ implementation that comes with this Lean code) write three kinds of file: a
key file, an entry file (the format page's leaf file) and a proof file. What a verifier must know
before it opens one of them follows from the public files. This file says which values these are. It
is the one place for these types, so that a description of the protocol, a coding of typed queries,
a converter and a reader of this library all take the same thing as their argument. Nothing is
invented here: every field is a word of a public parameter, or a part of a statement, as the format
page lays it out, and its comment names its place there ("Place"). The file lies in the directory
Decl/; its names stand in the namespace `Fmt`, with the functions on them (Fmt/Parsed.lean).

Sources. The format page that ships: docs/format/FORMAT.md (sections 4.1, 6.3 to 6.6, 7.1 to 7.8,
12.1 to 12.4, 13.5, and of section 18 the items on public inputs and on one setting),
docs/format/09-key-and-leaf-files.md (sections 9.5 to 9.8; R12.9, R13.11),
docs/format/10-proof-file.md (sections 10.1, 10.2 to R14.3, 10.4 to 10.7; R14.6, R14.8) and
docs/format/11-1-machinery.md (its paragraphs on scalars). Rule numbers are that page's. The file
imports Fmt/Rules8X.lean, for nine types of the byte format that lie in five files of Fmt/ (`Fld`,
`Ext`, `Kind`, `Entry`, `Plan`, `Shape`, `Item`, `ItemValue`, `Stored`); no Mathlib
is below it.
It has no test and no
theorem.

1. What the file contains.
   Five groups, each under its own heading below: what is public; from a round's name to its kind;
   from an entry's words to the cut of its message; from the declared rounds to the plan; the
   statements.

2. What is checked when the file compiles. Only the types.

3. Theorems. None.

4. What is not claimed, and what is not here.
   The records of what stands in the three files: Fmt/ParsedTypes.lean. The functions on all these
   types: Fmt/Parsed.lean. The value of `Declared` at given public files: not in this file. The
   planner that derives plans and shapes from the public files lies under OnBytes/Params/
   (OnBytes/Params/Planner.lean); it gives no value of `Declared`.
   No value of the format's hash is a field. The configuration's digest is a hash of the public
   files, and every chain's parameter bytes hold it. By the format page (section 18, part of R4.9) a
   model must not fix such bytes before the hash is chosen: what is fixed before is the text of the
   public files and whatever follows from it without a hash. So the files' text is a field, and the
   digest and the parameter bytes are functions of it and of the hash (Fmt/Parsed.lean). By that
   section's list the item "configuration" is the one parameter item that is a hash; the further
   items (`ChainDecl.others`) are words, names and field elements (R13.5 to R13.14, R14.3). The
   parameter file's text can hold digests under the second hash (R15.3, R15.6): these are text.
   What is told once here so that it cannot differ: a round's entry and the plan; a round's name and
   its kind; an entry's numbers and the cut of its message; the setting (one for all chains); the
   plan's entry RECORD (it follows from the tables' shape, R13.15). What is told twice, and by
   which test it is compared: `Declared.entryFormOk`, `Declared.chainsFormOk` (Fmt/Parsed.lean). A
   verifier is meant to compute the declared structure from its own copy of the public files and
   never to take it as an input; a statement that speaks of an arbitrary declared structure is meant
   to take these tests as its premise (for a key file and a proof file, `Declared.keyFormOk` and
   `Declared.proofFormOk`, which call `Declared.chainsFormOk`). Neither is in this file: no function
   from the public files to a declared structure, and no theorem with one of these tests as a
   premise. The two theorems of Fmt/ChainStmSmall.lean that take `Declared.entryFormOk` as a premise
   have no premise that ties the declared structure to the public files, and a made-up one can pass
   that test (Fmt/Parsed.lean, at `Declared.entryFormOk`). That the fields which these tests do not
   compare are what the planner derives from `files` can be tested only where the planner lies. How
   `ProofStm.request` follows from the public files and `UserStm.request` (R15.5, with the second
   hash) is not here: the port has it (OnBytes/Proof/RequestItem.lean). That `ProofStm.words` spells
   `UserStm.request` is not here either: the test is in Fmt/RequestItem.lean.
   The same things in other types of this library. The port: `Params.TableName`, `Params.Rounds`
   (OnBytes/Params/Chains.lean), `Params.Given` (OnBytes/Params/Given.lean), `Params.IndexShape`,
   `Params.LinBindingShape` (OnBytes/Params/Items.lean), `Params.kindOf` with its seven lists
   (OnBytes/Params/Names.lean), the entry RECORD (OnBytes/Params/Planner.lean). The readers:
   `Params` (Fmt/ParamsRead.lean), `Round`, `Src`, `Spec` (Fmt/Rules8.lean), `SpecX`
   (Fmt/Rules8X.lean). The compiler's side: `Run.PQ.XD` (Run/PlanQXRun.lean), `Run.PQ.RD`
   (Run/PlanQTypes.lean). The readers' types lie below this file, which imports Fmt/Rules8X.lean,
   and are not used in it; the others lie above it or beside it. All are named, none is used.

Terms: lean/GLOSSARY.md.

-/
import Fmt.Rules8X

namespace Fmt

/-! ## What is public
Fixed by the text of the public files, without a hash, before any proof. -/

/-- The tables' shape: the six words of a table's name, in the page's order. The first table and
all further tables have one shape. It is the beginning of the parameter items "the link" (R13.9) and
"the test on the table" (R13.13). -/
structure TableShape where
  /-- rows have length 2 ^ a; the tree's depth. Place: FORMAT.md 4.1, R4.10. -/
  a         : Nat
  /-- the entries of a row's message, pads among them. Place: FORMAT.md 4.1, R4.10. -/
  message   : Nat
  /-- the entries of a row's random tail. Place: FORMAT.md 4.1, R4.10. -/
  tail      : Nat
  /-- the table has 2 ^ logRows rows, so a column has as many symbols.
  Place: FORMAT.md 4.1, R4.10. -/
  logRows   : Nat
  /-- the stored answers for each row. Place: FORMAT.md 4.1, R4.10. -/
  answers   : Nat
  /-- the bytes of a leaf's salt in a table's tree. Place: FORMAT.md 4.1, R4.10. -/
  saltBytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Where a chain's 32 random bytes come from (R4.5): (a) they are the chain's first bytes in its
file; (b) they are the value of the statement's item number k, from 0; (c) there are none. -/
inductive RandAt where
  | inFile
  | item (k : Nat)
  | none
  deriving DecidableEq, Repr, Inhabited

/-- Whose tree a round opens (R7.13): the n-th tree whose root this chain sends, from 0; or a tree
that the chain has taken over: the one whose root was sent as number "sent", from 0, on chain number
"chain", from 0, of the same file. Its start is the sender's run's value (R7.4). The first two
chains of a file begin with an empty list of trees and take none over, so "sent" is also the tree's
number in its leaves' hashes (R7.13). It names the tree; the root and the start are values of one
proof. -/
inductive TreeSource where
  | own (n : Nat)
  | taken (chain sent : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The setting: six of the eight words at the head of a plan, in the page's order. The second word,
the hash, is 1; the eighth is the number of entries. The plans of all seven chains of the three
files are made under one setting (FORMAT.md 18, "One setting"). -/
structure PlanSetting where
  /-- the field. Place: FORMAT.md 4.1, R4.3. -/
  field   : Fld
  /-- the bytes of a leaf's salt. Place: FORMAT.md 4.1, R4.3; 6.1, R7.3. -/
  salt    : Nat
  /-- the bytes of a nonce in a file. Place: FORMAT.md 4.1, R4.3; 7.2, R8.2. -/
  nonce   : Nat
  /-- the bytes of a listed position; 0: none is listed. Place: FORMAT.md 4.1, R4.3; 7.2, R8.2. -/
  posB    : Nat
  /-- the answers to each out-of-domain sample. Place: FORMAT.md 4.1, R4.3. -/
  samples : Nat
  /-- whether a sum-check's message leaves out the coefficient that the check fixes: 1 in every plan
  of the format. Place: FORMAT.md 4.1, R4.3. -/
  saved   : Nat
  deriving DecidableEq, Repr

/-- A round: its entry of the plan, and what a reader must be told beside it. The round's kind is no
field: it follows from the entry's name (`kindOf`). How its message is cut into items is no field:
it follows from three of the entry's words (`Entry.cut`). -/
structure DeclaredRound where
  /-- the round's entry of the plan: its name and eleven words. Place: FORMAT.md 4.1, R4.3. -/
  entry  : Entry
  /-- the stored trees that the round opens, in the order of the statement's items, each with its
  part of the draws. Place: FORMAT.md 7.4, R8.7; 6.6, R7.19. -/
  stored : List Stored := []
  /-- the other trees that it opens, by increasing place in the chain's list.
  Place: FORMAT.md 7.4, R8.7; 6.4, R7.13; 09-key-and-leaf-files.md 9.7, R13.12. -/
  opens  : List (Shape × TreeSource) := []
  deriving DecidableEq, Inhabited

/-- A chain, as far as the public files fix it. It holds neither its statement nor the
configuration's digest, so not its parameter bytes either, which hold that digest. -/
structure ChainDecl where
  /-- the chain's label.
  Place: 09-key-and-leaf-files.md 9.6, R13.4; 10-proof-file.md R14.3, R14.9, R14.10. -/
  label     : Nat
  /-- Whether this is a chain whose plan begins with the entry RECORD if tables have a record: a
  link's chain, a key file's one-time chain. The flag says which chain it is; whether tables have a
  record is the shape's fifth word.
  Place: 09-key-and-leaf-files.md 9.6, R13.15. -/
  record    : Bool := false
  /-- the parameter items behind the item "configuration", each with its name and its value's
  bytes. Place: FORMAT.md 4.1, R4.3; 09-key-and-leaf-files.md 9.6, R13.5. -/
  others    : List (String × ByteArray)
  /-- the case of the random bytes. Place: FORMAT.md 4.1, R4.5; 7.8, the table at its end. -/
  rand      : RandAt
  /-- the number of the first tree that the chain sends itself. Place: FORMAT.md 6.4, R7.13. -/
  firstTree : Nat := 0
  /-- the rounds. Place: 09-key-and-leaf-files.md 9.7, 9.8; FORMAT.md 7.8. -/
  rounds    : List DeclaredRound
  deriving DecidableEq, Inhabited

/-- The shape of a binding tree: the two words of the parameter item "binding tree". -/
structure BindShape where
  /-- the tree's depth. Place: 09-key-and-leaf-files.md 9.6, R13.5; 10-proof-file.md R14.6. -/
  depth     : Nat
  /-- the bytes of a leaf's salt.
  Place: 09-key-and-leaf-files.md 9.6, R13.5; 10-proof-file.md R14.6. -/
  saltBytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The three chains of a key file or of a proof file, in the file's order. -/
structure ThreeDecl where
  /-- a key file's one-time chain; a proof file's first chain: chain number 0.
  Place: FORMAT.md 7.6, R13.2; 7.8, R14.1. -/
  first  : ChainDecl
  /-- the binding tree, whose slot stands between the first two chains. In a key file its depth is
  0. Place: FORMAT.md 6.5, R7.18; 09-key-and-leaf-files.md 9.7, R13.6; 10-proof-file.md R14.6. -/
  bind   : BindShape
  /-- the shared chain: chain number 1. Place: FORMAT.md 7.6, R13.2; 7.8, R14.1. -/
  shared : ChainDecl
  /-- the second chain: chain number 2. Place: FORMAT.md 7.6, R13.2; 7.8, R14.1. -/
  second : ChainDecl
  deriving DecidableEq, Inhabited

/-- The description's half of the declared structure. It has no field, so it has one value, which is
the default of the field `desc` of `Declared`: a value of `Declared` need not name it, and two
values of `Declared` never differ in it.
-/
structure DescDecl where
  deriving DecidableEq, Repr, Inhabited

/-- The declared structure. A part that is not given is its type's default: chains without a round
and with the label 0, which the tests on the declared structure (Fmt/Parsed.lean) refuse. Data
alone: no field is a proposition, none is chosen, and none is a value of the format's hash. -/
structure Declared where
  /-- The public files, each as its bytes, in the order in which the configuration's digest takes
  them: the parameter file first; the programs take three: parameter file, layout file, scale file.
  Place: FORMAT.md 4.1, R4.9; 18, "Some public inputs are answers of the oracle". -/
  files   : List ByteArray
  /-- The setting. Place: FORMAT.md 4.1, R4.3. -/
  setting : PlanSetting
  /-- The tables' shape. Place: FORMAT.md 4.1, R4.10. -/
  table   : TableShape
  /-- The link's chain of an entry file. Place: 09-key-and-leaf-files.md 9.8. -/
  link    : ChainDecl := default
  /-- A key file's chains. Place: 09-key-and-leaf-files.md 9.7. -/
  key     : ThreeDecl := default
  /-- A proof file's chains. Place: FORMAT.md 7.8. -/
  proof   : ThreeDecl := default
  /-- The description's half. Place: no page says it (its fields say their own places). -/
  desc    : DescDecl := {}
  deriving DecidableEq

/-! ## From a round's name to its kind -/

/-- The names of the rounds in which the verifier draws elements of the extension field. -/
def namesElems : List String :=
  ["BAT", "BAT-sigma", "PSC round", "PSC Y", "ZERO", "LINE", "LKP shift", "JOIN", "LKP",
   "FOLD round", "BASE lambda", "LIN point", "LIN zeta", "LINK point", "LINK phi"]

/-- The names of the rounds in which the verifier draws the element that joins a hiding
polynomial to a claim. -/
def namesJoin : List String := ["PSC epsilon", "FOLD epsilon"]

/-- The names of the rounds in which the verifier draws the seeds of out-of-domain samples. -/
def namesSeeds : List String := ["SEND seed"]

/-- The names of the rounds in which the verifier draws positions. -/
def namesPositions : List String := ["LOC", "CS", "BASE", "LINK"]

/-- The names of the rounds in which the verifier draws entries of a matrix over -1, 0, 1. -/
def namesEntries : List String := ["RNG"]

/-- The names of the rounds that end in a seal. -/
def namesSealed : List String := ["SEAL"]

/-- The names of the rounds in which the verifier says nothing. -/
def namesNothing : List String := ["SEND answer", "SPLIT", "PSC values", "REPLY", "LAST"]

/-- The kind of the round of a name, or nothing if the format has no round of this name (R14.11). A
first query holds the rounds' names and not their kinds (R4.3): so the kind under which a round is
run is computed from the name that is hashed. -/
def kindOf (name : String) : Option Kind :=
  if namesElems.contains name then some .elems
  else if namesJoin.contains name then some .join
  else if namesSeeds.contains name then some .seeds
  else if namesPositions.contains name then some .positions
  else if namesEntries.contains name then some .entries
  else if namesSealed.contains name then some .sealed
  else if namesNothing.contains name then some .nothing
  else none

/-! ## From an entry's words to the cut of its message -/

/-- How a prover's message is cut into items, from the entry's numbers of bytes, roots and answers.
By R8.8 the plan's entry gives lengths alone, and the list of items belongs to each protocol. For
the three files the list follows from four sentences of the format page: a message behind a round
that samples seeds begins with all answers (R8.3); the roots come before the other items (R13.11: in
every such message they are sent first); every item but a root is an element of E (R12.9, R13.10,
10-proof-file.md 10.6; of a sub-proof: 11-1-machinery.md, "Scalars and their numbers": apart from
roots and answers everything that it sends is scalars, elements of E); no message has a plain word
(R8.8). No page states the function itself. For a message with answers and roots together the first
two sentences meet, and no page says which yields; no table of rounds has such a message; the
answers stand first here because `Round.ok` (Fmt/Rules8.lean) asks so. -/
def Entry.cut (e : Entry) : List Item :=
  List.replicate e.answers .answer ++ List.replicate e.roots .root ++
    List.replicate ((e.msg - 24 * e.answers - 32 * e.roots) / 24) .e

/-- the cut of a round's message -/
def DeclaredRound.items (r : DeclaredRound) : List Item := r.entry.cut

/-! ## From the declared rounds to the plan -/

/-- The plan's entry under the name RECORD for tables of the shape s (R13.15): s.answers (c + 1)
elements are sampled, of which s.answers must not be 0, where c is the least number with 2 ^ c not
below the entries of a row's message. -/
def recordEntry (s : TableShape) : Entry :=
  { name := "RECORD"
    drawE := s.answers * ((if s.message ≤ 1 then 0 else Nat.log2 (s.message - 1) + 1) + 1)
    drawNZ := s.answers }

/-- The entries of a chain's plan: the entry RECORD, where the chain has it and tables have a
record; then the rounds' entries. -/
def Declared.entries (D : Declared) (c : ChainDecl) : List Entry :=
  (if c.record && D.table.answers != 0 then [recordEntry D.table] else []) ++ c.rounds.map (·.entry)

/-- What is hashed of the entries of a chain's plan into its first query (R4.3): for each entry its
name and its eleven words, in the page's order. (The eight words at the plan's head are hashed too:
`Declared.plan`.) It is computed from the declared rounds, the tables' shape and nothing else. (The
eleven words are `Entry.words`, Fmt/ParamsReadLaws.lean, which lies above this file; that an entry's
bytes are its name and these words is proved in Fmt/ParamsReadLawsProofs.lean.) -/
def Declared.planWords (D : Declared) (c : ChainDecl) : List (String × List Nat) :=
  (D.entries c).map fun e =>
    (e.name,
      [e.count, e.work, e.msg, e.roots, e.answers, e.drawE, e.drawNZ, e.poss, e.logN, e.trits,
        e.rows])

/-- The plan of a chain. A plan is no field and a kind is no field: what is hashed as the plan, and
the kind under which a round is run, are computed from the very rounds that are declared. -/
def Declared.plan (D : Declared) (c : ChainDecl) : Plan :=
  ⟨D.setting.field, D.setting.salt, D.setting.nonce, D.setting.posB, D.setting.samples,
    D.setting.saved, D.entries c⟩

/-! ## The statements -/

/-- A stored table as a statement and a file hold it. -/
structure TableSt where
  /-- The root of the table's tree: 32 bytes, any value. In a file it stands bare; in a statement's
  item as a string of bytes, behind the word 32.
  Place: FORMAT.md 7.7, R13.3; 7.6, R13.2; 4.1, R4.6. -/
  root    : ByteArray
  /-- The stored answers of the table's record: elements of E, by row and within a row by answer;
  their number stands in no file: it is the shape's.
  Place: FORMAT.md 7.6, R13.2; 09-key-and-leaf-files.md 9.5, R13.8. -/
  answers : List Ext := []
  deriving DecidableEq, Inhabited

/-- The statement of an entry file's link. -/
structure EntryStm where
  /-- The first table (the anchor). It is never taken from the entry file: a verifier has kept it
  from a key file. Place: 09-key-and-leaf-files.md 9.6, R13.5; FORMAT.md 7.7. -/
  first   : TableSt
  /-- The further table (the leaf table), whose root and answers the entry file holds.
  Place: 09-key-and-leaf-files.md 9.6, R13.5; FORMAT.md 7.7, R13.3. -/
  further : TableSt
  deriving DecidableEq, Inhabited

/-- What a proof file's chains are told from outside the file. (A key file's chains are told nothing
from outside: the one table in their statements is the file's own, `KeyParsed.table`. The check of a
key file is told the commitment ID: `UserStm.id`.) -/
structure ProofStm where
  /-- The further table on which the proof was made: the item "table" of the first and of the
  shared chain. It is read from that table's entry file, never from the proof file.
  Place: 10-proof-file.md 10.2, R14.3; 10.5, R14.9. -/
  table   : TableSt
  /-- The number under which that table is kept: the item "stored copy", one word. The proof file's
  head has it too. Place: 10-proof-file.md 10.2, R14.3; FORMAT.md 7.8, R14.2. -/
  copy    : UInt32
  /-- The value of the item "request": a string of bytes, whole, as the caller of the frame passes
  it in. In the programs, where the parameter file's line "prof" is 20: 177 words of four bytes,
  which each program makes for itself from the parameter file, the scale file and the request file.
  They hold a digest of the request file and not the file: the file's own bytes are `words`.
  Place: 10-proof-file.md 10.2, R14.3; FORMAT.md 12.3, R15.1, R15.5. -/
  request : ByteArray
  /-- The value of the item "the request file's words": a string of bytes: the caller's request
  itself, byte for byte. In the programs: the request file, whole: its words of four bytes, the low
  byte first. It is not the value of the item "request", which is `request`.
  Place: 10-proof-file.md 10.2, R14.3; FORMAT.md 12.2. -/
  words   : ByteArray
  /-- The next token that the client was given, as an element of E. It is no item of a statement:
  the prover sends it in the round REPLY, and a verifier compares.
  Place: 10-proof-file.md 10.3, R14.8; FORMAT.md 12.4, R15.7. -/
  reply   : Ext
  deriving DecidableEq, Inhabited

/-- The caller's own values: what a whole call of the programs' verifier is given beside the public
files and the three files. -/
structure UserStm where
  /-- The commitment ID: 32 bytes. The caller names it as 64 digits of base 16.
  Place: FORMAT.md 13.5; 4.1, R4.11. -/
  id      : ByteArray
  /-- The request file's words, of four bytes each: the tokens, then two positions.
  Place: FORMAT.md 12.2. -/
  request : List UInt32
  /-- The token file's one word: the next token that the caller was served.
  Place: FORMAT.md 12.2. -/
  token   : UInt32
  deriving DecidableEq, Inhabited

end Fmt

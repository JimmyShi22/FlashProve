-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Carrier.lean: decodes a parsed file, which this file's names and notes call a
"carrier".
Purpose. A separate, untrusted program (tools/parser/parse_files.py) splits a key file or a proof
file into its parts, adds values that it computes and that are in no file, and writes all as one
flat file (tools/parser/PARSED-FORM.md, section 2). This file decodes those bytes into the structure
`File`. OnBytes/Maker/CarrierTyping.lean then builds the compiled verifier's proof input, without
calling a hash, from a `File` and four things that the caller must supply: the data of the file's
shape, the configuration digest, the binding tree's shape, and the plain parts of three rounds.
States. No theorem: this is code to run. `read` decodes a parsed file, and `readSeeds` the small
seeds file beside it. Each returns the decoded value, or an error message that names the field and
the byte; it names no byte for a wrong magic or for numbers that do not rise, and no field for bytes
left over. The notes give the byte layout and the list of what is refused.
Under. Two inputs to `read`: the expected 8-byte magic, and the bytes. It uses no plan and no hash.
Does not show:
 1. anything about the parsed leaf file (magic FPENTC01): it has no decoder here;
 2. that the parser can be trusted: only the form of its output is checked, as far as the notes'
    list "Refused" says, and nothing else;
 3. anything in the format's other field: only p = 2^64 - 2^32 + 1 is supported;
 4. that the rows are exactly the leaves that a verifier reads: this is not checked;
 5. anything about the seeds: the seeds file is only for comparison, and a verifier derives the
    seeds itself;
 6. the format's whole rule for a salt's length: only its upper bound, 64 bytes, is checked;
 7. the user's own copy of the commitment ID, the request, the reply or the three public files, the
    plan, or the configuration digest: none of them is in a parsed file (the next token that the
    prover sent is, in `rounds1`); a verifier gets them from its user, and never takes the reply
    from a parsed file;
 8. that the content is right: that a path leads to a root, that a run value is its chain's, that
    the rows are the leaves read, that the seeds belong to the table's name;
 9. anything about the file that a parsed file was made from;
10. that `root`, `answers` and `copy` are right: they are the parser's claim, and whoever uses them
    must check them against the user's commitment ID;
11. that these three enter the proof input: building it reads none of them, and `answers` and `copy`
    enter only through the plain parts of three rounds, which the caller makes from them;
12. that `places` and a tree's `chain` are right: they are only there to be compared with the plan's
    and the data's values;
13. that `place` is below `places`, or what `copy` is in a proof file: neither is checked here;
14. anything about soundness.

Notes in full, with every limit at length, are at the end of this file. They are the whole text.
Wherever this summary and the notes differ on a limit or a premise, the stronger limit holds, and
one that only one of the two names holds too; the notes hold for everything else.
Terms: lean/GLOSSARY.md.


-/
import Fmt.Rules1
import Fmt.Rules8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker.Carrier

open _root_.Fmt (Rd rdWord rdElt rdExt rdBytes rdDigest ItemValue Ext)

/-! ## The grammar's readers -/

/-- A reader that says where it refuses. It takes the file's bytes and the byte at which to begin,
and returns the value with the byte behind it, or the refusal's words. -/
abbrev RdE (α : Type) : Type := ByteArray → Nat → Except String (α × Nat)

/-- A reader of Fmt/Rules1.lean as such a reader. n: the number of bytes that it takes. The readers
that are laid in here refuse for two causes alone, and the refusal says which: the bytes end; or, at
F and E, the bytes are there and a word among them is not below p. A reader with a third cause must
not be laid in: its refusal would be told as the second. -/
def plain {α : Type} (n : Nat) (r : Rd α) : RdE α := fun b i =>
  match r b i with
  | some x => .ok x
  | none =>
    if i + n ≤ b.size then
      .error s!" has a word that is not below p, in the {n} bytes from byte {i} on"
    else .error s!" wants {n} bytes from byte {i} on, and the file has {b.size}"

/-- A field: its name goes in front of what was refused inside it. -/
def fld {α : Type} (name : String) (r : RdE α) : RdE α := fun b i =>
  (r b i).mapError fun e => s!".{name}{e}"

/-- u64, as a natural number. -/
def rdNat : RdE Nat := fun b i => (plain 8 rdWord b i).map fun x => (x.1.toNat, x.2)

/-- F: one word below p. -/
def rdF : RdE UInt64 := plain 8 (rdElt .two)

/-- E: three such words. -/
def rdE : RdE Ext := plain 24 (rdExt .two)

/-- digest: 32 bytes. -/
def rdDig : RdE ByteArray := plain 32 rdDigest

/-- n items, one after the other. k: the number of the next item; acc: the items read. -/
def rdLoop {α : Type} (r : RdE α) : Nat → Nat → Array α → RdE (List α)
  | 0, _, acc => fun _ i => .ok (acc.toList, i)
  | n + 1, k, acc => fun b i =>
    match r b i with
    | .ok (x, j) => rdLoop r n (k + 1) (acc.push x) b j
    | .error e => .error s!"[{k}]{e}"

/-- list of T: the count, then the items. Every item of the grammar takes at least one byte, so a
count above the number of bytes that are left is refused at once. A lower count that the bytes do
not hold ends in the refusal of the first item that is missing. Nothing is set aside for the
count. -/
def rdList {α : Type} (r : RdE α) : RdE (List α) := fun b i =>
  match fld "count" rdNat b i with
  | .ok (n, j) =>
    if n > b.size - j then
      .error s!".count is {n}, more than the {b.size - j} bytes that are left, at byte {i}"
    else rdLoop r n 0 #[] b j
  | .error e => .error e

/-- The first member of a list of numbers that is not above the member before it: its number in the
list, its value, the value before it. Nothing: the numbers rise strictly, so none comes twice. k:
the number of the list's first member. -/
def fallFrom : Nat → List Nat → Option (Nat × Nat × Nat)
  | k, a :: b :: l => if a < b then fallFrom (k + 1) (b :: l) else some (k + 1, b, a)
  | _, _ => none

/-! ## The small structs -/

/-- Item: the kind, then the value. The value is an item as the program's reader of a chain holds
it. -/
def rdItem : RdE ItemValue := fun b i => do
  let (kind, j) ← fld "kind" rdNat b i
  match kind with
  | 0 => (fld "root" rdDig b j).map fun x => (.root x.1, x.2)
  | 1 => (fld "f" rdF b j).map fun x => (.f x.1, x.2)
  | 2 => (fld "word" (plain 8 rdWord) b j).map fun x => (.word x.1, x.2)
  | 3 => (fld "e" rdE b j).map fun x => (.e x.1, x.2)
  | 4 => (fld "answer" rdE b j).map fun x => (.answer x.1, x.2)
  | n => .error s!".kind is {n}, not 0 to 4, at byte {i}"

/-- A round: the items of its message, and its nonce. -/
structure Round where
  /-- all items of the message in their order, the roots among them -/
  items : List ItemValue
  /-- 0 where the round has no proof of work -/
  nonce : Nat

/-- Reads a Round. -/
def rdRound : RdE Round := fun b i => do
  let (items, i) ← fld "items" (rdList rdItem) b i
  let (nonce, i) ← fld "nonce" rdNat b i
  pure (⟨items, nonce⟩, i)

/-- An opened leaf. -/
structure Row where
  /-- the position in the tree -/
  leaf : Nat
  /-- the column's words -/
  column : List UInt64
  /-- the file's own salt of the leaf -/
  salt : ByteArray
  /-- the whole path, the leaf's sibling first -/
  path : List ByteArray

/-- bytes, at most 64 of them: a salt. The length is held against 64 before a byte is taken. -/
def rdSalt : RdE ByteArray := fun b i => do
  let (n, j) ← fld "length" rdNat b i
  if n > 64 then throw s!" has {n} bytes, more than 64, at byte {i}"
  plain n (rdBytes n) b j

/-- Reads a Row. -/
def rdRow : RdE Row := fun b i => do
  let (leaf, i) ← fld "leaf" rdNat b i
  let (column, i) ← fld "column" (rdList rdF) b i
  let (salt, i) ← fld "salt" rdSalt b i
  let (path, i) ← fld "path" (rdList rdDig) b i
  pure (⟨leaf, column, salt, path⟩, i)

/-- The opened leaves of one tree. -/
structure TreeRows where
  /-- the tree's number among all roots that the three chains send, from 0 -/
  tree : Nat
  /-- the chain that sent the tree's root: 0 the first, 1 the shared, 2 the second -/
  chain : Nat
  /-- the opened leaves, by rising leaf -/
  rows : List Row

/-- Reads a TreeRows. Refused: a chain above 2; leaves that do not rise strictly. -/
def rdTree : RdE TreeRows := fun b i => do
  let (tree, i) ← fld "tree" rdNat b i
  let (chain, j) ← fld "chain" rdNat b i
  if chain > 2 then throw s!".chain is {chain}, not 0, 1 or 2, at byte {i}"
  let (rows, i) ← fld "rows" (rdList rdRow) b j
  if let some (k, y, x) := fallFrom 0 (rows.map fun r => r.leaf) then
    throw s!".rows[{k}].leaf is {y}, not above the leaf before it, {x}; the tree's number is {tree}"
  pure (⟨tree, chain, rows⟩, i)

/-! ## The carrier -/

/-- A carrier's fields behind the magic, in their order. What each is: the head of this file. -/
structure File where
  root : ByteArray
  answers : List Ext
  run1 : ByteArray
  copy : Nat
  rounds1 : List Round
  run2 : ByteArray
  rounds2 : List Round
  run3 : ByteArray
  rounds3 : List Round
  trees : List TreeRows
  stored : List Row
  bindRoot : ByteArray
  place : Nat
  places : Nat
  slotSalt : ByteArray
  slotPath : List ByteArray

/-- The first 8 bytes of a key file's carrier. -/
def magicKey : String := "FPKEYC01"

/-- The first 8 bytes of a proof file's carrier. -/
def magicProof : String := "FPPRFC01"

/-- Reads the fields of a carrier that begins with `magic`: `magicKey` or `magicProof`. Under any
other string of 8 bytes the fields are read as under the proof file's. -/
def rdFile (magic : String) : RdE File := fun b i => do
  let (m, i) ← fld "magic" (plain 8 (rdBytes 8)) b i
  if m != magic.toUTF8 then
    throw s!".magic is not {magic}: another kind of file, or another version"
  let (root, i) ← fld "root" rdDig b i
  let (answers, i) ← fld "answers" (rdList rdE) b i
  let (run1, i) ← fld "run1" rdDig b i
  let (copy, j) ← fld "copy" rdNat b i
  if magic == magicKey && copy != 0 then
    throw s!".copy is {copy}, not 0 as in every key file's carrier, at byte {i}"
  let (rounds1, i) ← fld "rounds1" (rdList rdRound) b j
  let (run2, i) ← fld "run2" rdDig b i
  let (rounds2, i) ← fld "rounds2" (rdList rdRound) b i
  let (run3, i) ← fld "run3" rdDig b i
  let (rounds3, i) ← fld "rounds3" (rdList rdRound) b i
  let (trees, i) ← fld "trees" (rdList rdTree) b i
  if let some (k, y, x) := fallFrom 0 (trees.map fun t => t.tree) then
    throw s!".trees[{k}].tree is {y}, not above the number before it, {x}"
  let (stored, i) ← fld "stored" (rdList rdRow) b i
  if let some (k, y, x) := fallFrom 0 (stored.map fun r => r.leaf) then
    throw s!".stored[{k}].leaf is {y}, not above the leaf before it, {x}"
  let (bindRoot, i) ← fld "bindRoot" rdDig b i
  let (place, i) ← fld "place" rdNat b i
  let (places, i) ← fld "places" rdNat b i
  let (slotSalt, i) ← fld "slotSalt" rdSalt b i
  let (slotPath, i) ← fld "slotPath" (rdList rdDig) b i
  pure (⟨root, answers, run1, copy, rounds1, run2, rounds2, run3, rounds3, trees, stored, bindRoot,
    place, places, slotSalt, slotPath⟩, i)

/-- Refuses where the reader stopped before the last byte. kind: the first word of every refusal. -/
def whole {α : Type} (kind : String) (b : ByteArray) (x : Except String (α × Nat)) :
    Except String α :=
  match x with
  | .ok (v, i) =>
    if i == b.size then .ok v
    else .error s!"{kind}: {b.size - i} byte(s) left over from byte {i} on"
  | .error e => .error (kind ++ e)

/-- **Reads a whole carrier.** magic: `magicKey` or `magicProof`; it is the first word of every
refusal. No hash call and no plan. What is refused: the head of this file. -/
def read (magic : String) (b : ByteArray) : Except String File :=
  whole magic b (rdFile magic b 0)

/-! ## The file beside: the record's seeds -/

/-- Seed: a point and a factor. -/
def rdSeed : RdE (List Ext × Ext) := fun b i => do
  let (z, i) ← fld "z" (rdList rdE) b i
  let (beta, i) ← fld "beta" rdE b i
  pure ((z, beta), i)

/-- **Reads the small file beside a carrier**: the seeds of the stored table's record, a bare list,
for a comparison with the seeds that a verifier draws itself.
A word that is not below p and a byte left over are refused. -/
def readSeeds (b : ByteArray) : Except String (List (List Ext × Ext)) :=
  whole "seeds" b (rdList rdSeed b 0)

end OnBytes.Maker.Carrier

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Maker/Carrier.lean: the reader of a carrier: a flat file in which a separate program, the
parser, hands over what it has cut out of a key file or a proof file, so that the proof string of
the compiled verifier can be laid of it without a hash call (OnBytes/Maker/CarrierTyping.lean).
Reading a carrier needs no plan. Laying the string takes more, all from the caller: the data of the
file's shape, the configuration's digest, the shape of the binding tree, and the plain parts of
three rounds.

The same thing under other words. The parser is tools/parser/parse_files.py. Its page
tools/parser/PARSED-FORM.md, section 2, describes the same bytes and calls a carrier a "parsed file"
(key.parsed.bin, proof.parsed.bin). That page's one-time chain (key file) and first chain (proof
file) are the first chain here; its anchor (key file) and leaf table (proof file) are the stored
table here; its slot is the place here. The parsed leaf file of its section 3 (magic FPENTC01) has
no reader in this file.

Why. In a key file no part has a word for its own length (OnBytes/Key/File.lean), and in both kinds
of file the reader of an opening takes the opened positions as given (`rdOpening`, Fmt/Rules7.lean):
these are drawn from the hash. So whoever cuts such a file must replay its hash chains. The proof
string that the compiled verifier takes (`OneProtocolProof`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) also holds
values that are in no file: each chain's run's value, whole paths, the binding tree's root. A parser
outside this library does that work and writes its result in the form below. The parser is not
trusted: it can be read as the prover's last step. This file tests the form of what it wrote, as far
as "Refused" below says, and nothing else. Code to be run; no theorem is stated.

Words. A file has three hash chains: the first, the shared, the second. Their numbers are 0, 1, 2;
their fields are run1 and rounds1, run2 and rounds2, run3 and rounds3. The first chain's last round
is called the seal. The binding tree is the hash tree in which the first chain's closing value is
one leaf (OnBytes/Proof/Place.lean). The stored table is the committed table of weights that the
file opens; its record is a list of stored answers with their seeds.

The grammar. A struct is its fields in the declared order, with no names and no padding. `u64`: 8
bytes, the lowest first. `F`: one u64 below p = 2^64 - 2^32 + 1 (`Fld.two`, Fmt/Rules1.lean; the
format's other field is not served). `E`: three of these. `digest`: 32 bytes. `bytes`: a u64 for the
length, then the bytes. `list of T`: a u64 for the count, then the items. No byte follows the last
field.

The fields of a carrier, in their order.
  magic     8 bytes           "FPKEYC01" for a key file, "FPPRFC01" for a proof file
  root      digest            the stored table's root
  answers   list of E         the stored table's stored answers
  run1      digest            the first chain's run's value
  copy      u64               the number of the stored copy; 0 for a key file
  rounds1   list of Round     the first chain's rounds, all, the seal too
  run2      digest            the shared chain's run's value
  rounds2   list of Round     the shared chain's rounds, all
  run3      digest            the second chain's run's value
  rounds3   list of Round     the second chain's rounds, all
  trees     list of TreeRows  one entry for each tree of which a leaf is opened
  stored    list of Row       the stored table's opened leaves
  bindRoot  digest            the binding tree's root
  place     u64               the place of the file's leaf in the binding tree
  places    u64               the number of that tree's leaves
  slotSalt  bytes             the salt of that leaf, at most 64 bytes
  slotPath  list of digest    that leaf's siblings, the leaf's own sibling first
  Round     := items : list of Item, nonce : u64 (0 where the round has no proof of work)
  Item      := kind : u64, then ONE value by the kind:
               0 root: digest, 1 f: F, 2 word: u64, 3 e: E, 4 answer: E
  TreeRows  := tree : u64, chain : u64, rows : list of Row
  Row       := leaf : u64, column : list of F, salt : bytes, path : list of digest
A round's items are all items of its message in their order, the roots among them; a round without
a message has no item. tree: the tree's number among all roots that the three chains send, from 0,
the first chain's roots first, then the shared chain's, then the second's; the stored table is not
counted; a tree that a later chain opens keeps its number. chain: the chain that sent the root: 0
the first, 1 the shared, 2 the second. leaf: the position in that tree. salt: the file's own salt
of the leaf, at most 64 bytes. path: the whole path, as many digests as the tree is deep, the
leaf's sibling first. The trees' numbers rise strictly, and so do the leaves of a tree's rows and of
the stored rows: so none comes twice. A tree that is opened at several rounds, or by several chains,
has one entry with all its opened leaves; a second entry under its number is refused here, and a
look-up would take the first alone. There is a row for just the leaves that the verifier reads: that
the reader does not test.

Beside a carrier there can be a small file with the seeds of the stored table's record: a bare
list of Seed, Seed := z : list of E, beta : E. It is there for a comparison alone: the seeds are a
function of the table's name and the hash, and a verifier draws them itself.

Refused: another magic; a field that the bytes do not hold; a list's count above the number of bytes
that are left; a word that is not below p where the grammar says F or E; an item's kind above 4; a
tree's chain above 2; numbers of trees or leaves that do not rise strictly; a copy other than 0
under the key file's magic; a salt of more than 64 bytes (the upper bound alone of the format's
`Fmt.saltLenOK`); a byte left over. A carrier's refusal begins with the magic that was asked for,
which tells a key file's carrier from a proof file's; a seeds file's begins with "seeds". Then it
names the place: the fields from the outside in, a list's member by its number from 0, then what is
wrong, then the byte. No byte is named at a wrong magic and at numbers that do not rise; no field
at bytes left over. Three examples:
  FPKEYC01.rounds1[0].items[4].kind is 5, not 0 to 4, at byte 232
  FPKEYC01.rounds1[0].items[1].f has a word that is not below p, in the 8 bytes from byte 176 on
  seeds[1].beta wants 24 bytes from byte 96 on, and the file has 119

What is not in a carrier: the user's copy of the commitment ID, of the request, of the reply or of
the three public files; the plan; the configuration's digest. These reach a verifier from its user.
A proof file does state the next token itself: the prover sends it in a round of the first chain,
as the element (y, 0, 0), and it is among rounds1 like every other message. A verifier compares it
with the reply that its user gives and never takes the reply from a carrier.

Main definitions: `File`, `read`, `readSeeds`; the small structs `Round`, `Row`, `TreeRows`.

Not claimed. That what a carrier holds is right: that a path leads to a root, that a run's value is
the chain's, that the rows are the leaves that a verifier reads, that the seeds are those of the
table's name. A carrier that is read says nothing on the file of which it was made. root, answers
and copy are the parser's word on what the user's commitment ID has to pin, and whoever takes them
from here has to hold them against that ID. The laying of the proof string reads none of the three;
answers and copy come into the string only through plain parts that the caller makes of them. The
fields `places` and a tree's `chain` are there for a comparison: whoever lays a proof string takes
the one from the plan and the other from the data, and holds the carrier's against them. It is not
tested here that a place is below the number of places, nor, at a proof file, what copy is. Nothing
on soundness.

Terms: lean/GLOSSARY.md; "carrier" is explained above.
-/

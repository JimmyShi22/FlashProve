-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ChainStm.lean: the statements of the three chains of a key file and of a proof file, as
functions of the declared structure, the parsed file, what the caller brings, and the seals of the
file's earlier chains.

A key file and a proof file have three chains each: the first (a key's one-time chain; a proof's
first chain), the shared chain, the second chain (FORMAT.md R13.2, R14.1). The bytes of a chain's
statement enter the chain's first query, the hash call that gives its first value (R4.6:
`firstBytes`, Fmt/Rules4.lean), behind a word for their length. The spellings that lie under Fmt/
are called and not written again: `TableSt.item`, `sharedStm`, `ProofStm.bytes` (Fmt/Parsed.lean),
`sealItems`, `publishedIDW` (Fmt/Rules4.lean), `bindLeafW`, `vertexBW` (Fmt/Rules7.lean),
`recordSeedsW` (Fmt/RecordSeeds.lean). Definitions alone.
Laws: Fmt/ChainStmLaws.lean, Fmt/ChainStmJoin.lean, Fmt/ChainStmMore.lean, Fmt/ChainStmSmall.lean.
Tests: Fmt/TestChainStm.lean.

Main names:
  THE OPEN FORMS spell a statement from whatever they are handed; their arguments are tied to
  nothing. The laws on bytes are stated on them.
  `keyStmAt`, `proofStmAt`: the statement of each of the three chains (`Which`), from a table or an
    outer statement, two seals and a root.
  `SlotParsed.rootW`, `climbW`: the binding tree's root from a depth, a digest, a seal and a slot.
    They refuse nothing. `SlotParsed.root`: `SlotParsed.rootW` at the format's own hash.
  `KeyStm`, `KeyStm.ok`, `UserStm.keyStm`, `KeyStm.idOkW`: the caller's commitment ID, and the test
    of it against a table under a digest.
  `recordStm`: the statement of the chain of a record's seeds, from a digest and a table.
  `ProofStm.ok`, `sealsOk`, `TableShape.fitsWord`: forms, and a bound on the shape.
  `TableShape.cube`: the number of coordinates of a point of a record's seed. `seedsOk`, `toldOk`:
    the forms of the two lists that the commitment ID's string has beside the answers.
  THE CLOSED FORMS are what a check of a file is to call. Where a form fails, those that give a
  statement answer nothing.
  `ChainDecl.bindShape`: the binding tree's depth and salt's length, READ OUT OF THE HASHED ITEM
    "binding tree" of the first chain's declared parameters. `Declared.proofDepth`: a proof's depth
    by it.
  `KeyParsed.firstStm`, `ProofParsed.firstStm`: a first chain's statement. No hash, no seal.
  `KeyParsed.sharedStmW`, `ProofParsed.sharedStmW` (over `sharedStmOfW`): a shared chain's
    statement, from the first chain's seal. THE BINDING TREE's ROOT IS NO ARGUMENT: it is computed
    from that seal and the file's slot, at the depth and with the salt's length of the hashed item,
    under the digest of the declared public files (`Declared.cfgW`).
  `secondStm`: a second chain's statement, from both seals.
  `KeyParsed.stmAtW`, `ProofParsed.stmAtW`, and at the format's own hash `KeyParsed.stmAt`,
    `ProofParsed.stmAt`: all three of a file.
  `Declared.seedsW`: the elements of a table's record's seeds, drawn from its name.
  `KeyParsed.idOkW`: the test of the caller's ID against the file's own table under the declared
    files' digest, with the seeds drawn and no digest at the end. False where that table has not its
    form or the ID has not 32 bytes. WHERE THE DRAWING OF THE SEEDS REFUSES IT DOES NOT ANSWER
    FALSE: it goes on with no seeds. (That is reached only at an h whose answer under 160 has not 32
    bytes. `sharedStmOfW` does otherwise in the like corner: nothing where the root has not 32
    bytes.)
  `Declared.recordStmW`: `recordStm` under the declared files' digest: closed in the digest alone.
    It asks no form and always answers.
Limits:
  THREE NAMES HERE FIX THE HASH: `SlotParsed.root`, `KeyParsed.stmAt` and `ProofParsed.stmAt` are
  the forms with a W at the format's own hash (`hId`, Fmt/Rules7.lean). They are for the tests
  (Fmt/TestChainStm.lean) and for files that run the chains or tie them to the programs' own reader.
  No other definition here calls them. The laws of Fmt/ChainStmJoin.lean and Fmt/ChainStmMore.lean
  are stated on the forms with a W, at a letter h.
  THE TWO SEALS ARE ARGUMENTS OF THE CLOSED FORMS TOO. By FORMAT.md 18 a verifier computes the two
  seals and the root, "all three", "and takes none of them as an input". Of the three the closed
  forms compute the root. A seal is the digest that a chain's last round draws if that round is SEAL
  (R6.8): a value of the run of all that chain's rounds. The library's function that runs a chain
  under a description is `readChainX` (Fmt/Rules8X.lean), and `Declared.spec` (Fmt/Parsed.lean)
  makes the description from a statement. No function here calls them: these functions give each
  chain's statement to whoever runs the chains one after the other and hands each seal on. That a
  seal which is handed in is the one that the run of that very chain has drawn, and that the chain
  has not refused, is not asked. The digest of zeros, which the programs give as the seal of a
  rejected chain (FORMAT.md 18), is not refused here. `Declared.chainsFormOk` (Fmt/Parsed.lean) asks
  that the last round of a first and of a shared chain is SEAL and that a second chain has no such
  round; none here calls it.
  OF THE DECLARED STRUCTURE the closed forms ask this and no more: of the item "binding tree": two
  words; depth at most 48 (R14.6); a salt's length that R7.3 admits; in a key file depth 0 (R13.5,
  R13.6); of the tables' shape: `TableShape.fitsWord` (those that give a statement;
  `KeyParsed.idOkW` writes no statement's length and does not ask it). They read the public files,
  the field and the shape's six words and ask nothing of them: not `TableShape.ok`, and not that
  each of the six words is below 2 ^ 64 (`TableShape.wordsFit`, Fmt/ChainStmMore.lean): two declared
  shapes whose words agree modulo 2 ^ 64 give one name and one ID's string. `Declared.keyFormOk` and
  `Declared.proofFormOk` (Fmt/Parsed.lean) are not called. The field `ThreeDecl.bind` is not read
  (`KeyParsed.fits` and `ProofParsed.fits`, Fmt/Parsed.lean, hold a slot against that field;
  `Declared.chainsFormOk` holds the field against the item).
  OF A PROOF's OUTER STATEMENT x the form is asked (`ProofStm.ok`) and that the file's head names
  x's stored copy (`ProofParsed.copyFits`). x.table is held against no entry file. x.request is held
  against nothing here: Fmt/RequestItem.lean has the function that says what it must be, and the
  test `ProofStm.requestOkW`. x.words, the request file's own bytes, is held against nothing here
  either: not against a request file, and not against x.request (a test of it: `ProofStm.wordsOk`,
  there).
  THE BOUND ON A STATEMENT's LENGTH that is asked here is 2 ^ 64 bytes, the bound of the spelling (a
  length is one word). The page's bound on a hashed string is lower (R2.3, R2.7: 2 ^ 32 - 144
  bytes). It is not asked here; the library's strict reader of a chain asks it of the statement
  (Fmt/ChainStmSmall.lean). 32 bytes are asked of each seal and of the root, each where it is used;
  `sealsOk` asks the same of the three together and is a premise of laws on the open forms. No
  definition calls it, nor `seedsOk` or `toldOk`.
  `TableSt.ok`, `TableShape.fitsWord` and `SlotParsed.fits` compute 2 ^ logRows and 2 ^ depth; the
  depth is bounded before (48), logRows is not.

-/
import Fmt.Parsed
import Fmt.RecordSeeds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-- What the CHECK of a key file is told from outside the file: the commitment ID that the caller
names. The key's CHAINS are told nothing from outside: the one table in their statements is the
file's own (`KeyParsed.table`), and the ID enters no chain; it is compared with a hash of that
table's name, its record's seeds and its answers (`KeyParsed.idOkW`, over `KeyStm.idOkW`). Place:
FORMAT.md 13.5; 4.1, R4.11. -/
structure KeyStm where
  /-- the commitment ID: 32 bytes -/
  id : ByteArray
  deriving DecidableEq, Inhabited

/-- The form of a key's statement. -/
def KeyStm.ok (x : KeyStm) : Bool := x.id.size == 32

/-- A key's statement from the caller's own values: the ID is told once, by the caller. -/
def UserStm.keyStm (u : UserStm) : KeyStm := ⟨u.id⟩

/-- The three chains of a key file or of a proof file, in the file's order. -/
inductive Which where
  | first | shared | second
  deriving DecidableEq, Repr, Inhabited

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- Goes up from a vertex of a binding tree to its root: x is the vertex's value, p its place in its
level. At each level the lowest bit of p says on which side the sibling stands: at 1 the sibling is
the left child (R14.7). -/
def climbW (cfg : ByteArray) : List ByteArray → ByteArray → Nat → m ByteArray
  | [], x, _ => pure x
  | sib :: rest, x, p => do
    let up ← if p % 2 == 1 then vertexBW h cfg sib x else vertexBW h cfg x sib
    climbW cfg rest up (p / 2)

/-- AN OPEN FORM. The binding tree's root, from a depth, a digest cfg, a seal and a slot (R7.18,
R14.7). The leaf's index is 2 ^ depth + place; at depth 0 with no digest on the path the root is the
leaf itself (R13.6). The climb goes over the digests of the slot's path, however many. Nothing is
refused: not a place from 2 ^ depth on, not a path of another length than depth, not a salt's
length. `sharedStmOfW` asks the slot's form first (`SlotParsed.fits`, Fmt/Parsed.lean). -/
def SlotParsed.rootW (depth : Nat) (cfg seal1 : ByteArray) (s : SlotParsed) : m ByteArray := do
  let leaf ← bindLeafW h depth s.place.toNat cfg seal1 s.salt
  climbW h cfg s.path leaf s.place.toNat

/-- AN OPEN FORM: cfg, t, seeds and told are tied to nothing. A test: is the caller's ID the
commitment ID (R4.11) of the table t under the declared shape and the digest cfg, with these
elements for its record's seeds and these digests at the end? False, without a hash call, where the
caller's ID has not 32 bytes (`KeyStm.ok`). The hash is the library's `publishedIDW`, on the string
`idString D cfg t seeds told` (Fmt/Parsed.lean). No form of t, seeds or told is asked. -/
def KeyStm.idOkW (x : KeyStm) (D : Declared) (cfg : ByteArray) (t : TableSt) (seeds : List Ext)
    (told : List ByteArray) : m Bool :=
  if x.ok then do
    pure (decide ((← publishedIDW h cfg (D.table.name cfg t.root) seeds t.answers told) = x.id))
  else pure false

end

/-- The binding tree's root at the format's own hash: for the tests and for ties to the programs'
own reader. No closed form calls it; the laws at a hash h are on `rootW`. -/
def SlotParsed.root (depth : Nat) (cfg seal1 : ByteArray) (s : SlotParsed) : ByteArray :=
  Id.run (s.rootW hId depth cfg seal1)

/-- AN OPEN FORM: cfg is tied to nothing. The statement of a chain that stands in no file: the chain
from which the seeds of a stored table's record are drawn (R4.8). It is the table's name (R4.10):
root, configuration's digest, six words of the shape. Of the table it reads the root alone. Only the
statement is written here: that chain's label (2 ^ 32), the 32 zero bytes in the place of the
parameters' digest, the empty record field, that it has no random bytes, its one round and how many
seeds are drawn are not (the first value: `recordFirstW`, Fmt/Rules4.lean). The function is defined
at a shape without stored answers too. -/
def recordStm (D : Declared) (cfg : ByteArray) (t : TableSt) : ByteArray := D.table.name cfg t.root

/-- THE OPEN FORM. The statement's bytes of each chain of a KEY file (R13.5, R13.6), spelled from a
table, two seals and a root that are tied to nothing here. A check of a file calls
`KeyParsed.stmAtW`. -/
def keyStmAt (t : TableSt) (seal1 bindRoot seal2 : ByteArray) : Which → ByteArray
  | .first => t.item
  | .shared => sharedStm t bindRoot
  | .second => sealItems [seal1, seal2]

/-- THE OPEN FORM. The statement's bytes of each chain of a PROOF file (R14.3, R14.9, R14.10),
spelled from what the proof's chains are told from outside, two seals and a root that are tied to
nothing here. A check of a file calls `ProofParsed.stmAtW`. -/
def proofStmAt (x : ProofStm) (seal1 bindRoot seal2 : ByteArray) : Which → ByteArray
  | .first => x.bytes
  | .shared => sharedStm x.table bindRoot
  | .second => sealItems [seal1, seal2]

/-- The form of what a proof's chains are told: the table's; the reply canonical; the first chain's
statement has fewer than 2 ^ 64 bytes, since its length is one word in the first query
(`firstBytes`, Fmt/Rules4.lean). For a table with the form, the number in the last clause is the
length of `ProofStm.bytes` (`ProofStm.bytes_size_ok`, Fmt/ChainStmLaws.lean): 183 bytes of names,
length words, the root and the stored copy's word; 24 for each answer; the value of the item
"request" (x.request); and the request file's own bytes (x.words). So the lengths of the four items'
values fit their words too. -/
def ProofStm.ok (D : Declared) (x : ProofStm) : Bool :=
  x.table.ok D.setting.field D.table && D.setting.field.okE x.reply &&
    decide (183 + 24 * D.table.count + x.request.size + x.words.size < 2 ^ 64)

/-- The number c of R4.10: the least integer with 2 ^ c not below the number of entries of a row's
message. A seed of a table's record has a point of c coordinates (R4.8). -/
def TableShape.cube (s : TableShape) : Nat :=
  if s.message ≤ 1 then 0 else Nat.log2 (s.message - 1) + 1

/-- The form of the flat list of a record's seeds under a shape: for each of a row's stored answers
(the shape's word `answers`, not the table's number of answers `TableShape.count`) a point of c
coordinates and a factor; all canonical. -/
def seedsOk (f : Fld) (s : TableShape) (seeds : List Ext) : Bool :=
  seeds.length == s.answers * (s.cube + 1) && seeds.all f.okE

/-- The form of a list of digests: 32 bytes each. -/
def toldOk (told : List ByteArray) : Bool := told.all (·.size == 32)

/-- The form of two seals and a binding root: 32 bytes each. -/
def sealsOk (seal1 bindRoot seal2 : ByteArray) : Bool :=
  seal1.size == 32 && bindRoot.size == 32 && seal2.size == 32

/-- The statement of an entry's link, with two tables of this shape and the form `TableSt.ok`, has
fewer than 2 ^ 64 bytes: 160 bytes of names, length words and roots, and 24 for each answer of each
table (`EntryStm.bytes_size_ok`, Fmt/ChainStmLaws.lean). It is the longest of the statements that
are made of tables, seals and roots alone: the statement of a key's one-time chain has 69 bytes and
24 for each answer, a shared chain's 140 and 24 for each answer. It is a premise of laws, and the
closed forms below ask it. 2 ^ 64 is the bound of the spelling, not the format's (R2.3, R2.7: at
most 2 ^ 32 - 144 bytes of hashed string). Where `Declared.entryFormOk` and `EntryStm.ok` hold it
follows (`Declared.entryFormOk_fitsWord`, Fmt/ChainStmSmall.lean). -/
def TableShape.fitsWord (s : TableShape) : Bool := decide (160 + 48 * s.count < 2 ^ 64)

/-! ## The closed forms -/

/-- The shape of a file's binding tree, READ OUT OF THE FIRST CHAIN's DECLARED PARAMETER ITEM
"binding tree" (R13.5, R14.6): exactly two words, the depth and the number of bytes of a leaf's
salt. The item's bytes are hashed with the first chain's parameters (`Declared.params`,
Fmt/Parsed.lean). Nothing unless the item is there and has 16 bytes, the depth is at most 48
(`depthOK`, R14.6) and the salt's length is one that a leaf can have (`saltLenOK`, R7.3). Of two
items of that name the first is read. The field `ThreeDecl.bind` is not read.
(`ChainDecl.itemWords`, Fmt/Parsed.lean, reads an item's first words and asks neither its length nor
these two ranges.) -/
def ChainDecl.bindShape (c : ChainDecl) : Option BindShape :=
  ((c.others.lookup "binding tree").bind (whole (rdPair rdWord rdWord))).bind fun x =>
    if depthOK x.1.toNat && saltLenOK x.2.toNat then some ⟨x.1.toNat, x.2.toNat⟩ else none

/-- The depth of a proof's binding tree as the hashed item says it; 0 where `ChainDecl.bindShape`
gives nothing (there the closed form of a proof's shared chain answers nothing). -/
def Declared.proofDepth (D : Declared) : Nat := (D.proof.first.bindShape.map (·.depth)).getD 0

/-- The statement of a KEY file's one-time chain (R13.5): the item "table" of the file's own table.
Nothing unless that table has the form and the shape has `TableShape.fitsWord`. No hash, no seal. -/
def KeyParsed.firstStm (D : Declared) (F : KeyParsed) : Option ByteArray :=
  if F.table.ok D.setting.field D.table && D.table.fitsWord then some F.table.item else none

/-- The statement of a PROOF file's first chain (R14.3), of what the chains are told from outside.
Nothing unless x has the form `ProofStm.ok` and the file's head names x's stored copy
(`ProofParsed.copyFits`, R14.2). No hash, no seal. -/
def ProofParsed.firstStm (D : Declared) (x : ProofStm) (F : ProofParsed) : Option ByteArray :=
  if x.ok D && F.copyFits x then some x.bytes else none

/-- The statement of a second chain, of a key or of a proof (R13.5, R14.10): the two seals. Nothing
unless both have 32 bytes. -/
def secondStm (seal1 seal2 : ByteArray) : Option ByteArray :=
  if seal1.size == 32 && seal2.size == 32 then some (sealItems [seal1, seal2]) else none

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- HALF OPEN: b, t and s are whatever the caller hands; the two functions below hand it the hashed
item's shape, the file's or the outer statement's table, and the file's slot. The statement of a
shared chain (R13.5, R13.6, R14.7, R14.9). THE ROOT IS COMPUTED HERE. Asked before any hash: the
table has the form, the tables' shape has `TableShape.fitsWord`, the slot has the form of the shape
b (`SlotParsed.fits`: the place below 2 ^ depth, the salt's length, one digest of 32 bytes a level),
the seal has 32 bytes. Then the configuration's digest is computed from the declared files, and the
root from it, the seal and the slot at b's depth. Nothing too where h gives a root that has not 32
bytes (the format's own hash never does). -/
def sharedStmOfW (D : Declared) (b : BindShape) (t : TableSt) (s : SlotParsed) (seal1 : ByteArray) :
    m (Option ByteArray) :=
  if t.ok D.setting.field D.table && D.table.fitsWord && s.fits b && seal1.size == 32 then do
    let cfg ← D.cfgW h
    let r ← s.rootW h b.depth cfg seal1
    pure (if r.size == 32 then some (sharedStm t r) else none)
  else pure none

/-- The statement of a KEY file's shared chain: `sharedStmOfW` at the shape that the one-time
chain's hashed item "binding tree" gives, the file's own table and the file's slot. Nothing unless
that item gives a shape (`ChainDecl.bindShape`) and its depth is 0 (R13.5; so the slot's word must
be 0: R13.6). -/
def KeyParsed.sharedStmW (D : Declared) (F : KeyParsed) (seal1 : ByteArray) :
    m (Option ByteArray) :=
  match D.key.first.bindShape with
  | some b => if b.depth == 0 then sharedStmOfW h D b F.table F.slot seal1 else pure none
  | none => pure none

/-- The statement of a PROOF file's shared chain: `sharedStmOfW` at the shape that the first chain's
hashed item "binding tree" gives, the outer statement's table and the file's slot. Nothing unless
that item gives a shape (`ChainDecl.bindShape`) and the first chain's statement is something
(`ProofParsed.firstStm`). -/
def ProofParsed.sharedStmW (D : Declared) (x : ProofStm) (F : ProofParsed) (seal1 : ByteArray) :
    m (Option ByteArray) :=
  match D.proof.first.bindShape with
  | some b =>
    if (F.firstStm D x).isSome then sharedStmOfW h D b x.table F.slot seal1 else pure none
  | none => pure none

/-- THE THREE STATEMENTS OF A KEY FILE's CHAINS. seal1, seal2: to be the seals that the runs of the
one-time chain and of the shared chain have drawn. The first statement reads neither, the shared one
the first. The second statement reads neither D nor F: it is something wherever both seals have 32
bytes, also where the two others are nothing. -/
def KeyParsed.stmAtW (D : Declared) (F : KeyParsed) (seal1 seal2 : ByteArray) :
    Which → m (Option ByteArray)
  | .first => pure (F.firstStm D)
  | .shared => F.sharedStmW h D seal1
  | .second => pure (secondStm seal1 seal2)

/-- THE THREE STATEMENTS OF A PROOF FILE's CHAINS. x: what the chains are told from outside. As in
`KeyParsed.stmAtW`, the second statement reads neither D, x nor F. -/
def ProofParsed.stmAtW (D : Declared) (x : ProofStm) (F : ProofParsed) (seal1 seal2 : ByteArray) :
    Which → m (Option ByteArray)
  | .first => pure (F.firstStm D x)
  | .shared => F.sharedStmW h D x seal1
  | .second => pure (secondStm seal1 seal2)

/-- The elements of the seeds of the record of the table t, flat (R4.8, R4.11): drawn from the
statement of the record's chain (`recordStm`: the table's name), as many seeds as a row has stored
answers (the shape's word `answers`), each with a point of `TableShape.cube` coordinates, in the
declared field (the programs draw in the second field alone). cfg is tied to nothing. The format
asks at least one answer (`TableShape.ok`). Where the chain's step refuses: the empty list, which
has not the form `seedsOk`; where it answers, the list has that form
(`Declared.seedsW_ok`, Fmt/ChainStmMore.lean). At a plain hash (values in Id) it refuses exactly
where h's answer to the call for that chain's first value has not 32 bytes (`recordSeedsW_some_iff`,
there). -/
def Declared.seedsW (D : Declared) (cfg : ByteArray) (t : TableSt) : m (List Ext) := do
  let l ← recordSeedsW h D.setting.field (recordStm D cfg t) D.table.cube D.table.answers
  pure (flatSeeds (l.getD []))

/-- THE CLOSED FORM OF THE TEST ON THE COMMITMENT ID (13.5): is the caller's ID the commitment ID of
the key file's own table, under the declared shape and the digest of the declared public files? The
record's seeds are no argument: they are drawn here, from that table's name under that digest
(`Declared.seedsW`). The ID's string is closed with the word 0: by the format an empty list, of
which it defines no element (R4.11); that the library types it as a list of digests is the
library's own choice. False, without a hash call, unless that table has the form `TableSt.ok` and
the caller's ID has 32 bytes. Where the drawing refuses the seeds are the empty list, and the test
goes on with it: it does not answer false. -/
def KeyParsed.idOkW (D : Declared) (F : KeyParsed) (x : KeyStm) : m Bool :=
  if F.table.ok D.setting.field D.table && x.ok then do
    let cfg ← D.cfgW h
    let seeds ← D.seedsW h cfg F.table
    x.idOkW h D cfg F.table seeds []
  else pure false

/-- `recordStm` under the digest of the declared public files. The table is still the caller's. -/
def Declared.recordStmW (D : Declared) (t : TableSt) : m ByteArray := do
  let cfg ← D.cfgW h
  pure (recordStm D cfg t)

end

/-- `KeyParsed.stmAtW` at the format's own hash: for the tests and for files that run the chains.
The laws at a hash h are on the form with a W. -/
def KeyParsed.stmAt (D : Declared) (F : KeyParsed) (seal1 seal2 : ByteArray) (w : Which) :
    Option ByteArray := Id.run (F.stmAtW hId D seal1 seal2 w)

/-- `ProofParsed.stmAtW` at the format's own hash: for the same. -/
def ProofParsed.stmAt (D : Declared) (x : ProofStm) (F : ProofParsed) (seal1 seal2 : ByteArray)
    (w : Which) : Option ByteArray := Id.run (F.stmAtW hId D x seal1 seal2 w)

end Fmt

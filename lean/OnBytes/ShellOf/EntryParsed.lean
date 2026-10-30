-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/EntryParsed.lean: a test program for the entry file behind the parser outside Lean:
it reads the parsed form that tools/parser/ writes for a key file and a leaf file (here: "entry
file"; not the form of `Fmt.EntryParsed`, Fmt/ParsedTypes.lean), makes the value `AskedE` of it, and
hands that to the verifier of EntryProg.lean.

States. Definitions only: `rdLeaf`, `rdKeyHead`, `chainOf` (the readers); `parseP G O` (the whole
reader, with the hash function O as an argument); `entryParsedMainO`, `entryParsedMain`,
`entryParsedCheck` (the program). The theorems are in EntryParsedLaws.lean.
Under. No hypothesis. The whole reader is untrusted, like the parser outside Lean: the theorem on
the exit code holds for every parser.
Does not show.
  1. Soundness: this is a test that serves the runs of lean/Ask/.
  2. That `rdLeaf` refuses a word not below the prime, a salt or column of any length, a row at any
     leaf, two rows of one leaf, two entries for one tree, or an entry without a row: it does not.
  3. Anything of the parsed key file beyond its first two fields.
  4. That the check compares the value's tree shapes with the description: it does not; they are
     filled in here, on the untrusted side (`chainOf` takes them from the description).
  5. Anything by comparing the two files' copies of the first table: nothing relies on that test.
  6. Without hypotheses on lengths, that digest and seeds at `Fmt.oracle` are the format's own.
  7. Which leaf table was read: its number is in the file's name only.
  8. Any theorem about `chainOf`.
  9. Five tests, which this reader does not make: that a word of a round's value or of a column is
     below the prime; the run's value; a salt's length; the width of a stored table's column; rows
     beyond those that are read. What `askedFit` does not ask of these five is tested by nothing.
 10. A difference in the nonce of a round that asks no proof of work: the answer is the same.
 11. As much refusal as `entryMain`: that program's strict reader refuses more.
 12. That no further test is needed: the only argument for that is a bound: it
     bounds an event on the maker's query log and does not combine with the other two files' parts.
 13. The tests that the parsed form's page asks of the verifier: see 9.
 14. Safety against a hostile file: it can end the process by the stack, or cost hours or more; a
     crash is no verdict, and never the exit code 0.
 15. What EntryProg.lean lists as not shown; that any file passes at an O other than `Fmt.oracle`.
 16. Anything of the original key file and leaf file: they are not seen.
 17. That an honest parsed file is read and accepted: a fact of a run; this file records none.
 18. That the value is the one which `convE` makes of the original files: it is not.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ShellOf.EntryProg
import OnBytes.Tie.EntryAtRec

set_option autoImplicit false

namespace OnBytes.ShellOf.EntryParsed

open OnBytes.ShellOf.Claimed
open OnBytes.ShellOf.EntryProg
open OnBytes.Tie (AskedE EntryGround linkAtCfg seedsUnder seedsAt)
open TypedOracleCompiler.Slice (entryXD runEntryFull runEntrySmall cRun oBO)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Fmt (Rd rdWord rdPair rdDigest rdText rdList ItemValue)

/-! ## The fields -/

/-- A reader's value through a function. -/
def rdMap {α β : Type} (f : α → β) (r : Rd α) : Rd β := fun b i => (r b i).map fun x => (f x.1, x.2)

/-- Three words, as they are: no test of canonical form. -/
def rdT3 : Rd (UInt64 × UInt64 × UInt64) := rdPair rdWord (rdPair rdWord rdWord)

/-- An element of the extension field, as it is. -/
def rdE : Rd E := rdMap (fun x => ⟨x.1, x.2.1, x.2.2⟩) rdT3

/-- A word as a number. -/
def rdNat : Rd Nat := rdMap (·.toNat) rdWord

/-- Item := kind, value. Kind 0: a root; 3: an element; 4: an answer. All others: refused. -/
def rdItem : Rd ItemValue := fun b i =>
  match rdWord b i with
  | some (k, j) =>
    if k == 0 then rdMap ItemValue.root rdDigest b j
    else if k == 3 then rdMap ItemValue.e rdT3 b j
    else if k == 4 then rdMap ItemValue.answer rdT3 b j
    else none
  | none => none

/-- Row := leaf, column, salt, path. -/
structure RowP where
  leaf : Nat
  col : List UInt64
  salt : ByteArray
  path : List ByteArray

def rdRow : Rd RowP :=
  rdMap (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩)
    (rdPair rdNat (rdPair (rdList rdWord) (rdPair rdText (rdList rdDigest))))

/-- The ten fields but the magic. A round: its items and its nonce. A tree: its index among the
roots sent and its rows (the field "chain" is read and dropped). -/
structure LeafP where
  root0 : ByteArray
  answers0 : List E
  root : ByteArray
  answers : List E
  run : ByteArray
  rounds : List (List ItemValue × Nat)
  trees : List (Nat × List RowP)
  stored0 : List RowP
  stored1 : List RowP

/-- TreeRows := tree, chain, rows: the second is dropped. -/
def rdTree : Rd (Nat × List RowP) :=
  rdMap (fun x => (x.1, x.2.2)) (rdPair rdNat (rdPair rdNat (rdList rdRow)))

def magicLeaf : ByteArray := "FPENTC01".toUTF8
def magicKey : ByteArray := "FPKEYC01".toUTF8

/-- The parsed leaf file. -/
def rdLeaf (b : ByteArray) : Option LeafP :=
  if b.extract 0 8 == magicLeaf then do
    let (root0, i) ← rdDigest b 8
    let (answers0, i) ← rdList rdE b i
    let (root, i) ← rdDigest b i
    let (answers, i) ← rdList rdE b i
    let (run, i) ← rdDigest b i
    let (rounds, i) ← rdList (rdPair (rdList rdItem) rdNat) b i
    let (trees, i) ← rdList rdTree b i
    let (stored0, i) ← rdList rdRow b i
    let (stored1, i) ← rdList rdRow b i
    if i == b.size then some ⟨root0, answers0, root, answers, run, rounds, trees, stored0, stored1⟩
    else none
  else none

/-- Of the parsed key file: the magic, the first table's root, its answers. -/
def rdKeyHead (b : ByteArray) : Option (ByteArray × List E) :=
  if b.extract 0 8 == magicKey then do
    let (root, i) ← rdDigest b 8
    let (answers, _) ← rdList rdE b i
    some (root, answers)
  else none

/-! ## The made-up chain -/

/-- One opening of a tree of shape sh at all its rows. None: a path that has not as many digests as
the tree is deep. -/
def openingOf (sh : _root_.Fmt.Shape) (rows : List RowP) :
    Option (_root_.Fmt.Shape × List Nat × _root_.Fmt.OpenOut) :=
  if rows.all fun r => r.path.length == sh.a then some (sh, rows.map (·.leaf),
    { cols := rows.map (·.col)
      salts := rows.map (·.salt)
      given := []
      root := ByteArray.empty
      seen := rows.flatMap fun r =>
        r.path.zipIdx.map fun d => (sh.a - d.2, (r.leaf / 2 ^ d.2) ^^^ 1, d.1)
      next := 0 })
  else none

/-- The stored tables' openings of round k, in the description's order. -/
def storedAt (D : XD) (L : LeafP) (k : Nat) :
    Option (List (_root_.Fmt.Shape × List Nat × _root_.Fmt.OpenOut)) :=
  match D.stored[k]? with
  | some ts => ts.mapM fun t => openingOf t.sh (if t.item == 1 then L.stored1 else L.stored0)
  | none => some []

/-- The chain as the typing reads it. None: a tree that the description opens nowhere; a path of
another length than its tree's depth. -/
def chainOf (D : XD) (L : LeafP) : Option _root_.Fmt.ChainOut :=
  (L.trees.mapM fun t =>
    (D.base.ownShapes.lookup t.1).bind fun sh => openingOf sh t.2).bind fun own =>
    (L.rounds.zipIdx.mapM fun r => (storedAt D L r.2).map fun st =>
      ({ msg := ByteArray.empty
         vals := r.1.1
         nonce := r.1.2
         drawn := ⟨[], [], [], none⟩
         list := []
         opens := st ++ (if r.2 == 0 then own else []) } : _root_.Fmt.RoundOut)).map fun rs =>
    { pd := ByteArray.empty
      run := some L.run
      rho0 := ByteArray.empty
      rho := ByteArray.empty
      seen := []
      rounds := rs.toArray }

/-! ## The parser, the kits, the program -/

/-- Untrusted. -/
def parseP (G : EntryGround) (O : ByteArray → ByteArray) : Parser := fun cl key ent =>
  match rdKeyHead key, rdLeaf ent with
  | some K, some L =>
    if K.1 == L.root0 && K.2 == L.answers0 then
      let c := cRun (cfgOf cl.cfg) O
      match chainOf (entryXD G c) L with
      | none => .error "the parsed leaf file has a tree or a path that the description has not"
      | some out =>
        match seedsUnder (seedsAt (oBO O)) (linkAtCfg G.q c) ⟨K.1, K.2⟩,
          seedsUnder (seedsAt (oBO O)) (linkAtCfg G.q c) ⟨L.root, L.answers⟩ with
        | some l0, some l1 => .ok ⟨⟨K.1, K.2⟩, ⟨L.root, L.answers⟩, l0, l1, out⟩
        | _, _ => .error "a table has no seeds"
    else .error "the two parsed files' copies of the first table differ"
  | none, _ => .error "the parsed key file's head does not read"
  | _, none => .error "the parsed leaf file does not read"

def usageP : String :=
  "usage: small|full <commitment ID: 64 hex digits> <config folder> <key.parsed.bin> " ++
    "<leaf-k.parsed.bin>"

/-- The last line of a yes. -/
def wordP : String :=
  "YES: OF THE VALUE THAT LEAN's READER MADE OF THE TWO PARSED FILES GIVEN (of the parsed key " ++
    "file its first two fields alone), under the user's commitment ID and public files: the " ++
    "original key file and leaf file were not seen; no key file's chain, no proof file, no " ++
    "request, no reply was checked"

/-- `kitAt` with another usage line and another last line of a yes. -/
def kitU (z : Params.StdSize) (verify : Claim → AskedE → Bool) (stage : Claim → AskedE → String)
    (gives : Claim → AskedE → List String) (p : Parser) : Kit :=
  { kitAt z verify stage gives p with usage := usageP, word := wordP }

def kitFullP (O : ByteArray → ByteArray) : Kit :=
  kitU Params.stdFull (runAt runEntryFull Tie.recordGround.q.link.table O)
    (stageO Tie.recordGround TypedOracleCompiler.Slice.record_ok O)
    (givesO Tie.recordGround.q.link.table O) (parseP Tie.recordGround O)

def kitSmallP (O : ByteArray → ByteArray) : Kit :=
  kitU Params.stdSmall (runAt runEntrySmall Tie.smallRecordGround.q.link.table O)
    (stageO Tie.smallRecordGround TypedOracleCompiler.Slice.small_record_ok O)
    (givesO Tie.smallRecordGround.q.link.table O) (parseP Tie.smallRecordGround O)

/-- THE PROGRAM, with the hash function on bytes an argument. -/
def entryParsedMainO (O : ByteArray → ByteArray) : List String → IO UInt32
  | "full" :: r => mainOf (bodyOf (kitFullP O)) r
  | "small" :: r => mainOf (bodyOf (kitSmallP O)) r
  | _ => mainOf (bodyOf (kitSmallP O)) []

/-- THE PROGRAM: at the format's oracle on bytes, made of Lean's BLAKE2b. -/
def entryParsedMain : List String → IO UInt32 := entryParsedMainO _root_.Fmt.oracle

/-- The program, then: the code 0 returns; every other code is thrown, as words. -/
def entryParsedCheck (args : List String) : IO Unit :=
  entryParsedMain args >>= fun c =>
    if c = 0 then pure ()
    else throw (IO.userError ("NOT A YES: the program's exit code is " ++ toString c))

end OnBytes.ShellOf.EntryParsed

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/ShellOf/EntryParsed.lean: THE PROGRAM FOR THE ENTRY FILE's PART BEHIND THE PARSER OUTSIDE
LEAN: a reader of the parsed form that tools/parser/ writes for a leaf file (ten fields, magic
`FPENTC01`: tools/parser/PARSED-FORM.md, sections 1 and 3), to the plain value `AskedE`; then the
verifier of OnBytes/ShellOf/EntryProg.lean. That page's "leaf file" is this library's "entry file".
Definitions alone; the laws are in OnBytes/ShellOf/EntryParsedLaws.lean. The form read here is not
the one of `Fmt.EntryParsed` (Fmt/ParsedTypes.lean), which keeps the openings by round with their
given digests.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

  The call: small|full <commitment ID: 64 hex digits> <config folder> <key.parsed.bin>
    <leaf-k.parsed.bin>
  `rdLeaf`: the ten fields, one after the other, by the format's own readers of words, digests, byte
    strings and lists (Fmt/Rules1.lean). Refused: another magic; a file that ends early; an item's
    kind other than 0, 3, 4; a byte left over. Not refused: a word that is not below the field's
    prime; a salt or a column of whatever length; rows at whatever leaves; two rows of one leaf; two
    entries with one tree's index; an entry without a row.
  `rdKeyHead`: of `key.parsed.bin` the magic `FPKEYC01` and fields 1 and 2 (the first table's root
    and answers) and no more: the rest of that file is not looked at.
  `chainOf D L`: a `Fmt.ChainOut` MADE UP of the fields, so that the typing of the check
    (`assembleS`, OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean) finds in it what it reads: the run's value;
    each round's values and nonce; one opening for each tree, with the shape that the description D
    has for it, its rows' leaves, columns and salts, and as "vertices met" the rows' whole paths
    (entry k of a path: depth a - k, place (leaf / 2 ^ k) xor 1). The shapes are laid HERE, ON THE
    UNTRUSTED SIDE: the check does not hold them against D. Refused: a tree that D opens nowhere; a
    row that is laid and whose path has not as many digests as its tree is deep (a stored table's
    rows are laid where the file has the round in which D opens that table). Where two rows name one
    vertex, the first is the one that every look-up finds. The two stored tables' openings are laid
    at the round and number at which D has them; the chain's own trees' behind these in round 0. All
    other fields are empty.
  `parseP G O`: the parser of the kit, the hash function on bytes an argument. The first table is
    taken out of `key.parsed.bin`; refused where the leaf file's copy (root0, answers0) differs: a
    matter of honesty: nothing leans on it. The public files' digest (`cRun`) and the seeds of both
    tables (`seedsAt`, OnBytes/Tie/EntryAtRec.lean, at `oBO O`) are made here THROUGH O: no fixed
    hash stands in this reader; no seeds file is read. At `Fmt.oracle` they are the format's own
    digest and seeds, as the library's converter makes them (`convE`,
    OnBytes/TypedOracleCompiler/Slice/EntryConv.lean): `cRun_oracle`, `seedsUnder_oracle`
    (OnBytes/ShellOf/EntryParsedLaws.lean), under premises on lengths. The number k of the leaf
    table stands in the file's name alone: the program does not know it.
  `entryParsedMainO O`, `entryParsedMain`, `entryParsedCheck`: as `entryMainO`, `entryMain`,
    `entryCheck`.

ALL OF THIS READER IS ON THE UNTRUSTED SIDE, like the parser outside Lean whose file it reads: to
the theorem on the exit code, which holds for every parser, it owes completeness alone.
`parseP_tables` (OnBytes/ShellOf/EntryJoinLaws.lean) says which bytes became the value's two tables;
`furtherIs_joins`, which joins the leaf file's table to a proof file's, leans on it. No law speaks
of `chainOf`. The claim (the ID, the three public files) comes from the user and does not pass
through it.

Who tests what it hands over. THIS READER TESTS NONE OF THESE FIVE: that a word of a round's value
or of a column is below the field's prime; the run's value (the ten fields do not hold the chain's
32 random bytes, so it cannot be computed from them); a salt's length; a stored table's column's
width; rows beyond those that are read. On the trusted side stand: the tests on the value
(`askedFit`, OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean: its text says which); the ID's comparison (the
first table); the comparison of the seeds inside the check; the paths' lengths (the lax verifier);
the own columns' widths (the typing). WHAT OF THE FIVE `askedFit` DOES NOT ASK IS TESTED BY NOTHING.
The nonce of a round at which the description asks no work is dropped by the typing: a file that
differs there alone gets the same answer. THE VERIFIER IS THE SAME AS `entryMain`'s, BUT THE PROGRAM
REFUSES LESS: there the wired parser, trusted for nothing, is the port's strict reader, which leaves
no room for the first four: it refuses such words, computes the run's value itself, and cuts salts
and columns by the plan. Whether a test is owed: the one ground for "none" is a bound that takes
every value a (OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean; see its limits: it
bounds an event on the maker's log and does not chain with the other two files' parts). The parsed
form's page asks the verifier for these tests.

What a hostile file can cost. The functions are total, and a count is held against the bytes that
are left before a list is laid. But the format's reader of a list takes one stack frame a value, and
a file may have up to 2 ^ 28 bytes: a hostile file can end the process by the stack. And time: the
rows of a tree are as many as the file likes, and the check's typing looks up every vertex of every
row, read or not, in one list of all that tree's vertices: the time grows with the square of the
rows: at 2 ^ 28 bytes, hours or more. The program has no clock. A crash is no verdict, and never the
exit code 0.

What is not claimed: all that the head of OnBytes/ShellOf/EntryProg.lean does not claim (its
sentence on the wired parser and the fixed hash speaks of `parseE`; here: that at an O other than
`Fmt.oracle` any file is accepted: no law, no run). Anything of the original key file and leaf file:
they are not seen. That a file which tools/parser/ makes of honest files is read and accepted: a
fact of a run: this file records none. That the value made here is the one that `convE` makes of the
original files: it is not, field by field (the made-up chain leaves empty what the check does not
read, and lays the openings elsewhere).
-/

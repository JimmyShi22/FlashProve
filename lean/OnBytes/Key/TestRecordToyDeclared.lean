-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/TestRecordToyDeclared.lean: the declared structure (Decl/Declared.lean, Fmt/Parsed.lean)
and the parsed record of a key file, at the toy key file that the programs wrote
(OnBytes/Entry/RecordToyFiles.lean).

The three chains are declared off the descriptions under which Key.check reads the file. These are
made as Key.readKey (OnBytes/Key/File.lean) and Proof.readTail (OnBytes/Proof/Tail.lean, whose head
explains block, dry run and description; the strict reader: OnBytes/Iop/Ground.lean) make them,
spelled again here, since no function of the library returns them. A tree that the second chain
takes over is named by the chain that has sent its root and by its place among that chain's roots.
Of the parsed record the three chains' rounds are what the strict reader has returned; head, table,
random bytes and slot are cut out of the file.

1. The declared chains spell the programs' parameter bytes of all three chains, byte for byte.
2. Declared.keyFormOk says yes at this structure.
3. Declared.spec gives the three descriptions back, in every field but the plan; so do TableSt.item
   and sharedStm the statements of the first two chains. The one-time chain's statement, spelled by
   hand from the key file's bytes, has the size and the checksum of the programs' own file.
4. The trees that the second chain takes over stand in one round, its first with an opening. By
   increasing place they are the one-time chain's first tree (the index-mask message) and last
   (W) and the shared chain's second (Omega).
5. Written back: the parsed record, written by KeyParsed.bytes, is the key file, byte for byte.
6. KeyParsed.fits says yes at the parsed record.
7. Parsed records with one kind of thing changed do not fit: 31 changes. Four of them are written
   back to the key file's very bytes: elements and answers in each other's places, either of the
   two alone, and a further round without a byte. So 5 alone would not see them.
8. The structure with one kind of thing changed is refused by Declared.keyFormOk: eight changes. And
   the parsed record does not fit a structure whose tables have twice the rows.

Where the expected values come from. The bytes are the programs'. The yes of 2 and of 6: the file is
an honest key file of the programs, and R13.2, R13.4 to R13.7, R13.15, R13.18 and R13.19 describe
the form of such a file and of its chains. 4: the table of a key file's trees in
docs/format/09-key-and-leaf-files.md, 9.7, with R13.7 and R8.7. A no follows from the rule that the
change's name cites. The size and the checksum in 3 come from outside Lean: ls and b2sum over
key.one-time.statement, a file that the run which wrote the key file's parameter bytes wrote beside
them (sha256 7d11cf1b5739edb77ba76a3933e962f15fc21086cfef4b3f611f33d995fec18d). The checksum is
BLAKE2b, taken as in OnBytes/Entry/TestRecordToySums.lean.

Typed by hand, as in OnBytes/Entry/TestRecordToyDeclared.lean: the setting, the tables' shape, the
binding tree's shape, which chain has the flag of the entry RECORD, the three cases of the random
bytes, and in the parsed record the lengths 8, 32, 8 and 40 at which head, random bytes and slot are
cut, and the slot's empty path. Test 1 holds the setting and the flags against the programs' bytes,
test 2 the two shapes, test 3 the cases of the random bytes.

Every test is checked when the file compiles. The program verify-on-bytes does not import this file.

Not claimed. No theorem. One honest file.
Test 1 is in part a circle. The further items were read off the very bytes with which it compares,
and so were the plans under which the dry runs give the rounds' entries. It can fail on the setting,
on the digest of the two public files, and on the entry RECORD: its numbers, its place, and that the
two later plans have none.
Test 3 is in part a circle too. The statement is an argument that Declared.spec lays back; label,
first tree, stored trees, entries, the opened trees' shapes and roots were copied out of the
descriptions; the parameter bytes are test 1's. It can fail on the digest, on the case of the random
bytes and the value of the statement's item 1, on kindOf against the port's kinds, on Entry.cut
against the port's items, and on the start of each tree that is taken over. TableSt.item and the
port's statement are two wrappers of one function, Fmt.tableItem.
Test 5 says little of the declared structure: a writer reads of it the nonce's and a listed
position's bytes. 344 of the 503,744 bytes are cut out of the file and laid back; for them the test
holds the order of the file's parts. A fault that ChainParsed.of and the writers share is not seen.
Test 6 holds in part by the making: the strict reader has cut columns, digests and elements under
the shapes from which the chains are declared. It can fail on the head, on the number of answers, on
the salts' lengths, and on Entry.cut, the cut of every message into items, against the items under
which the port has read the file.
Not entered at this file: listed positions (the plan lists none); a slot's path (the depth is 0); a
nonce too wide for its bytes (it has eight); elements of F or plain words in a message. The tables'
salt and the setting's are both 40, so which of the two a function takes is not seen. Listed
positions, a slot's path, a nonce too wide and the two salts are tried at made-up values in
Fmt/TestKeyProofForm.lean.
At some changes a second clause refuses too, and a test here does not show which clause has refused.
Nothing on soundness, completeness or hiding.
-/
import OnBytes.Key.TestRecordToy
import Fmt.Parsed
import Fmt.ParamsRead
import Fmt.Blake2b

namespace OnBytes.Key.RecordToyDeclared
open Fmt
open OnBytes.Entry.RecordToy (chains keyFile oneTimeParameters sharedParameters secondParameters
  publicFileOne publicFileTwo)

/-- The key file as read, with the three chains' descriptions. -/
structure KeyRead where
  /-- the first table -/
  table : Params.TableName
  /-- the place of the first byte of the one-time chain -/
  start : Nat
  /-- the three chains and the slot in the binding tree, as read -/
  read : Proof.TailRead
  /-- the description of the one-time chain -/
  first : SpecX
  /-- of the shared chain -/
  shared : SpecX
  /-- of the second chain -/
  second : SpecX

/-- Reads the toy key file. -/
def keyRead : Option KeyRead := do
  let k ← chains
  let p := k.oneTime
  let (table, j) ← (Key.readTable p.lin.fold.index p.given.cfg keyFile).toOption
  let r ← (Key.readKey k table keyFile j).fromStart.toOption
  let q := Key.tailPublic k table
  let (rounds1, dry) ← (Key.oneTime p).dryRun (Key.startOf p)
  let spec1 ← p.describe table rounds1
  let seal1 ← r.first.seal
  let (rounds2, end2) ← (Proof.sharedBlock q.lin r.key).dryRun (Proof.sharedStart q)
  let spec2 ← q.shared.describe q.lab₂ q.table r.place.root rounds2
  let seal2 ← r.shared.seal
  let rounds3 ← (Proof.secondBlock q.lin dry.lin (end2.goesOn r.shared)).rounds
    (Proof.secondStart q dry r.first)
  let spec3 ← q.second.describe q.lab₃ seal1 seal2 rounds3 (Proof.secondFirstTree r.first)
  pure ⟨table, j, r, spec1, spec2, spec3⟩

/-- A tree's source, declared. earlier: the roots that each earlier chain of the file has sent. A
root that none of them has sent gets a source that ChainDecl.takenOk refuses. -/
def takenFrom (earlier : List (List ByteArray)) : Src → TreeSource
  | .own n => .own n
  | .given root _ =>
    match (earlier.zipIdx.filterMap fun e => (e.1.idxOf? root).map fun p => (e.2, p)).head? with
    | some x => .taken x.1 x.2
    | none => .taken earlier.length 0

/-- A chain, declared off its description S and its parameter bytes b. -/
def chainOf (S : SpecX) (b : ByteArray) (flag : Bool) (rand : RandAt)
    (earlier : List (List ByteArray)) : ChainDecl :=
  { label := S.base.label
    record := flag
    others := ((paramsRead b).map (·.others)).getD []
    rand := rand
    firstTree := S.base.firstTree
    rounds := (S.base.rounds.zip S.stored).map fun y =>
      ⟨y.1.entry, y.2, y.1.opens.map fun o => (o.1, takenFrom earlier o.2)⟩ }

/-- The toy's declared structure, with the key's three chains. -/
def keyDeclared : Option Declared := keyRead.map fun s =>
  { files := [publicFileOne, publicFileTwo]
    setting := ⟨.two, 40, 8, 0, 1, 1⟩
    table := ⟨14, 803, 1001, 3, 1, 40⟩
    key :=
      { first := chainOf s.first oneTimeParameters true .inFile []
        bind := ⟨0, 40⟩
        shared := chainOf s.shared sharedParameters false (.item 1) []
        second := chainOf s.second secondParameters false .inFile
          [s.read.first.roots, s.read.shared.roots] } }

/-- The first table as the declared structure's functions take it. -/
def tableOf (s : KeyRead) : TableSt :=
  ⟨s.table.root, s.table.answers.map fun e => (e.c0, e.c1, e.c2)⟩

/-- The parsed record of the key file: the head; the table; each chain's rounds as the strict reader
has returned them, with its 32 random bytes where they stand in the file; the slot, cut at its
lengths: a word and a salt of 40 bytes. -/
def parsed : Option KeyParsed := do
  let s ← keyRead
  let D ← keyDeclared
  let r := s.read
  let first ← ChainParsed.of (D.plan D.key.first) (some (keyFile.extract s.start (s.start + 32)))
    r.first.out
  let shared ← ChainParsed.of (D.plan D.key.shared) none r.shared.out
  let second ← ChainParsed.of (D.plan D.key.second)
    (some (keyFile.extract r.shared.next (r.shared.next + 32))) r.second.out
  let word ← rdWord keyFile r.first.next
  pure ⟨keyFile.extract 0 8, tableOf s, first,
    ⟨word.1, keyFile.extract (r.first.next + 8) (r.first.next + 48), []⟩, shared, second⟩

/-- Two descriptions agree in every field but the plan, whose bytes are among the parameter
bytes. -/
def sameSpec (X S : SpecX) : Bool :=
  X.base.label == S.base.label && X.base.params == S.base.params &&
    X.base.statement == S.base.statement && X.base.firstTree == S.base.firstTree &&
    X.base.cfg == S.base.cfg && X.base.rounds == S.base.rounds && X.stored == S.stored &&
    (match X.base.rand, S.base.rand with
      | .inFile, .inFile => true
      | .given a, .given b => a == b
      | .none, .none => true
      | _, _ => false)

/-- The descriptions that Declared.spec makes of the three declared chains, each held against the
description under which the file was read. -/
def specsBack : Option (Bool × Bool × Bool) := do
  let s ← keyRead
  let D ← keyDeclared
  let run1 ← s.read.first.out.run
  let run2 ← s.read.shared.out.run
  let a ← D.spec D.key.first D.cfg s.first.base.statement
  let b ← D.spec D.key.shared D.cfg s.shared.base.statement
  let c ← D.spec D.key.second D.cfg s.second.base.statement
    [(s.read.first.roots, run1), (s.read.shared.roots, run2)]
  pure (sameSpec a s.first, sameSpec b s.shared, sameSpec c s.second)

/-- The one-time chain's statement, spelled by hand from the key file's bytes (R13.5, R4.1, R4.6):
the name "table" as a text; the value's length, 240; the root as a string of 32 bytes; the list of
the eight answers, 24 bytes each. -/
def statementByHand : ByteArray :=
  u64n 5 ++ "table".toUTF8 ++ u64n 240 ++ u64n 32 ++ keyFile.extract 8 40 ++ u64n 8 ++
    keyFile.extract 40 232

/-- The trees that a round takes over: chain and place. -/
def takenIn (r : DeclaredRound) : List (Nat × Nat) :=
  r.opens.filterMap fun o =>
    match o.2 with
    | .taken k p => some (k, p)
    | .own _ => none

/-- The rounds of the one-time chain's record changed, each by g. -/
def atFirst (g : RoundParsed → RoundParsed) (F : KeyParsed) : KeyParsed :=
  { F with first := { F.first with rounds := F.first.rounds.map g } }

/-- An answer in the place of an element, and the other way round: the same bytes. -/
def swapKind : ItemValue → ItemValue
  | .e x => .answer x
  | .answer x => .e x
  | g => g

/-- A word that spells no element of either field of the format. -/
def big : UInt64 := 18446744073709551615

/-- Every opening of a chain's record changed. -/
def atOpens (g : OpenParsed → OpenParsed) (c : ChainParsed) : ChainParsed :=
  { c with rounds := c.rounds.map fun r => { r with opens := r.opens.map g } }

/-- The parsed record with one kind of thing changed, wherever it occurs in the named part: none of
these fits. The first four are written back to the key file's bytes. -/
def changedParsed : List (String × (KeyParsed → KeyParsed)) := [
  ("R8.8: answers and elements in each other's places",
    atFirst fun r => { r with vals := r.vals.map swapKind }),
  ("R8.1: a further round without a byte", fun F =>
    { F with first := { F.first with rounds := F.first.rounds ++ [⟨[], none, [], []⟩] } }),
  ("R8.8: elements where answers are sent", atFirst fun r => { r with vals := r.vals.map fun
    | .answer x => .e x
    | g => g }),
  ("R8.8: answers where elements are sent", atFirst fun r => { r with vals := r.vals.map fun
    | .e x => .answer x
    | g => g }),
  ("R13.1: an entry file's head", fun F => { F with head := headOf tagEntry .two }),
  ("R13.2: a root of 31 bytes", fun F => { F with table := { F.table with
    root := F.table.root.extract 0 31 } }),
  ("R13.2: an answer less", fun F => { F with table := { F.table with
    answers := F.table.answers.drop 1 } }),
  ("R1.4: answers that are not canonical", fun F => { F with table := { F.table with
    answers := F.table.answers.map fun _ => (big, 0, 0) } }),
  ("R4.5: random bytes of 33", fun F => { F with first := { F.first with
    rand := some (zeroBytes 33) } }),
  ("R4.5: the shared chain with random bytes in the file",
    fun F => { F with shared := { F.shared with rand := some zero32 } }),
  ("R4.5: the second chain without its random bytes",
    fun F => { F with second := { F.second with rand := none } }),
  ("R8.1: a round less in the shared chain",
    fun F => { F with shared := { F.shared with rounds := F.shared.rounds.dropLast } }),
  ("R8.8: an element more in every message of the one-time chain",
    atFirst fun r => { r with vals := r.vals ++ [.e (1, 2, 3)] }),
  ("R8.8: the last item of every message of the one-time chain is missing",
    atFirst fun r => { r with vals := r.vals.dropLast }),
  ("R1.5: roots of 31 bytes in the messages", atFirst fun r => { r with vals := r.vals.map fun
    | .root d => .root (d.extract 0 31)
    | g => g }),
  ("R1.4: answers of the messages that are not canonical",
    atFirst fun r => { r with vals := r.vals.map fun
      | .answer _ => .answer (big, 0, 0)
      | g => g }),
  ("R12.9: elements where roots are sent", atFirst fun r => { r with vals := r.vals.map fun
    | .root _ => .e (1, 2, 3)
    | g => g }),
  ("R1.4: elements of the messages that are not canonical",
    atFirst fun r => { r with vals := r.vals.map fun
      | .e _ => .e (big, 0, 0)
      | g => g }),
  ("R8.2: no nonce in the one-time chain", atFirst fun r => { r with nonce := none }),
  ("R8.2: a nonce in every round of the one-time chain",
    atFirst fun r => { r with nonce := some 0 }),
  ("R8.2: a listed position in every round of the one-time chain",
    atFirst fun r => { r with listed := [1] }),
  ("R13.6: the slot 1", fun F => { F with slot := { F.slot with place := 1 } }),
  ("R13.2: a slot's salt that is longer by a byte",
    fun F => { F with slot := { F.slot with salt := F.slot.salt.push 0 } }),
  ("R13.6: a digest on the slot's path",
    fun F => { F with slot := { F.slot with path := [zero32] } }),
  ("R8.7: the first opening of every round of the second chain is missing",
    fun F => { F with second := { F.second with rounds := F.second.rounds.map fun r =>
      { r with opens := r.opens.drop 1 } } }),
  ("R7.8: openings without a column in the second chain",
    fun F => { F with second := atOpens (fun o => { o with cols := [] }) F.second }),
  ("R6.6: every column of the shared chain's openings twice",
    fun F => { F with shared := atOpens (fun o => { o with cols := o.cols ++ o.cols }) F.shared }),
  ("R1.3: elements of the second chain's columns that are not canonical",
    fun F => { F with second := atOpens (fun o =>
      { o with cols := o.cols.map fun c => (c.1.map fun _ => big, c.2) }) F.second }),
  ("R7.8: columns of the shared chain that are short by an element",
    fun F => { F with shared := atOpens (fun o =>
      { o with cols := o.cols.map fun c => (c.1.dropLast, c.2) }) F.shared }),
  ("R7.3: salts of the second chain's leaves that are longer by eight bytes",
    fun F => { F with second := atOpens (fun o =>
      { o with cols := o.cols.map fun c => (c.1, c.2 ++ zeroBytes 8) }) F.second }),
  ("R7.8: given digests of 31 bytes in the one-time chain",
    fun F => { F with first := atOpens (fun o =>
      { o with given := o.given.map fun d => d.extract 0 31 }) F.first }) ]

/-- A round in which every tree that is taken over has the next number in its shape. -/
def nextNumbers (r : DeclaredRound) : DeclaredRound :=
  { r with opens := r.opens.map fun o =>
      match o.2 with
      | .taken _ _ => ({ o.1 with tree := o.1.tree + 1 }, o.2)
      | .own _ => o }

/-- A round whose stored trees have columns of half the width. -/
def halfWidth (r : DeclaredRound) : DeclaredRound :=
  { r with stored := r.stored.map fun t => { t with sh := { t.sh with W := t.sh.W / 2 } } }

/-- The structure with one kind of thing changed: none of these passes. -/
def changedStructure : List (String × (Declared → Declared)) := [
  ("R13.4: the shared chain under the second chain's label", fun D =>
    { D with key := { D.key with shared := { D.key.shared with label := D.key.second.label } } }),
  ("R13.15: the one-time chain without the flag of the entry RECORD", fun D =>
    { D with key := { D.key with first := { D.key.first with record := false } } }),
  ("R13.7: the second chain's first tree is one more", fun D =>
    { D with key := { D.key with second := { D.key.second with
      firstTree := D.key.second.firstTree + 1 } } }),
  ("R13.13: the shape has a row's message of one entry more", fun D =>
    { D with table := { D.table with message := D.table.message + 1 } }),
  ("R13.19: the stored table's columns have half the width that the shape gives", fun D =>
    { D with key := { D.key with shared := { D.key.shared with
      rounds := D.key.shared.rounds.map halfWidth } } }),
  ("R13.5: the binding tree has salts of 48 bytes", fun D =>
    { D with key := { D.key with bind := ⟨0, 48⟩ } }),
  ("R13.6: the one-time chain without its last round", fun D =>
    { D with key := { D.key with first := { D.key.first with
      rounds := D.key.first.rounds.dropLast } } }),
  ("R7.13: the trees that the second chain takes over, each under the next number", fun D =>
    { D with key := { D.key with second := { D.key.second with
      rounds := D.key.second.rounds.map nextNumbers } } }) ]

/-- The names of the members that a test admits. -/
def admitted {α : Type} (test : α → Bool) (l : List (String × α)) : List String :=
  (l.filter fun x => test x.2).map (·.1)

-- 1. the declared chains spell the programs' parameter bytes
#guard (keyDeclared.map fun D =>
  (D.params D.key.first D.cfg == oneTimeParameters, D.params D.key.shared D.cfg == sharedParameters,
    D.params D.key.second D.cfg == secondParameters)) == some (true, true, true)
-- 2. the structure passes
#guard (keyDeclared.map (·.keyFormOk)) == some true
-- 3. the descriptions and the first two statements come back
#guard specsBack == some (true, true, true)
#guard (keyRead.map fun s => ((tableOf s).item == s.first.base.statement,
  sharedStm (tableOf s) s.read.place.root == s.shared.base.statement)) == some (true, true)
#guard (keyRead.map fun s => s.first.base.statement == statementByHand) == some true
#guard statementByHand.size == 261 &&
  hex (blake2b 64 ByteArray.empty ByteArray.empty statementByHand) ==
    "d2a88f431ddbceaa0c6b7b6bd18859cff862b2cba8853dd1a5a5b11929e2b7d0" ++
    "5cec2959d8446561953d18609c47ff689c327599d05be9f51340f43d03d82385"
-- 4. one round of the second chain takes trees over: its first with an opening
#guard (keyDeclared.map fun D =>
  ((D.key.second.rounds.filter fun r => !r.opens.isEmpty).map takenIn).filter (!·.isEmpty) ==
      [[(0, 0), (0, D.key.first.roots - 1), (1, 1)]] &&
    ((D.key.second.rounds.filter fun r => !r.opens.isEmpty).head?.map takenIn).any (!·.isEmpty) &&
    decide (2 ≤ D.key.first.roots)) == some true
-- 5. written back
#guard (keyDeclared.bind fun D => parsed.map fun F => F.bytes D == keyFile) == some true
-- 6. the parsed record fits
#guard (keyDeclared.bind fun D => parsed.map fun F => F.fits D) == some true
-- 7. parsed records that do not fit; the first four have the key file's bytes
#guard changedParsed.length == 31 && (keyDeclared.bind fun D => parsed.map fun F =>
  admitted (fun g => (g F).fits D) changedParsed) == some []
#guard (keyDeclared.bind fun D => parsed.map fun F =>
  (changedParsed.take 4).map fun g => (g.2 F != F, (g.2 F).bytes D == keyFile)) ==
  some (List.replicate 4 (true, true))
-- 8. structures that do not pass; the parsed record does not fit tables of twice the rows
#guard changedStructure.length == 8 && (keyDeclared.map fun D =>
  admitted (fun g => (g D).keyFormOk) changedStructure) == some []
#guard (keyDeclared.bind fun D => parsed.map fun F =>
  F.fits { D with table := { D.table with logRows := D.table.logRows + 1 } }) == some false

end OnBytes.Key.RecordToyDeclared

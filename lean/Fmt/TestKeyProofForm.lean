-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/TestKeyProofForm.lean: tests of the declared structure (Decl/Declared.lean, Fmt/Parsed.lean) as
far as a key file and a proof file go, at made-up chains and made-up parsed records.

1. The head. The first eight bytes that headOf writes are the kind, CPIK for a key file, CPEN for an
   entry file (R13.1) and CPPF for a proof file (R14.2), and the version, H821 in the second field
   and H811 in the first (R13.1).
2. Declared.keyFormOk. Made-up chains of a key file pass. With one thing changed they are refused:
   54 changes of the chains, seven of the setting or the tables' shape. A change's name says what is
   changed and, where a rule of the format says it, the rule.
3. The labels. A proof's shared or second chain under a key's label, the two in each other's places,
   and a key's under a proof's: five refused.
4. Declared.proofFormOk. Made-up chains of a proof file pass, also with a further item at the end
   (R14.3) and with a binding tree of depth 48 (R14.6). Eight changes are refused, among them items
   "the test on the table" that differ in one word between the first and the shared chain (R14.9).
5. Declared.shapeOf: a tree's shape by file, chain and number, at trees of four shapes.
6. The writers, against bytes whose words are spelled by hand: a round, a slot, and a key file's and
   a proof file's parts in the files' order (R13.2; R14.1, R14.2), each chain under a plan of its
   own.
7. KeyParsed.fits and ProofParsed.fits. A made-up parsed record fits the made-up chains; with one
   thing changed it does not: 34 changes of a key file's, five of a proof file's. And
   RoundParsed.fits under a setting with nonces and listed positions of two bytes: one round fits,
   six do not.
8. A chain of 100,000 rounds goes through eight functions on a declared chain, with the numbers
   that follow from the number of rounds. It turns red if one of them runs out of stack. One whose
   time grows with the square of the number of rounds would make the build slow, not red.

Where the expected values come from. A yes or a no was worked out by hand from the sentence that the
change's name tells. The numbers are rules of the format pages in docs/format/: FORMAT.md,
08-parameters.md, 09-key-and-leaf-files.md, 10-proof-file.md. In the bytes of parts 1 and 6 the
words are spelled by hand: a word has eight bytes, the lowest first (R1.1).

Every test is checked when the file compiles. The program verify-on-bytes does not import this file.

Not claimed. No theorem. The chains and parsed records are made up: no public files give them, and
no file of the programs is read. The made-up tables have salts of 48 bytes and the setting has 40,
so that a test sees which of the two a function takes. In the programs' files one line gives both
(08-parameters.md, the line salt), and Declared.keyFormOk does not compare them. At some changes a
second clause refuses too, and a test here does not show which clause has refused. Three clauses of
Declared.chainsFormOk cannot refuse alone: a stored tree of another shape in the first or the second
chain is also a stored tree where none may be, and a first chain without "codes" has not the items'
names either. Two arms of ItemValue.fitsItem are not entered: Entry.cut gives no element of F and no plain
word, so no declared round asks for one. That a listed position is not too wide for its bytes has no
row: in a plan of the format it is below 2 ^ k with k at most eight times these bytes (R8.10), so
that clause cannot refuse alone. Of TableShape.ok one clause is tried, to see that keyFormOk asks
it; clauses of it by themselves: Fmt/ParsedKnown.lean, Fmt/TestChainStm.lean. No verifier calls the
functions that are tried here.
Nothing on soundness, completeness or hiding.
-/
import Fmt.Parsed

namespace Fmt
namespace TestKeyProofForm

/-! ## Made-up chains -/

/-- The tables' shape: rows of 2 ^ 14 with 803 entries of a message and a tail of 1001, 2 ^ 3 rows,
one stored answer a row, salts of 48 bytes. -/
def shape : TableShape := ⟨14, 803, 1001, 3, 1, 48⟩

/-- A declared structure with that shape and no chain: salts of 40 bytes, nonces of eight, no listed
position, one answer to a sample. -/
def bare : Declared where
  files := []
  setting := ⟨.two, 40, 8, 0, 1, 1⟩
  table := shape

/-- A made-up item "the test on the table": a shape's six words, then one word. -/
def testItem (last : UInt64 := 5) (s : TableShape := shape) : ByteArray :=
  cat (s.words.map u64n) ++ u64 last

/-- A round that sends a root and draws a seed. -/
def sendR : DeclaredRound :=
  ⟨{ name := "SEND seed", msg := 32, roots := 1, drawE := 2, drawNZ := 1 }, [], []⟩

/-- A round whose message is one answer to an out-of-domain sample. -/
def answerR : DeclaredRound := ⟨{ name := "SEND answer", msg := 24, answers := 1 }, [], []⟩

/-- A round whose message is one element of E. -/
def splitR : DeclaredRound := ⟨{ name := "SPLIT", msg := 24 }, [], []⟩

/-- A round that ends in a seal. -/
def sealR : DeclaredRound := ⟨{ name := "SEAL" }, [], []⟩

/-- The stored table as the shared chain opens it: at both draws, under the statement's item 0. -/
def storedT : Stored := ⟨⟨14, 8, true, 0⟩, 48, 0, 0, 2⟩

/-- A small tree of one element a column, under the number n. -/
def small (n : Nat := 0) : Shape := ⟨1, 1, false, n⟩

/-- A small tree of two elements a column. -/
def wide : Shape := ⟨1, 2, false, 0⟩

/-- The round LOC: work is asked, two positions are sampled, the stored table is opened. -/
def locR : DeclaredRound := ⟨{ name := "LOC", work := 4, poss := 2, logN := 14 }, [storedT], []⟩

/-- Made-up chains of a key file: the first two send a root each, the first also an answer and an
element, the shared chain opens the stored table, the second opens the two trees. -/
def keyT : ThreeDecl where
  first :=
    { label := 0x46524d02, record := true, rand := .inFile,
      others := [("index-mask message", u64 0), ("ranges", u64 0),
        ("binding tree", u64 0 ++ u64 40), ("codes", u64 9), ("the test on the table", testItem)],
      rounds := [sendR, answerR, splitR, sealR] }
  bind := ⟨0, 40⟩
  shared :=
    { label := 0x4c494e01, rand := .item 1,
      others := [("codes", u64 9), ("the test on the table", testItem)],
      rounds := [sendR, locR, sealR] }
  second :=
    { label := 0x4c494e02, rand := .inFile, others := [], firstTree := 2,
      rounds := [⟨{ name := "CS", poss := 1, logN := 1 }, [],
        [(small, .taken 0 0), (wide, .taken 1 0)]⟩] }

/-- The binding tree's item for a depth and a salt's length. -/
def bindItem (depth salt : UInt64) : ByteArray := u64 depth ++ u64 salt

/-- Made-up chains of a proof file: the key's rounds, under a proof's three labels, items and a
binding tree of the given depth. a, b: the last word of "the test on the table" in the first and in
the shared chain. -/
def proofAt (depth : Nat := 2) (a b : UInt64 := 5) : ThreeDecl :=
  { keyT with
    bind := ⟨depth, 40⟩
    shared := { keyT.shared with
      label := 0x46524d03, others := [("codes", u64 9), ("the test on the table", testItem b)] }
    second := { keyT.second with label := 0x46524d04 }
    first := { keyT.first with
      label := 0x46524d01, record := false,
      others := [("codes", u64 9), ("the test on the table", testItem a),
        ("request's shape", u64 0), ("layout", u64 0), ("links' identifiers", u64 0),
        ("pending rows", u64 1), ("binding tree", bindItem (UInt64.ofNat depth) 40)] } }

/-- The same at depth 2. -/
def proofT : ThreeDecl := proofAt

/-- The first chain changed. -/
def first (g : ChainDecl → ChainDecl) (T : ThreeDecl := keyT) : ThreeDecl :=
  { T with first := g T.first }
/-- The shared chain changed. -/
def shared (g : ChainDecl → ChainDecl) (T : ThreeDecl := keyT) : ThreeDecl :=
  { T with shared := g T.shared }
/-- The second chain changed. -/
def second (g : ChainDecl → ChainDecl) (T : ThreeDecl := keyT) : ThreeDecl :=
  { T with second := g T.second }

/-- Every round of a chain changed. -/
def rounds (g : DeclaredRound → DeclaredRound) (c : ChainDecl) : ChainDecl :=
  { c with rounds := c.rounds.map g }

/-- Every stored tree of a chain changed. -/
def storedAt (g : Stored → Stored) : ChainDecl → ChainDecl :=
  rounds fun r => { r with stored := r.stored.map g }

/-- The second chain with one round CS that opens the given trees. -/
def opening (o : List (Shape × TreeSource)) : ThreeDecl :=
  second fun c => { c with rounds := [⟨{ name := "CS", poss := 1, logN := 1 }, [], o⟩] }

/-- The key's chains with one thing changed: none of these passes. -/
def changedKey : List (String × ThreeDecl) := [
  ("R13.4: the one-time chain under the label of a proof's first chain",
    first fun c => { c with label := 0x46524d01 }),
  ("R13.4: the shared chain under the second chain's label",
    shared fun c => { c with label := 0x4c494e02 }),
  ("R13.4: the second chain under the shared chain's label",
    second fun c => { c with label := 0x4c494e01 }),
  ("R13.15: the one-time chain without the flag of the entry RECORD",
    first fun c => { c with record := false }),
  ("R13.15: the shared chain with the flag", shared fun c => { c with record := true }),
  ("R13.15: the second chain with the flag", second fun c => { c with record := true }),
  ("FORMAT.md 7.8: the one-time chain without random bytes",
    first fun c => { c with rand := .none }),
  ("FORMAT.md 7.8: the shared chain's random bytes are the statement's item 0",
    shared fun c => { c with rand := .item 0 }),
  ("FORMAT.md 7.8: the second chain without random bytes",
    second fun c => { c with rand := .none }),
  ("R13.5: the binding tree's salt is not its item's", { keyT with bind := ⟨0, 48⟩ }),
  ("R14.6: the binding tree's salt, with its item, is not the setting's",
    { keyT with bind := ⟨0, 48⟩, first := { keyT.first with others := keyT.first.others.map fun x =>
        if x.1 == "binding tree" then (x.1, bindItem 0 48) else x } }),
  ("R13.5: the item of the binding tree tells another salt than the tree has",
    first fun c => { c with others := c.others.map fun x =>
      if x.1 == "binding tree" then (x.1, bindItem 0 48) else x }),
  ("R13.6: a binding tree of depth 1, against its item", { keyT with bind := ⟨1, 40⟩ }),
  ("R13.6: a binding tree of depth 1, with its item",
    { keyT with bind := ⟨1, 40⟩, first := { keyT.first with others := keyT.first.others.map fun x =>
        if x.1 == "binding tree" then (x.1, bindItem 1 40) else x } }),
  ("R13.5: other codes in the shared chain",
    shared fun c => { c with others := [("codes", u64 8), ("the test on the table", testItem)] }),
  ("R13.5: another test on the table in the shared chain, longer by a word",
    shared fun c =>
      { c with others := [("codes", u64 9), ("the test on the table", testItem ++ u64 0)] }),
  ("R13.5: a third item in the shared chain",
    shared fun c => { c with others := c.others ++ [("more", u64 0)] }),
  ("R13.5: an item in the second chain", second fun c => { c with others := [("codes", u64 9)] }),
  ("R13.5: the one-time chain's items in the other order",
    first fun c => { c with others := c.others.reverse }),
  ("R13.7: the second chain's first tree is 3", second fun c => { c with firstTree := 3 }),
  ("R7.13: the one-time chain's first tree is 1", first fun c => { c with firstTree := 1 }),
  ("R7.13: the shared chain's first tree is 1", shared fun c => { c with firstTree := 1 }),
  ("R7.4: the stored tree's depth is not the shape's",
    shared (storedAt fun t => { t with sh := { t.sh with a := 13 } })),
  ("R7.4: the stored tree's width is not the shape's",
    shared (storedAt fun t => { t with sh := { t.sh with W := 4 } })),
  ("R7.4: the stored tree's salt is not the shape's",
    shared (storedAt fun t => { t with salt := 40 })),
  ("R7.4: the stored tree is not marked as stored",
    shared (storedAt fun t => { t with sh := { t.sh with stored := false } })),
  ("R7.4: the stored tree has the number 7",
    shared (storedAt fun t => { t with sh := { t.sh with tree := 7 } })),
  ("R14.9: LOC opens the stored table at one of its two draws",
    shared (storedAt fun t => { t with count := 1 })),
  ("R14.9: LOC opens the stored table under the statement's item 1",
    shared (storedAt fun t => { t with item := 1 })),
  ("R14.9: LOC opens the stored table from the draw 1 on",
    shared (storedAt fun t => { t with lo := 1 })),
  ("R14.9: LOC opens the stored table twice",
    shared (rounds fun r => { r with stored := r.stored ++ r.stored })),
  ("R14.9: LOC opens a tree of the chain", shared (rounds fun r =>
    if r.entry.name == "LOC" then { r with opens := [(small, .own 0)] } else r)),
  ("R13.19: two rounds LOC", shared fun c => { c with rounds := [sendR, locR, locR, sealR] }),
  ("R13.19: no round LOC",
    shared fun c => { c with rounds := c.rounds.filter fun r => r.entry.name != "LOC" }),
  ("R14.9: another round of the shared chain opens a stored table too", shared (rounds fun r =>
    if r.entry.name == "SEND seed" then { r with stored := [{ storedT with count := 0 }] } else r)),
  ("FORMAT.md 7.6: the one-time chain opens a stored table",
    first (rounds fun r => { r with stored := [{ storedT with count := 0 }] })),
  ("09-key-and-leaf-files.md 9.7, the trees of a key file: the second chain opens a stored table",
    second (rounds fun r => { r with stored := [{ storedT with count := 0 }] })),
  ("R13.12: a round samples a position and opens nothing",
    second (rounds fun r => { r with opens := [] })),
  ("R6.2: a round CS that samples no position",
    second (rounds fun r => { r with entry := { r.entry with poss := 0 } })),
  ("R6.2: a round SEND seed without an element that is not 0",
    first (rounds fun r => { r with entry := { r.entry with drawNZ := 0 } })),
  ("R6.2: the same in the shared chain", shared (rounds fun r =>
    if r.entry.name == "SEND seed" then { r with entry := { r.entry with drawNZ := 0 } } else r)),
  ("a chain without a round", second fun c => { c with rounds := [] }),
  ("R13.19: the second chain has a round SEAL",
    second fun c => { c with rounds := c.rounds ++ [sealR] }),
  ("R13.6: the one-time chain does not end in SEAL",
    first fun c => { c with rounds := c.rounds.dropLast }),
  ("R13.19: the shared chain does not end in SEAL",
    shared fun c => { c with rounds := c.rounds.dropLast }),
  ("R14.11: a round under a name that the format has not",
    first fun c =>
      { c with rounds := [⟨{ name := "FOO", msg := 32, roots := 1 }, [], []⟩, sealR] }),
  ("R1.1: a word of the plan of 2 ^ 64", first fun c => { c with rounds :=
    [{ sendR with entry := { sendR.entry with rows := 2 ^ 64 } }, sealR] }),
  ("R12.9: a message of a root and eight bytes, which are no element of E",
    first fun c => { c with rounds :=
      [{ sendR with entry := { sendR.entry with msg := 40 } }, sealR] }),
  ("R7.13: a round opens a tree of its chain that the chain does not send",
    second (rounds fun r => { r with opens := r.opens ++ [(small 101, .own 99)] })),
  ("R7.13: a tree is taken over that the one-time chain never sent",
    opening [(small 1, .taken 0 1)]),
  ("R7.13: a tree is taken over from the second chain itself", opening [(small, .taken 2 0)]),
  ("R7.13: a tree is taken over under another number", opening [(small 1, .taken 0 0)]),
  ("R7.13: the one-time chain takes a tree over", first (rounds fun r =>
    if r.entry.name == "SEND seed" then { r with opens := [(small, .taken 0 0)] } else r)),
  ("R7.13: the shared chain takes a tree over", shared (rounds fun r =>
    if r.entry.name == "SEND seed" then { r with opens := [(small, .taken 0 0)] } else r)) ]

/-- The declared structure with a key's chains. -/
def withKey (T : ThreeDecl) : Declared := { bare with key := T }

/-- The declared structure with a proof's chains. -/
def withProof (T : ThreeDecl) : Declared := { bare with proof := T }

/-- The shape with a tail of 2 ^ 14 entries, as long as a row. -/
def longTail : TableShape := { shape with tail := 2 ^ 14 }

/-- A chain whose item "the test on the table" begins with the shape s. -/
def itemOf (s : TableShape) (c : ChainDecl) : ChainDecl :=
  { c with others := c.others.map fun x =>
      if x.1 == "the test on the table" then (x.1, testItem 5 s) else x }

/-- A round SEND seed as two answers to a sample ask it (R6.2). -/
def twoNZ (r : DeclaredRound) : DeclaredRound :=
  if r.entry.name == "SEND seed" then { r with entry := { r.entry with drawNZ := 2 } } else r

/-- The key's chains under another setting or shape: none of these passes. -/
def changedUnder : List (String × Declared) := [
  ("R13.13: the shape's tail is not the item's",
    { withKey keyT with table := { shape with tail := 1000 } }),
  ("08-parameters.md 8.1, test 20: a listed position of nine bytes",
    { withKey keyT with setting := { bare.setting with posB := 9 } }),
  ("R8.2: a nonce of no byte", { withKey keyT with setting := { bare.setting with nonce := 0 } }),
  ("R8.2: a nonce of nine bytes",
    { withKey keyT with setting := { bare.setting with nonce := 9 } }),
  ("R12.1: message and tail are longer than a row, in the shape and in both chains' items alike",
    { withKey (first (itemOf longTail) (shared (itemOf longTail))) with table := longTail }),
  ("R13.8: two answers to a sample, one stored answer a row",
    { withKey keyT with setting := { bare.setting with samples := 2 } }),
  ("R13.8: the same, with two elements that are not 0 in each round SEND seed",
    { withKey (first (rounds twoNZ) (shared (rounds twoNZ))) with
      setting := { bare.setting with samples := 2 } }) ]

/-! ## Made-up parsed records -/

/-- A word that spells no element of either field of the format. -/
def big : UInt64 := 18446744073709551615

/-- Eight made-up answers. -/
def eight : List Ext := (List.range 8).map fun i => (UInt64.ofNat i, 7, UInt64.ofNat (i * i))

/-- A round's record without a nonce, a listed position or an opening. -/
def said (vals : List ItemValue) : RoundParsed := ⟨vals, none, [], []⟩

/-- A column of n elements with a salt of the given number of bytes: the setting's 40, or the
tables' 48. -/
def column (n : Nat) (salt : Nat := 40) : List UInt64 × ByteArray :=
  (List.replicate n 3, pattern salt)

/-- The record of the first chain: 32 random bytes, a root, an answer, an element, nothing for
SEAL. -/
def firstP : ChainParsed :=
  ⟨some (pattern 32), [said [.root zero32], said [.answer (1, 2, 3)], said [.e (4, 5, 6)], said []]⟩

/-- The record of the shared chain: a root; a nonce and the stored table opened at two columns of
eight. -/
def sharedP : ChainParsed :=
  ⟨none, [said [.root zero32], ⟨[], some 7, [], [⟨[column 8 48, column 8 48], [zero32]⟩]⟩, said []]⟩

/-- The record of the second chain: two trees opened at one column each, of one and of two. -/
def secondP : ChainParsed :=
  ⟨some (pattern 32 5 1), [⟨[], none, [], [⟨[column 1], []⟩, ⟨[column 2], [zero32]⟩]⟩]⟩

/-- A made-up record of a key file that fits keyT. -/
def keyP : KeyParsed :=
  ⟨headOf tagKey .two, ⟨zero32, eight⟩, firstP, ⟨0, pattern 40, []⟩, sharedP, secondP⟩

/-- keyP with other messages in the first three rounds of the first chain. -/
def messages (a : List ItemValue := [.root zero32]) (b : List ItemValue := [.answer (1, 2, 3)])
    (c : List ItemValue := [.e (4, 5, 6)]) : KeyParsed :=
  { keyP with first := { firstP with rounds := [said a, said b, said c, said []] } }

/-- A made-up record of a proof file that fits proofT: a slot in a tree of depth 2. -/
def proofP : ProofParsed :=
  ⟨headOf tagProof .two, 258, firstP, ⟨3, pattern 40, [zero32, zero32]⟩, sharedP, secondP⟩

/-- The round LOC in the shared chain's record changed: the one round there with an opening. -/
def atLocRound (g : RoundParsed → RoundParsed) (F : KeyParsed := keyP) : KeyParsed :=
  { F with shared := { F.shared with rounds := F.shared.rounds.map fun r =>
      if r.opens.isEmpty then r else g r } }

/-- The opening of LOC changed. -/
def atLoc (g : OpenParsed → OpenParsed) : KeyParsed :=
  atLocRound fun r => { r with opens := r.opens.map g }

/-- The key file's record with one thing changed: none of these fits. -/
def changedKeyP : List (String × KeyParsed) := [
  ("R13.1: an entry file's head", { keyP with head := headOf tagEntry .two }),
  ("R13.1: the other field's version", { keyP with head := headOf tagKey .one }),
  ("R13.2: a root of 31 bytes", { keyP with table := ⟨zeroBytes 31, eight⟩ }),
  ("R13.2: seven answers for eight rows", { keyP with table := ⟨zero32, eight.drop 1⟩ }),
  ("R1.4: an answer that is not canonical",
    { keyP with table := ⟨zero32, (big, 0, 0) :: eight.drop 1⟩ }),
  ("R4.5: the one-time chain without its random bytes",
    { keyP with first := { firstP with rand := none } }),
  ("R4.5: random bytes of 33", { keyP with first := { firstP with rand := some (pattern 33) } }),
  ("R4.5: the shared chain with random bytes in the file",
    { keyP with shared := { sharedP with rand := some (pattern 32) } }),
  ("R8.1: a round less", { keyP with first := { firstP with rounds := firstP.rounds.dropLast } }),
  ("R8.1: a round more",
    { keyP with first := { firstP with rounds := firstP.rounds ++ [said []] } }),
  ("R4.3: two roots where the entry's word tells one", messages [.root zero32, .root zero32]),
  ("R12.9: an element where a root is sent", messages [.e (1, 2, 3)]),
  ("R1.5: a root of 31 bytes in a message", messages [.root (zeroBytes 31)]),
  ("R1.4: an answer in a message that is not canonical", messages (b := [.answer (big, 0, 0)])),
  ("R1.4: an element in a message that is not canonical", messages (c := [.e (0, big, 0)])),
  ("R8.8: an element where an answer is sent", messages (b := [.e (1, 2, 3)])),
  ("R8.8: an answer where an element is sent", messages (c := [.answer (4, 5, 6)])),
  ("R8.8: a message without its item", messages (b := [])),
  ("R8.2: a nonce where no work is asked",
    { keyP with first := { firstP with
        rounds := ⟨[.root zero32], some 0, [], []⟩ :: firstP.rounds.drop 1 } }),
  ("R8.2: no nonce where work is asked", atLocRound fun r => { r with nonce := none }),
  ("R8.2: a listed position where the plan lists none",
    atLocRound fun r => { r with listed := [1] }),
  ("R13.6: the slot 1 in a tree of depth 0", { keyP with slot := ⟨1, pattern 40, []⟩ }),
  ("R13.2: a slot's salt of 39 bytes", { keyP with slot := ⟨0, pattern 39, []⟩ }),
  ("R13.2: a slot's salt of the tables' 48 bytes", { keyP with slot := ⟨0, pattern 48, []⟩ }),
  ("R13.6: a digest on the path of a tree of depth 0",
    { keyP with slot := ⟨0, pattern 40, [zero32]⟩ }),
  ("R6.6: three columns behind two draws",
    atLoc fun o => { o with cols := [column 8 48, column 8 48, column 8 48] }),
  ("R7.8: no column", atLoc fun o => { o with cols := [] }),
  ("R7.8: a column of seven elements",
    atLoc fun o => { o with cols := [column 8 48, column 7 48] }),
  ("R13.19: a column of the stored table with a salt of the setting's 40 bytes",
    atLoc fun o => { o with cols := [column 8 48, column 8 40] }),
  ("R7.3: a column of a tree of the chains with a salt of the tables' 48 bytes",
    { keyP with second := { secondP with rounds :=
        [⟨[], none, [], [⟨[column 1 48], []⟩, ⟨[column 2], [zero32]⟩]⟩] } }),
  ("R8.7: the two openings of the second chain's round in each other's places",
    { keyP with second := { secondP with rounds := secondP.rounds.map fun r =>
        { r with opens := r.opens.reverse } } }),
  ("R1.3: an element of a column that is not canonical",
    atLoc fun o => { o with cols := [column 8 48, (List.replicate 8 big, pattern 48)] }),
  ("R8.7: the second chain's round with one of its two openings",
    { keyP with second := { secondP with rounds := secondP.rounds.map fun r =>
        { r with opens := r.opens.take 1 } } }),
  ("R7.8: a given digest of 31 bytes", atLoc fun o => { o with given := [zeroBytes 31] }) ]

/-- The proof file's record with one thing changed: none of these fits. -/
def changedProofP : List (String × ProofParsed) := [
  ("R14.2: a key file's head", { proofP with head := headOf tagKey .two }),
  ("R14.7: the slot 4 in a tree of depth 2",
    { proofP with slot := ⟨4, pattern 40, [zero32, zero32]⟩ }),
  ("R14.7: one digest on the path of a tree of depth 2",
    { proofP with slot := ⟨3, pattern 40, [zero32]⟩ }),
  ("R14.7: a digest of 31 bytes on the path",
    { proofP with slot := ⟨3, pattern 40, [zero32, zeroBytes 31]⟩ }),
  ("R14.1: the first and the second chain in each other's places",
    { proofP with first := secondP, second := firstP }) ]

/-- A setting with nonces and listed positions of two bytes. -/
def listing : PlanSetting := ⟨.two, 40, 2, 2, 1, 1⟩

/-- A round that asks work and samples three positions below 2 ^ 10. No tree is opened: the form of
nonce and list alone is tried. -/
def listedR : DeclaredRound := ⟨{ name := "CS", work := 4, poss := 3, logN := 10 }, [], []⟩

/-- Records of that round that do not fit under that setting. -/
def changedListed : List (String × RoundParsed) := [
  ("R8.2: the list is not increasing", ⟨[], some 258, [2, 1], []⟩),
  ("R8.2: a position twice", ⟨[], some 258, [1, 1], []⟩),
  ("R6.6: a position that is not below 2 ^ 10", ⟨[], some 258, [1, 1024], []⟩),
  ("R6.6: four positions behind three draws", ⟨[], some 258, [1, 2, 3, 4], []⟩),
  ("R8.2: no list", ⟨[], some 258, [], []⟩),
  ("R8.2: a nonce too wide for its two bytes", ⟨[], some 65536, [1], []⟩) ]

/-- A made-up chain of one round, a word and the nonce 258, for the writers of a key file and a
proof file. -/
def one (x : UInt64) (rand : Option ByteArray) : ChainParsed :=
  ⟨rand, [⟨[.word x], some 258, [], []⟩]⟩

/-- A plan under which a nonce and a listed position have n bytes each. A writer reads no more of
it. -/
def planOf (n : Nat) : Plan :=
  { field := .two, salt := 40, nonce := n, posB := n, samples := 1, saved := 1, entries := [] }

/-- The names of the members that a test admits. -/
def admitted {α : Type} (test : α → Bool) (l : List (String × α)) : List String :=
  (l.filter fun x => test x.2).map (·.1)

end TestKeyProofForm

open TestKeyProofForm

-- 1. the head
#guard hex (headOf tagKey .two) == "4350494b48383231" && headOf tagKey .two == ascii "CPIKH821"
#guard headOf tagEntry .two == ascii "CPENH821" && headOf tagProof .two == ascii "CPPFH821" &&
  headOf tagKey .one == ascii "CPIKH811"

-- 2. a key file's chains
#guard (withKey keyT).keyFormOk
#guard changedKey.length == 54 && admitted (fun T => (withKey T).keyFormOk) changedKey == []
#guard changedUnder.length == 7 && admitted Declared.keyFormOk changedUnder == []

-- 3. the labels
#guard admitted (fun T => (withProof T).proofFormOk)
  [("R14.9: the shared chain under a key's label",
      shared (fun c => { c with label := 0x4c494e01 }) proofT),
   ("R14.10: the second chain under a key's label",
      second (fun c => { c with label := 0x4c494e02 }) proofT),
   ("R14.9, R14.10: the two in each other's places",
      shared (fun c => { c with label := 0x46524d04 })
        (second (fun c => { c with label := 0x46524d03 }) proofT))] == []
#guard admitted (fun T => (withKey T).keyFormOk)
  [("R13.4: the shared chain under a proof's label",
      shared fun c => { c with label := 0x46524d03 }),
   ("R13.4: the second chain under a proof's label",
      second fun c => { c with label := 0x46524d04 })] == []

-- 4. a proof file's chains
#guard (withProof proofT).proofFormOk && (withProof (proofAt 48)).proofFormOk &&
  (withProof
    (first (fun c => { c with others := c.others ++ [("more", u64 0)] }) proofT)).proofFormOk
#guard admitted (fun T => (withProof T).proofFormOk)
  [("R14.3: a key's chains", keyT),
   ("R14.3: the flag of the entry RECORD", first (fun c => { c with record := true }) proofT),
   ("R14.6: a binding tree of depth 49", proofAt 49),
   ("R14.6: the item tells the depth 2, the tree has 3", { proofT with bind := ⟨3, 40⟩ }),
   ("R14.3: the items request's shape and layout in each other's places",
      first (fun c => { c with others := c.others.take 2 ++ [("layout", u64 0),
        ("request's shape", u64 0)] ++ c.others.drop 4 }) proofT),
   ("R14.3: the first item is missing",
      first (fun c => { c with others := c.others.drop 1 }) proofT),
   ("R1.9: a further item under a name with a byte below 0x20",
      first (fun c => { c with others := c.others ++ [("more\n", u64 0)] }) proofT)] == []
-- R14.9: the last word of "the test on the table" is 22 in both chains; 22 and 21
#guard ((withProof (proofAt 2 22 22)).proofFormOk, (withProof (proofAt 2 22 21)).proofFormOk) ==
  (true, false)

-- 5. the two trees of the made-up key, which the second chain alone opens, by the chain that has
-- sent them; the same in a proof file; a tree that its own chain opens, in an entry file
#guard (withKey keyT).shapeOf 1 0 0 == some (small 0) &&
  (withKey keyT).shapeOf 1 1 0 == some wide &&
  (withProof proofT).shapeOf 2 0 0 == some (small 0) &&
  (withProof proofT).shapeOf 2 1 0 == some wide
#guard ({ bare with link := { keyT.first with
    rounds := [{ sendR with opens := [(⟨3, 5, false, 0⟩, .own 0)] }] } } :
  Declared).shapeOf 0 0 0 == some ⟨3, 5, false, 0⟩
-- a tree of the second chain's own, number 5, is no other chain's number 5
#guard (let D := withKey (second (rounds fun r =>
    { r with opens := r.opens ++ [(⟨2, 3, false, 7⟩, .own 5)] }))
  (D.shapeOf 1 2 5, D.shapeOf 1 0 5, D.shapeOf 1 1 5)) == (some ⟨2, 3, false, 7⟩, none, none)
-- none where nothing opens it: another number, another chain, a file without chains, no such file
#guard (withKey keyT).shapeOf 1 0 1 == none && (withKey keyT).shapeOf 1 2 0 == none &&
  bare.shapeOf 1 0 0 == none && (withKey keyT).shapeOf 2 0 0 == none &&
  (withKey keyT).shapeOf 0 0 0 == none && (withKey keyT).shapeOf 3 0 0 == none

-- 6. a round: the message; two low bytes of the nonce 258; three positions of two bytes; an opening
#guard hex (RoundParsed.bytes (planOf 2)
    ⟨[.word 5, .root zero32], some 258, [1, 2, 515], [⟨[([7], pattern 2)], [pattern 3]⟩]⟩) ==
  "0500000000000000" ++ hex zero32 ++ "0201" ++ "010002000302" ++ "0700000000000000" ++
    hex (pattern 2) ++ hex (pattern 3)
-- a slot: the word, the salt, the path
#guard hex (SlotParsed.bytes ⟨3, pattern 2, [pattern 3, pattern 1]⟩) ==
  "0300000000000000" ++ hex (pattern 2) ++ hex (pattern 3) ++ hex (pattern 1)
-- a key file: head, root, answers, one-time chain, slot, shared chain, second chain; the nonce 258
-- has one byte under the first chain's plan, two under the shared chain's, three under the second's
#guard hex (KeyParsed.bytesAt (planOf 1) (planOf 2) (planOf 3) ⟨ascii "CPIKH821",
    ⟨zero32, [(1, 2, 3)]⟩, one 4 (some (pattern 32)), ⟨0, pattern 2, []⟩, one 5 none,
    one 6 (some (pattern 32 5 1))⟩) ==
  hex (ascii "CPIKH821") ++ hex zero32 ++
    "0100000000000000" ++ "0200000000000000" ++ "0300000000000000" ++
    hex (pattern 32) ++ "0400000000000000" ++ "02" ++ "0000000000000000" ++ hex (pattern 2) ++
    "0500000000000000" ++ "0201" ++ hex (pattern 32 5 1) ++ "0600000000000000" ++ "020100"
-- a proof file: head, the table's number in four bytes, first chain, slot, shared, second chain
#guard hex (ProofParsed.bytesAt (planOf 1) (planOf 2) (planOf 3) ⟨ascii "CPPFH821", 258,
    one 4 (some (pattern 32)), ⟨1, pattern 2, [zero32]⟩, one 5 none,
    one 6 (some (pattern 32 5 1))⟩) ==
  hex (ascii "CPPFH821") ++ "02010000" ++ hex (pattern 32) ++ "0400000000000000" ++ "02" ++
    "0100000000000000" ++ hex (pattern 2) ++ hex zero32 ++ "0500000000000000" ++ "0201" ++
    hex (pattern 32 5 1) ++ "0600000000000000" ++ "020100"

-- 7. the parsed records
#guard keyP.fits (withKey keyT) && proofP.fits (withProof proofT)
#guard changedKeyP.length == 34 && admitted (fun F => F.fits (withKey keyT)) changedKeyP == []
#guard changedProofP.length == 5 &&
  admitted (fun F => F.fits (withProof proofT)) changedProofP == []
-- a round under a setting that lists positions
#guard (⟨[], some 258, [1, 2, 515], []⟩ : RoundParsed).fits listing listedR &&
  changedListed.length == 6 && admitted (fun x => x.fits listing listedR) changedListed == []

-- 8. 100,000 rounds, each with a root and an opening. The plan has one entry more, RECORD. An entry
-- has in the parameter bytes its name's length, the nine bytes of "SEND seed" and eleven words.
#guard
  (let c : ChainDecl := { keyT.first with
      rounds := List.replicate 100000 { sendR with opens := [(small, .own 0)] } }
   (c.roots, bare.chainOk c, c.takenOk [], storedShapeOk shape c, (bare.planWords c).length,
    (bare.params c zero32).size - (bare.params { c with rounds := [] } zero32).size,
    (bare.spec c zero32 ByteArray.empty).isSome, (withKey (first fun _ => c)).shapeOf 1 0 0)) ==
  (100000, true, true, true, 100001, 100000 * (8 + 9 + 8 * 11), true, some (small 0))

end Fmt

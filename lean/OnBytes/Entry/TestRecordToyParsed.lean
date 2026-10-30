-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestRecordToyParsed.lean: the parsed record of an entry file (Fmt/ParsedTypes.lean),
its writer and its test of form (Fmt/Parsed.lean), at the programs' own toy entry file of
OnBytes/Entry/RecordToyFiles.lean.

`parsed` is the record of what Entry.read (OnBytes/Entry/File.lean) has read of the file's chain.
The strict reader of Fmt/Rules8XFast.lean, under the description that the declared structure of
OnBytes/Entry/TestRecordToyDeclared.lean gives, reads the same record.

1. Written back. EntryParsed.bytes of that record is the programs' file, byte for byte. The head's 8
   bytes and the chain's 32 random bytes were cut out of the file, so of these the place alone is
   tried here; 2 holds the head's value and the length 32.
2. The record fits the declared structure (EntryParsed.fits). It has 19 rounds, 15 with a message
   and 4 with a nonce, and the rounds 3, 11, 16 and 18, from 0, have openings. These numbers were
   read off the entries in the programs' parameter bytes (R4.3) by a program outside Lean: 20
   entries, of which the first, RECORD, is no round (R13.15); 15 with bytes of a message; 4 with
   work; 4 with positions.
3. The structure changed, the record kept: under a shape with two answers a row, and under a link
   that is declared without random bytes, the record does not fit. The statement that
   EntryParsed.stm makes of the first table and the record is the toy's: the record's table and the
   statement's further table are one value here, so what is tried is which table stands where.
4. Records that do not fit: the honest record with one thing changed, 31 of them, each under a name
   that says what was changed. Six hold a word that is no element of the field: p, the field's
   modulus (R1.2), the least such word. A reader rejects it in an element of the field (R1.3; in a
   column: R7.10) and in each coordinate of an element of the extension field (R1.4). With p - 1 in
   the same six places the record fits: the test of form hashes nothing, so what it refuses there
   is the spelling.
5. Four of the 31 are written back to the honest file's very bytes: answers and elements have one
   spelling, either way; a round without a byte adds none; under a setting that lists no position a
   listed position is written in no byte. So "written back" alone does not see them, and 1 needs 2
   beside it. The bytes of the other 27 are compared with the file and given to no reader.
6. The six records with the word p, written to bytes, are copies of the honest file in which at most
   eight bytes are turned. Entry.check refuses each, under a name of the form: "record-answers" in
   the table's answers, "reader-form" in a message and in a column. With p - 1 they are refused
   under other names. The strict reader of Fmt/ refuses the four copies whose chain is turned.
   What this does not show: a turned word also turns what is hashed, so the two readers would
   refuse the four copies of the chain at a proof of work or at a root even without their test of
   the spelling. "record-answers" is the deciding reader's own refusal (OnBytes/Entry/Table.lean).
   "reader-form" is the word of the second walk that names a refusal, on which no verdict depends
   (OnBytes/Chain/Why.lean): it says where that walk stops. That the names at p - 1 are others was
   foretold and not derived: a hash differs, and the next proof of work, of 8 bits, or the
   opening's root then fails, but for a chance of 1 in 256 at a work.
7. The numbers that hang on the draws (ChainParsed.counts). No position is listed. Each opening has
   one column for each position of its draws, taken once (R6.6, R7.8): a stored table's of its part
   of the draws (R7.19), another tree's of all, each modulo the tree's length (R7.2, R7.15). It has
   one given digest for each vertex on the way to the root whose sibling has no opened leaf below
   it (R7.9). Both numbers are counted here anew, from the positions that the reader has drawn; no
   number of columns has a source outside Lean. The count is held at the page's own example (R7.9:
   depth 3, the list 0, 5, 7: four digests) and at four lists worked out by hand.
8. Which salt. In the toy all salts have 40 bytes. With the salts of the stored tables' openings, or
   those of the other trees' openings, made longer by 8 bytes in the record, and the stored trees'
   number, or the setting's, raised to 48 in the structure: a record fits where the stored tables'
   openings have the stored trees' number and the others the setting's (R8.7), and nowhere else.

What is expected follows from the rules named, from the text of the tests of form, and from the
programs' parameter bytes. No expected value was read off an evaluation in Lean. The names of
refusals in 6 are this library's own: no table of the programs has these copies.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. One honest file. How many columns and given digests an opening must have
follows from the draws and is not tested by EntryParsed.fits (Fmt/Parsed.lean, head, 4). The two
stored tables have parts of 76 draws each and columns of 8 words each, so no test here sees whether
a function takes the one table's number for the other's. The data are made-up toy data: no model, no
weights. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Entry.TestRecordToyDeclared
import Fmt.Rules8XFast
import Fmt.Parsed

namespace OnBytes.Entry.RecordToy
open Fmt

/-- The link's chain in the entry file: behind the head's 8 bytes, the root's 32 and eight answers
of 24 bytes (R13.3). -/
def chainBytes : ByteArray := entryFile.extract 232 entryFile.size

/-- What the strict reader of Fmt/ reads of bytes of a chain, under the description that the
declared structure gives. -/
def chainRead (b : ByteArray) : Option ChainOut := do
  let D ← declared
  let x ← statementAt
  let S ← D.spec D.link D.cfg x.bytes
  wholeChainXF S b

/-- What Entry.read has read of the programs' entry file. -/
def entryRead : Option EntryRead := do
  let p ← Params.Link.read entryParameters
  let t ← firstTable
  (Entry.read p t entryFile).toOption

/-- The record of the programs' entry file, from what a reader has read of its chain. -/
def recordOf (o : ChainOut) : Option EntryParsed := do
  let D ← declared
  let f ← furtherTable
  let c ← ChainParsed.of (D.plan D.link) (some (chainBytes.extract 0 32)) o
  pure ⟨entryFile.extract 0 8, ⟨f.root, f.answers.map extOf⟩, c⟩

/-- The record of the programs' entry file. -/
def parsed : Option EntryParsed := entryRead.bind fun r => recordOf r.chain.out

-- there is a record, and the strict reader of Fmt/ gives the same
#guard parsed.isSome && (chainRead chainBytes).bind recordOf == parsed

-- 1. written back
#guard (declared.bind fun D => parsed.map fun F => F.bytes D == entryFile) == some true

-- 2. the record fits; its numbers are those of the programs' entries
#guard (declared.bind fun D => parsed.map fun F => F.fits D) == some true
#guard (parsed.map fun F =>
  (F.link.rounds.length, (F.link.rounds.filter fun r => !r.vals.isEmpty).length,
    (F.link.rounds.filter fun r => r.nonce.isSome).length,
    (F.link.rounds.zipIdx.filter fun r => !r.1.opens.isEmpty).map (·.2))) ==
  some (19, 15, 4, [3, 11, 16, 18])

-- 3. two answers a row in the shape, one in the record; a link declared without random bytes
#guard (declared.bind fun D => parsed.map fun F =>
  (F.fits { D with table := { D.table with answers := 2 } },
    F.fits { D with link := { D.link with rand := .none } })) == some (false, false)
-- the statement, from the first table and the record
#guard (parsed.bind fun F => statementAt.map fun x => EntryParsed.stm x.first F == x) == some true

/-- The rounds changed by g. -/
def atRounds (g : List RoundParsed → List RoundParsed) (F : EntryParsed) : EntryParsed :=
  { F with link := { F.link with rounds := g F.link.rounds } }

/-- Round i, from 0, changed by g. -/
def atRound (i : Nat) (g : RoundParsed → RoundParsed) : EntryParsed → EntryParsed :=
  atRounds fun l => l.zipIdx.map fun r => if r.2 == i then g r.1 else r.1

/-- Opening j of round i changed by g. -/
def atOpening (i j : Nat) (g : OpenParsed → OpenParsed) : EntryParsed → EntryParsed :=
  atRound i fun r =>
    { r with opens := r.opens.zipIdx.map fun o => if o.2 == j then g o.1 else o.1 }

/-- The first column, with its salt, changed by g. -/
def atColumn (g : List UInt64 × ByteArray → List UInt64 × ByteArray) (o : OpenParsed) :
    OpenParsed :=
  { o with cols := o.cols.zipIdx.map fun c => if c.2 == 0 then g c.1 else c.1 }

/-- The first member of a list changed by g. -/
def atFirst {α : Type} (g : α → α) : List α → List α
  | [] => []
  | a :: l => g a :: l

/-- An answer in the place of an element, and the other way round: the same bytes. -/
def otherKind : ItemValue → ItemValue
  | .e x => .answer x
  | .answer x => .e x
  | g => g

/-- The places, from 0, of six rounds of the link: the first that has no byte in the file; the first
that sends a root; the first whose message has answers; the round LINK, which has a nonce and opens
the two stored tables; the first whose message is elements alone; the first that opens a tree of the
chain's own. -/
structure Places where
  silent  : Nat
  root    : Nat
  answer  : Nat
  link    : Nat
  element : Nat
  own     : Nat

/-- The six places, from the declared rounds. By the entries in the programs' parameter bytes they
are 0 (LINK point), 1 (SEND seed), 2 (SEND answer, with two answers), 3, 6 (FOLD epsilon, with one
element) and 11 (CS, the first round behind LINK that samples positions). -/
def places (D : Declared) : Option Places := do
  let first (p : DeclaredRound → Bool) : Option Nat :=
    (D.link.rounds.zipIdx.find? fun r => p r.1).map (·.2)
  pure ⟨← first fun r => r.entry.msg == 0 && r.entry.work == 0 && r.entry.poss == 0,
    ← first fun r => r.entry.roots != 0, ← first fun r => r.entry.answers != 0,
    ← first fun r => r.entry.name == "LINK" && r.entry.work != 0 && r.stored.length == 2,
    ← first fun r => r.entry.msg != 0 && r.entry.roots == 0 && r.entry.answers == 0,
    ← first fun r => !r.opens.isEmpty⟩

/-- An answer or an element with w as its first word. -/
def firstWord (w : UInt64) : ItemValue → ItemValue
  | .answer a => .answer (w, a.2)
  | .e a => .e (w, a.2)
  | g => g

/-- A root cut to 31 bytes. -/
def shortRoot : ItemValue → ItemValue
  | .root d => .root (d.extract 0 31)
  | g => g

/-- An element in the place of a root. -/
def noRoot : ItemValue → ItemValue
  | .root _ => .e (1, 2, 3)
  | g => g

/-- The draws of the part of the first stored tree that round i opens. -/
def firstPart (D : Declared) (i : Nat) : Nat :=
  ((D.link.rounds[i]?).bind (·.stored.head?)).elim 0 (·.count)

/-- The positions that round i draws. -/
def drawsOf (D : Declared) (i : Nat) : Nat := (D.link.rounds[i]?).elim 0 (·.entry.poss)

/-- The word w in six places: the first and the third word of the table's first answer; the first
word of the first answer of a message, of the first element of a message, of the first column of the
further table's opening, and of the first column of the opening of a tree of the chain's own. -/
def wordAt (P : Places) (w : UInt64) : List (String × (EntryParsed → EntryParsed)) :=
  [("the word in an answer of the table", fun F =>
      { F with table := { F.table with answers := atFirst (fun a => (w, a.2)) F.table.answers } }),
   ("the word as an answer's third", fun F =>
      { F with table := { F.table with
          answers := atFirst (fun a => (a.1, a.2.1, w)) F.table.answers } }),
   ("the word in an answer of a message", atRound P.answer fun r =>
      { r with vals := atFirst (firstWord w) r.vals }),
   ("the word in an element of a message", atRound P.element fun r =>
      { r with vals := atFirst (firstWord w) r.vals }),
   ("the word in a column", atOpening P.link 1 (atColumn fun c => (atFirst (fun _ => w) c.1, c.2))),
   ("the word in a column of the chain's own tree",
      atOpening P.own 0 (atColumn fun c => (atFirst (fun _ => w) c.1, c.2)))]

/-- The modulus of the field in which the programs compute: the least word that spells no element.
-/
def modulus : UInt64 := 18446744069414584321

/-- The honest record with one thing changed. The first four are written back to the honest bytes.
-/
def misfits (D : Declared) (P : Places) : List (String × (EntryParsed → EntryParsed)) :=
  [("elements for answers", atRound P.answer fun r => { r with vals := r.vals.map otherKind }),
   ("an answer for an element", atRound P.element fun r => { r with vals := r.vals.map otherKind }),
   ("a further round without a byte", atRounds fun l => l ++ [⟨[], none, [], []⟩]),
   ("a listed position where none is listed", atRound P.link fun r => { r with listed := [1] }),
   ("a key file's head", fun F => { F with head := headOf tagKey .two }),
   ("a root of 31 bytes", fun F =>
      { F with table := { F.table with root := F.table.root.extract 0 31 } }),
   ("an answer too many", fun F =>
      { F with table := { F.table with answers := F.table.answers ++ [(1, 2, 3)] } }),
   ("an answer too few", fun F =>
      { F with table := { F.table with answers := F.table.answers.dropLast } }),
   ("no random bytes", fun F => { F with link := { F.link with rand := none } }),
   ("33 random bytes", fun F => { F with link := { F.link with rand := some (zeroBytes 33) } }),
   ("a round less", atRounds fun l => l.dropLast),
   ("a value where no message is", atRound P.silent fun r => { r with vals := [.e (1, 2, 3)] }),
   ("a nonce where no work is asked", atRound P.silent fun r => { r with nonce := some 0 }),
   ("an element for a root", atRound P.root fun r => { r with vals := r.vals.map noRoot }),
   ("a root of 31 bytes in a message", atRound P.root fun r =>
      { r with vals := r.vals.map shortRoot }),
   ("no nonce where work is asked", atRound P.link fun r => { r with nonce := none }),
   ("an opening less", atRound P.link fun r => { r with opens := r.opens.take 1 }),
   ("an opening without a column", atOpening P.link 0 fun o => { o with cols := [] }),
   ("a column more than the part has draws", atOpening P.link 0 fun o =>
      { o with cols := (o.cols.take 1).flatMap (List.replicate (firstPart D P.link + 1)) }),
   ("a column short by a word", atOpening P.link 1 (atColumn fun c => (c.1.dropLast, c.2))),
   ("a salt longer by 8 bytes", atOpening P.link 1 (atColumn fun c => (c.1, c.2 ++ zeroBytes 8))),
   ("a given digest of 31 bytes", atOpening P.link 1 fun o =>
      { o with given := o.given.map fun d => d.extract 0 31 }),
   ("the chain's own tree: a column more than the round has draws", atOpening P.own 0 fun o =>
      { o with cols := (o.cols.take 1).flatMap (List.replicate (drawsOf D P.own + 1)) }),
   ("the chain's own tree: a column short by a word",
      atOpening P.own 0 (atColumn fun c => (c.1.dropLast, c.2))),
   ("the chain's own tree: a salt longer by 8 bytes",
      atOpening P.own 0 (atColumn fun c => (c.1, c.2 ++ zeroBytes 8)))] ++
  wordAt P modulus

/-- The names of the changes of a list under which the record meets the test t. -/
def thoseThat (l : Declared → Places → List (String × (EntryParsed → EntryParsed)))
    (t : Declared → EntryParsed → Bool) : Option (List String) := do
  let D ← declared
  let P ← places D
  let F ← parsed
  pure (((l D P).filter fun g => t D (g.2 F)).map (·.1))

-- 4. none of the 31 fits; with p - 1 for p all six fit
#guard (declared.bind fun D => (places D).map fun P =>
  (P.silent, P.root, P.answer, P.link, P.element, P.own)) == some (0, 1, 2, 3, 6, 11)
#guard (declared.bind fun D => (places D).map fun P => (misfits D P).length) == some 31
#guard thoseThat misfits (fun D F => F.fits D) == some []
#guard (thoseThat (fun _ P => wordAt P (modulus - 1)) fun D F => F.fits D) ==
  some ["the word in an answer of the table", "the word as an answer's third",
    "the word in an answer of a message", "the word in an element of a message",
    "the word in a column", "the word in a column of the chain's own tree"]
#guard Fld.two.p == modulus.toNat

-- 5. the first four are written back to the honest file's bytes, and no other
#guard thoseThat misfits (fun D F => F.bytes D == entryFile) ==
  some ["elements for answers", "an answer for an element", "a further round without a byte",
    "a listed position where none is listed"]

/-- How Entry.check ends on the record changed by each of the six changes, written to bytes. -/
def endingsAt (w : UInt64) : Option (List (Option String)) := do
  let D ← declared
  let P ← places D
  let F ← parsed
  pure ((wordAt P w).map fun g => ending ((g.2 F).bytes D))

-- 6. each copy has the honest file's length and differs from it in at most eight bytes
#guard (do
  let D ← declared
  let P ← places D
  let F ← parsed
  pure ((wordAt P modulus ++ wordAt P (modulus - 1)).all fun g =>
    let b := (g.2 F).bytes D
    b.size == entryFile.size &&
      (let n := ((List.range b.size).filter fun i => b.get! i != entryFile.get! i).length
       decide (1 ≤ n) && decide (n ≤ 8)))) == some true
-- the word p: refused at the form
#guard endingsAt modulus ==
  some [some "record-answers", some "record-answers", some "reader-form", some "reader-form",
    some "reader-form", some "reader-form"]
-- the word p - 1: refused, and not at the form
#guard ((endingsAt (modulus - 1)).map fun l => l.all fun e =>
  e.isSome && !["yes", "record-answers", "reader-form"].contains (e.getD "")) == some true
-- the strict reader of Fmt/ on the four copies whose chain is turned
#guard (do
  let D ← declared
  let P ← places D
  let F ← parsed
  pure (((wordAt P modulus).drop 2).map fun g =>
    (chainRead (((g.2 F).bytes D).extract 232 entryFile.size)).isSome)) ==
  some [false, false, false, false]

/-- How many digests an opening of a tree of depth a is given at the leaves xs, each named once:
depth by depth, one for each vertex whose sibling is not among them. -/
def givenAt : Nat → List Nat → Nat
  | 0, _ => 0
  | a + 1, xs =>
    (xs.filter fun x => !xs.contains (x ^^^ 1)).length + givenAt a (xs.map (· / 2)).eraseDups

/-- The numbers of columns and of given digests of each opening, round by round, from the positions
that were drawn: a stored tree is opened at its part of the draws, another tree at all. -/
def countsFrom (D : Declared) (o : ChainOut) : List (List (Nat × Nat)) :=
  (D.link.rounds.zip o.rounds.toList).map fun y =>
    let two (a : Nat) (ps : List Nat) : Nat × Nat :=
      let xs := (ps.map (· % 2 ^ a)).eraseDups
      (xs.length, givenAt a xs)
    (y.1.stored.map fun t => two t.sh.a ((y.2.drawn.poss.drop t.lo).take t.count)) ++
      y.1.opens.map fun t => two t.1.a y.2.drawn.poss

-- 7. as many positions are drawn as the programs' entries say; the record's numbers
#guard (entryRead.map fun r => (r.chain.out.rounds.toList.map (·.drawn.poss.length)).filter
  (· != 0)) == some [152, 63, 43, 41]
#guard (do
  let D ← declared
  let r ← entryRead
  let F ← parsed
  pure (F.link.counts.all (·.1 == 0), F.link.counts.map (·.2) == countsFrom D r.chain.out)) ==
  some (true, true)
-- the count at a tree of depth 3: the page's example; one leaf; two siblings; two leaves far apart;
-- all eight
#guard [givenAt 3 [0, 5, 7], givenAt 3 [5], givenAt 3 [4, 5], givenAt 3 [0, 7],
  givenAt 3 [0, 1, 2, 3, 4, 5, 6, 7]] == [4, 3, 2, 4, 0]

/-- The salts of all openings of the round LINK (stored := true) or of all other rounds, each longer
by 8 zero bytes. -/
def saltsLonger (P : Places) (stored : Bool) : EntryParsed → EntryParsed :=
  atRounds fun l => l.zipIdx.map fun r =>
    if (r.2 == P.link) == stored then
      { r.1 with opens := r.1.opens.map fun o =>
          { o with cols := o.cols.map fun c => (c.1, c.2 ++ zeroBytes 8) } }
    else r.1

/-- The structure whose stored trees have salts of s bytes. -/
def storedSalt (D : Declared) (s : Nat) : Declared :=
  let rounds := D.link.rounds.map fun r =>
    { r with stored := r.stored.map fun t => { t with salt := s } }
  { D with link := { D.link with rounds := rounds } }

-- 8. the honest record, the one with longer salts at the stored tables, the one with longer salts
-- at the other trees; each under the toy's structure, stored trees' salts of 48, the setting's 48
#guard (do
  let D ← declared
  let P ← places D
  let F ← parsed
  pure ([F, saltsLonger P true F, saltsLonger P false F].map fun G =>
    [D, storedSalt D 48, { D with setting := { D.setting with salt := 48 } }].map G.fits)) ==
  some [[true, false, false], [false, true, false], [false, false, true]]

end OnBytes.Entry.RecordToy

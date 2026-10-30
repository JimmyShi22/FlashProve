-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookAtWritten.lean: the key file's book of coins (`keyBook`, E2E/KeyBook.lean) is evaluated
at the library's written sizes of the full size, `keyFull`
(Johnson/Goal/PlanValues/KeySizedReturns.lean), and is compared, in five groups of tests A to E,
with values that are written separately from it, in other files. Two tables, of what is sent and of
what the book says of each place at this size, are defined as values; nothing is printed.
Definitions that can be evaluated, and tests; no theorem. The lines that begin with `#guard` are the
tests: Lean's evaluator runs them when the file is compiled, and the kernel does not check them.
Public data only, at this one size.

Terms. A book (`ProverCoinCounts`) is a structure of the frame (Johnson/Desc/ProofFile/Honest/Frame.lean: the
types in which an honest prover is written). It is the public table that says how many coins (random
field elements) each part of the prover has of its own, which blocks of these coins other parts are
given too, and how each sub-protocol's rounds are cut into parts. A place (`Place`) is the label of
a sub-protocol; a row is a place with its number of rounds. E2E/KeyPlaces.lean names the places and
says in docstrings which sub-protocol is at each (the lookups, the batching, the split, the four
proximity tests and the others). An entry (`Ahead`) is a block of the coins of one part, its owner,
that one other part, its spender, is given too; it is marked as spent or as carried. A sending is
the list of the oracle messages of one prover's message (with their counts of coins: `Sending`). A
face (`K3.Face`, Johnson/Desc/First/Look/K3LookupGeneral.lean) holds a lookup's public numbers. `KeyPub`
(E2E/KeyBook.lean) is the structure of public data from which `keyBook` computes the book;
`KeyPub.of` computes it from sizes. The written lists are `fullFirst`, `fullShared` and `fullSecond`
(E2E/KeyPlaces.lean): the rows of the first, the shared and the second chain at the full size, as
literals. The written rounds are the library's three lists of the key file's rounds at the full
size, as literals (`dryKeyFull`, Johnson/G/DryKeyLit.lean). Of a written round this file reads only
its entry of the plan (`Fmt.Entry`, Fmt/Plan.lean: the round's name and eleven numbers). Below, an
entry by itself is a book's.

  `fullPub`: a definition: the `KeyPub` of the written sizes: `KeyPub.of` at `keyFull` and at
    `keyFull.set.samples` answers to an OOD sample; `none` if `KeyPub.of` returns nothing. Two
    tests: it is not `none`; the number of answers is 1
  `atFull f`: a definition: the Boolean function f at the value of `fullPub`; false if `fullPub` is
    `none`
  `sendingsTable`: a definition: which oracle messages are sent at which place (`sentAt`,
    E2E/KeyBook.lean), each with its rows' numbers, fields and codes. A test: 9 places send
  `placesTable`: a definition: the table of places (`membersOf`, E2E/KeyBook.lean) at the full size.
    For each of the 35 rows of the written lists: its rounds, the number of its parts, the scalars
    that its written rounds send, its parts' own coins, and whose coins its parts spend and carry
  `written₁`, `written₂`, `written₃`: definitions: the entries of the plan of the written rounds of
    the first, the shared and the second chain
  `along rows es`: a definition: a chain's entries of the plan es, cut along its rows: each place
    with as many of them as its row has rounds, in order
  `writtenAlong`, `writtenAt p`: definitions: all places of the written lists, each with its written
    rounds; the written rounds at the place p, the empty list if p is in no row
  `scalarsOf es`: a definition: the number of scalars that the rounds es send: `scalarsIn`
    (Johnson/Desc/ProofFile/Honest/BookOf.lean), added up

The tests. K is the value of `fullPub`.
  A, the rows. The three lists of rows that are computed from K (`KeyPub.rowsFirst`,
    `KeyPub.rowsShared`, `KeyPub.rowsSecond`, E2E/KeyBookTests.lean) are the written lists.
    `places_of_made` (E2E/KeyPlaces.lean) shows, under its hypotheses, that the written lists are
    the rows of the key file's description at public files in scope. The three lists of written
    rounds have 18851, 68 and 30 rounds: the sums of the written lists' numbers of rounds (a test in
    E2E/KeyPlaces.lean)
  B, the rounds of a lookup. K has two faces, and both pass `Face.ok`. At each, the written rounds
    at the lookup's place, with the proof-of-work bits set to 0, are `K3.entriesV` of the face
    (Johnson/Desc/First/Look/Via/Rounds.lean). By `entries_spans` (E2E/KeyBookFace.lean) that list
    is the rounds of `spansOf`, from which the lookup's entries and cut are computed. These written
    rounds send as many scalars as the face has hidden values (`Face.slots`)
  C, the cut. For every place that has a written round, take the frame's cut by the rounds' names
    (`cutOfNames`, Johnson/Desc/ProofFile/Honest/BookOf.lean) at the place's kind and the written
    rounds' names. The list of these places with these cuts is `K.cuts`, the book's cuts
  D, what the spenders take. Of their two owners, the parts that send the multiplicities and the
    index-mask message, the lookups' entries (`lookups`) take as many coins as the library's
    verifier counts mask entries: `Wf.ownMasks` and `Wf.indexMasks` (OnBytes/Iop/Wf.lean). The
    second number and `1 + 2 * K.kCol` are together `Wf.indexMaskEntries` (same file). For the mask
    tables of these two messages the book counts 36864 and 256 coins: one more than
    `Send.freeMaskEntries` (OnBytes/Iop/Send.lean) returns at literal arguments. The written rounds
    send `1 + 2 * K.kCol` scalars at the batching, 1 at the split, and 2 k + 1 in the first 2 + k
    rounds of each of the four proximity tests, where k is the number of rounds of the test's first
    fold (`firstK`). These are the counts that `KeyPub.spent` gives to the entries of the batching,
    of the split and of three first folds. The first fold of Omega's test is no spender: its part
    owns the fresh table that it sends
  E, the codes at the four last stages. At each of the four proximity tests the count of the masking
    word in the extension field (message 1 of the last sending of `switchSendings`) is the number of
    scalars of the test's last written round, which is named "BASE". This tests which codes are read
    there. It does not test the rule for coins
  The numbers. Further tests state numbers as literals, so that a change of the sizes or of
    `KeyPub.of` makes a test fail: the faces' hidden values and numbers of spans, five cuts, what
    the lookups take, the numbers of spent and of carried entries, the owners' counts, and where six
    mask tables begin (`tableAt`)
  What is sent. `sentAt keyFull 1`, its sendings joined chain by chain, is `sentKey keyFull 1`
    (E2E/TreeRows.lean)

Limits.
- The tests are evaluations by Lean's evaluator, not by its kernel. Theorems on this book at these
  sizes are in other files: `full_made`, `full_rows`, `book_rows` (E2E/KeyBookPassesNamed.lean),
  `book_passes` (E2E/KeyBookThirdNamed.lean).
- Everything is at written values. That the sizes at public files in scope are those of `keyFull` is
  the library's `five_in_scope` (Johnson/RunOne/Law/KeyInScope.lean), whose equations cover all that
  `KeyPub.of` reads. That the rounds there are `dryKeyFull` is stated, of the rounds' data, by
  `pin_at_seat` (Johnson/Goal/Conditions/KeyAtTheSeat.lean), where the test `protocolDataWellFormed` accepts.
  Neither is called here. E2E/KeyBookSourced.lean draws a corollary of the first: in scope, at the
  sizes of the description's own source, `KeyPub.of` returns `fullPub` (`pub_of_made`,
  `pub_of_source`).
- The counts of the four tests' parts after the first fold (`rRng`, `rFolded`, `rOmega`, `rOwn`) are
  compared with nothing in this file, except that E compares the masking word's count in the
  extension field, which is one summand of each.
- The two calls of `Send.freeMaskEntries` in D are at literal arguments: they read nothing of the
  sizes.
- No test here can detect a wrong rule for coins. `sentAt` and `sentKey` are nearly the same text: a
  test of one against the other detects a slip in writing, not a wrong reading.
- `KeyPub.of` is evaluated at this one value, and at no smaller size.
- That all eleven of the frame's tests on a book (`ProverCoinCounts.clauses`) pass at this book, in scope, at
  the key file's own description (`KeyNamed`), where `fullPub = some K`, is `book_passes`
  (E2E/KeyBookThirdNamed.lean).
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookTests
import Johnson.G.DryKeyLit

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open OnBytes
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (entriesV)
open Lk6.AtPlan (keyFull)
open Johnson.G (dryKeyFull)
open ProofFile.Honest (Due cutOfNames scalarsIn)

/-- The `KeyPub` of the written sizes: `KeyPub.of` (E2E/KeyBook.lean) at `keyFull` and at its number
of answers to an OOD sample. `none` if `KeyPub.of` returns nothing. -/
def fullPub : Option KeyPub := KeyPub.of keyFull keyFull.set.samples

/-- A Boolean function at the value of `fullPub`; false if `fullPub` is `none`. -/
def atFull (f : KeyPub → Bool) : Bool := (fullPub.map f).getD false

/-- The entries of the plan of the first chain's written rounds (`dryKeyFull`). -/
def written₁ : List Fmt.Entry := dryKeyFull.1.map (·.1.entry)
/-- The same for the shared chain. -/
def written₂ : List Fmt.Entry := dryKeyFull.2.1.map (·.1.entry)
/-- The same for the second chain. -/
def written₃ : List Fmt.Entry := dryKeyFull.2.2.map (·.1.entry)

/-- A chain's entries of the plan, cut along its rows: each place with as many of them as its row
has rounds, in order. -/
def along : List (Place × Nat) → List Fmt.Entry → List (Place × List Fmt.Entry)
  | [], _ => []
  | r :: l, es => (r.1, es.take r.2) :: along l (es.drop r.2)

/-- All places of the three written lists of rows, each with its written rounds. -/
def writtenAlong : List (Place × List Fmt.Entry) :=
  along fullFirst written₁ ++ along fullShared written₂ ++ along fullSecond written₃

/-- The written rounds at a place; the empty list at a place that is in no row. -/
def writtenAt (p : Place) : List Fmt.Entry := (writtenAlong.lookup p).getD []

/-- The number of scalars that a list of rounds sends: `scalarsIn`
(Johnson/Desc/ProofFile/Honest/BookOf.lean), added up. -/
def scalarsOf (es : List Fmt.Entry) : Nat := (es.map fun e => scalarsIn { entry := e }).sum

#guard fullPub.isSome
#guard keyFull.set.samples == 1

-- A: the rows
#guard atFull fun K =>
  K.rowsFirst == fullFirst && K.rowsShared == fullShared && K.rowsSecond == fullSecond
#guard written₁.length == 18851 && written₂.length == 68 && written₃.length == 30

-- B: the rounds of a lookup
#guard atFull fun K => K.faces.length == 2 && K.faces.all (·.ok)
#guard atFull fun K => K.faces.zipIdx.all fun x =>
  (writtenAt (lookPlace x.2)).map (fun e => { e with work := 0 }) == entriesV x.1
#guard atFull fun K => K.faces.zipIdx.all fun x =>
  scalarsOf (writtenAt (lookPlace x.2)) == x.1.slots
#guard atFull fun K => K.faces.map (·.slots) == [17817, 17116]
#guard atFull fun K => K.faces.map (fun f => (spansOf f).length) == [935, 920]

-- C: the cut
#guard atFull fun K =>
  ((writtenAlong.filter fun x => !x.2.isEmpty).map fun x =>
    (x.1, cutOfNames x.1.kind (x.2.map (·.name)))) == K.cuts
#guard atFull fun K => [rngPlace, battPlace, foldedTestPlace, omegaTestPlace, ownTestPlace].map
  (fun p => K.cuts.lookup p) ==
    [some [6, 17], some [1, 19], some [9, 26], some [6, 18], some [7, 23]]

-- D: what the spenders take
#guard atFull fun K => (lookups K.faces 0 0 0).2 ==
  (Wf.ownMasks keyFull.ranges.x (Wf.matrixOf keyFull.once.shape),
    Wf.indexMasks keyFull.ranges.x (Wf.matrixOf keyFull.once.shape))
#guard atFull fun K => (lookups K.faces 0 0 0).2 == (34885, 48)
#guard atFull fun K => 48 + (1 + 2 * K.kCol) ==
  Wf.indexMaskEntries keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)
#guard atFull fun K => (K.sMsg.getD 0 default).table == 36864 &&
  Send.freeMaskEntries 9 4096 1 == 36863 && (K.sIdx.getD 0 default).table == 256 &&
  Send.freeMaskEntries 1 256 1 == 255
#guard atFull fun K => scalarsOf (writtenAt battPlace) == 1 + 2 * K.kCol
#guard scalarsOf (writtenAt splitPlace) == 1
#guard atFull fun K =>
  [(rngPlace, K.rng), (foldedTestPlace, K.folded), (omegaTestPlace, K.omega),
    (ownTestPlace, K.own)].all fun x =>
      scalarsOf ((writtenAt x.1).take (2 + firstK x.2)) == 2 * firstK x.2 + 1
#guard atFull fun K => K.spent.length == 983 + 967 + 5 && K.carried.length == 20

-- E: the codes at the four last stages
#guard atFull fun K =>
  [(rngPlace, K.rng), (foldedTestPlace, K.folded), (omegaTestPlace, K.omega),
    (ownTestPlace, K.own)].all fun x =>
      ((switchSendings keyFull.codes 1 x.2).bind fun l =>
        l.getLast?.map fun s => (s.getD 1 default).due.e) ==
      (writtenAt x.1).getLast?.map fun e => scalarsIn { entry := e }

-- the numbers: the owners' counts, chain by chain; where six mask tables begin
#guard atFull fun K => (keyBook K).first.map (·.2) ==
  [⟨0, 305⟩, ⟨98, 38098⟩, ⟨0, 22273⟩, ⟨0, 512⟩]
#guard atFull fun K => (keyBook K).shared.map (·.2) ==
  [⟨0, 10541⟩, ⟨0, 1387⟩, ⟨0, 7912⟩, ⟨0, 155⟩, ⟨0, 5698⟩]
#guard atFull fun K => (keyBook K).second.map (·.2) == [⟨0, 5046⟩]
#guard atFull fun K => [tableAt K.sIdx 0, tableAt K.sMsg 0, tableAt K.sMsg 1, tableAt K.sW 1,
  tableAt K.sFolded 1, tableAt K.sOmega 1] == [0, 0, 37305, 403, 10380, 1177]

-- what is sent at which place: joined chain by chain, these are the lists of `sentKey`, from which
-- the table of the key file's trees is computed (`tableKey`, E2E/TreeRows.lean)
#guard (sentAt keyFull 1).map (fun l =>
    ((l.filter (·.1.chain == 1)).flatMap (·.2), (l.filter (·.1.chain == 2)).flatMap (·.2),
      (l.filter (·.1.chain == 3)).flatMap (·.2))) == AtPublicFiles.TreeReads.sentKey keyFull 1

/-- The sendings at the full size. For each place that sends oracle messages: its chain and piece;
then, sending by sending and message by message, the rows of each sort (`dueOf`, E2E/RowCode.lean):
how many, the words of a symbol, the code. A message has `none` if a code of its rows is missing;
the table is `none` if `sentAt` returns nothing. -/
def sendingsTable :=
  (sentAt keyFull 1).map fun l => l.map fun x =>
    ((x.1.chain, x.1.piece), x.2.map fun s => s.map fun n => AtPublicFiles.RowCode.dueOf keyFull.codes n)

/-- The table of places at the full size. For each row of the written lists: chain, link and piece;
the number of rounds; the number of parts; the scalars that the written rounds send; the parts' own
coins (the part's number, the counts in the base field and in the extension field); whose coins are
spent (the owner's chain, piece and part; how many entries; how many coins of the extension field);
whose are carried (the owner; how many entries). `none` if `fullPub` is. -/
def placesTable :=
  fullPub.map fun K =>
    (membersOf (fullFirst ++ fullShared ++ fullSecond) (keyBook K)).map fun m =>
      (m.place.chain, m.place.link, m.place.piece, m.rounds, m.cut.length,
       scalarsOf (writtenAt m.place), m.takes.map fun t => (t.1, t.2.f, t.2.e),
       m.spends.map fun s => ((s.1.place.chain, s.1.place.piece, s.1.part), s.2.1, s.2.2),
       m.carries.map fun c => ((c.1.place.chain, c.1.place.piece, c.1.part), c.2))

-- 9 places send oracle messages; the table of places has 35 rows
#guard (sendingsTable.map (·.length)) == some 9 && (placesTable.map (·.length)) == some 35

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.fullPub
#print axioms AtPublicFiles.KeyBook.atFull
#print axioms AtPublicFiles.KeyBook.written₁
#print axioms AtPublicFiles.KeyBook.written₂
#print axioms AtPublicFiles.KeyBook.written₃
#print axioms AtPublicFiles.KeyBook.along
#print axioms AtPublicFiles.KeyBook.writtenAlong
#print axioms AtPublicFiles.KeyBook.writtenAt
#print axioms AtPublicFiles.KeyBook.scalarsOf
#print axioms AtPublicFiles.KeyBook.sendingsTable
#print axioms AtPublicFiles.KeyBook.placesTable

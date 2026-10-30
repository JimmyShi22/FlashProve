-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookHeldK12.lean: the key file's book of coins (`keyBook`, E2E/KeyBook.lean) is compared, by
tests, with what the two parts of the prover of each of the key file's four proximity tests state
themselves. The parts are `part0 J` and `part1 J` (E2E/KeyTestSizes.lean), that is `firstPart J` and
`restPart J` (Johnson/Desc/ProofFile/Honest/K12/Parts.lean), at the four jobs J of `allJobs`. Three
definitions that can be evaluated, general in the book, and four tests, three of which evaluate the
book at the written sizes of the full size (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean); no theorem. The lines that begin with `#guard` are
the tests: Lean's evaluator runs them when the file is compiled, and the kernel does not check them.

Terms. The frame (Johnson/Desc/ProofFile/Honest/Frame.lean) has the types in which an honest prover
is written and the functions that run it. A book (`ProverCoinCounts`) is its public table of how many coins
(random field elements) each part of the prover has of its own, which blocks of these coins other
parts are given too, and how each sub-protocol's rounds are cut into parts. A place (`Place`) is the
label of a sub-protocol; an address (`Addr`) is a place and the number of a part there. A count
(`Due`) is a number of coins in each of the two fields. An entry (`Ahead`) is a block of the coins
of one part, its owner, that one other part, its spender (the field `spender`), is given too; it is
marked as spent (`once` is true) or as carried (`once` is false). A part (`Part`) is the prover's
side of some consecutive rounds of a sub-protocol. It states its own count (`takes`) and the names
and counts of the entries that it spends (`spends`) and carries (`carries`), and it has one move for
each round (`moves`). A job (`TestJob`, Johnson/Desc/ProofFile/Honest/K12/Test.lean) is what a
caller says of its proximity test. Its members (the field `members`) are the oracle messages of the
test's group, each with the address of the part that sent it, its number in that part's sending (the
oracle messages of one prover's message) and its count. Its field `fresh` names, by address and
number, the first fold's fresh table: the mask table that has the coefficients of the fold's hiding
polynomial; it is `none` where the fold sends the table itself. The first part of a test has the
round "BAT" and the first fold, the second part all later rounds.

Why. The frame returns an error for a part that takes more or fewer coins than the book has for it
(`lendPart`); for a part whose stated names and counts are not, one by one and in the book's order,
those of the spent entries, and of the carried entries, that name it as their spender (`lend`); and
for a list of parts whose numbers of moves are not the book's cut at the place (`chainSteps`). The
book and the parts are two separate definitions, and neither calls the other. This file compares the
two, with the filters on the book's entries that `lendPart` has.

  `heldK12 B`: a definition: the test that the book B and the parts agree at each of the four jobs
    J: `statedBy (part0 J)` is `handedTo B` at part 0 of the job's place, `statedBy (part1 J)` is
    `handedTo B` at part 1 of it, and the cut of B at that place is the list of the two parts'
    numbers of moves
  `handedTo B a`: a definition: what B has for the part at the address a: the count of the first row
    at a in the three tables of B, joined (`dueAt`: 0 if there is no row); the names and counts
    (`Ahead.named`), in the order of B, of the entries whose spender is a and that are spent; the
    same for those that are carried
  `statedBy p`: a definition: what the part p states: `takes`, `spends` and `carries`

The tests. K is the value of `fullPub` (E2E/KeyBookAtWritten.lean): the public data, at the written
sizes, from which `keyBook` computes the book. `atFull` (same file) is false if there is no such
value.
  The places of the four jobs are, in this order, `rngPlace`, `foldedTestPlace`, `omegaTestPlace`
    and `ownTestPlace` (E2E/KeyPlaces.lean), the places under which the book has the four tests.
  `heldK12 (keyBook K)` is true.
  The test can fail: `heldK12` is false at `keyBook K false`, the book without its carried entries,
    and at the book whose carried entries are in reverse order while its spent entries are as they
    were.

Limits.
- The order of the carried entries is not an independent check. The order in which the parts state
  them (the members in the order of sending, the fresh table last) was written in knowledge of the
  book's order. Which messages are members, which parts send them, and the counts were written
  separately from the book.
- The names on both sides are made by the same functions: `runName`, `carriedName` and `foldMaskRun`
  (Johnson/Desc/ProofFile/Honest/ForKinds.lean). So the tests compare the arguments of a name, not
  its wording: for a carried entry the sender's address, the message's number and the address of the
  part that is given it. An address is written there without the kind of its place (`Addr.words`).
- Of an entry only the name, the count, the spender and the mark `once` are read. Its owner
  (`owner`) and where the block begins among the owner's coins (`start`) are not compared: a part
  states neither.
- The jobs are values of `skeleton` (E2E/KeyTestSizes.lean): the place, the stages, the flag
  `ownMask`, the members and `fresh` are filled, and the three functions of a job are constants, so
  what a part's move computes there is of no use. By the definitions of `firstPart` and `restPart`,
  the names, the counts and the numbers of moves read nothing but the place, the stages, the members
  and `fresh`. The jobs' values are literals; their limits are in the head of E2E/KeyTestSizes.lean.
- The frame looks a part's count up in the table of the part's chain (`ProverCoinCounts.rowsOf`); `handedTo`
  looks it up in the three tables joined. That a row is in the table of its own chain is not tested
  here; it is the first test of `ProverCoinCounts.clauses`.
- The frame's other grounds for an error are not tested here: that a block lies within its owner's
  coins, that the book has no row and no entry for a further part at the place, and that the parts
  have as many moves as the sub-protocol has rounds. So `heldK12` does not say that the frame gives
  the parts their coins. `laysB` (Johnson/Desc/ProofFile/Honest/K12/StepsReturn.lean) tests these
  too; `full_lays` (StepsAtKey.lean, same folder) shows by evaluation in Lean's kernel that it is
  true at the book of the written sizes, for the ranges' test only, at the job `jobKR`.
- The parts' counts, names and numbers of moves come from E2E/KeyTestSizes.lean and, through it,
  from K12/Parts.lean, K12/Test.lean, K12/Coins.lean and ForKinds.lean under
  Johnson/Desc/ProofFile/Honest/. This file does not compile without these. If a count, a name, the
  order or a number of moves changes on one side only, the second test fails, and this file no
  longer compiles.
- The tests are evaluations by Lean's evaluator, at the one value `keyFull`. They prove nothing.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookAtWritten
import E2E.KeyTestSizes

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open ProofFile.Honest (Addr Ahead ProverCoinCounts Due Part dueAt)
open AtPublicFiles.KeyTest (allJobs part0 part1)

/-- What the book B has for the part at the address a, with the filters of `lendPart` (the frame):
the count of the first row at a in the three tables joined, 0 if there is none; the names and counts
of the entries whose spender is a and that are spent; the same for those that are carried. -/
def handedTo (B : ProverCoinCounts) (a : Addr) : Due × List (String × Due) × List (String × Due) :=
  let mine := B.ahead.filter fun e => e.spender == a
  (dueAt (B.first ++ B.shared ++ B.second) a, (mine.filter (·.once)).map Ahead.named,
    (mine.filter (!·.once)).map Ahead.named)

/-- What a part states: `takes`, `spends` and `carries`. -/
def statedBy (p : Part Unit Unit Unit) : Due × List (String × Due) × List (String × Due) :=
  (p.takes, p.spends, p.carries)

/-- The book B and the two parts agree at each of the four jobs: in what each part states, and in
the cut at the job's place. -/
def heldK12 (B : ProverCoinCounts) : Bool :=
  allJobs.all fun J =>
    statedBy (part0 J) == handedTo B ⟨J.p.place, 0⟩ &&
      statedBy (part1 J) == handedTo B ⟨J.p.place, 1⟩ &&
      B.cuts.lookup J.p.place == some [(part0 J).moves.length, (part1 J).moves.length]

#guard allJobs.map (·.p.place) == [rngPlace, foldedTestPlace, omegaTestPlace, ownTestPlace]
#guard atFull fun K => heldK12 (keyBook K)
-- it can fail: the book without its carried entries; the book with only these in reverse order
#guard atFull fun K => !heldK12 (keyBook K false)
#guard atFull fun K => !heldK12 { keyBook K with ahead := K.spent ++ K.carried.reverse }

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.handedTo
#print axioms AtPublicFiles.KeyBook.statedBy
#print axioms AtPublicFiles.KeyBook.heldK12

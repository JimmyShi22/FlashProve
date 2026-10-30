-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyTestSizes.lean: the public numbers of the key file's four proximity tests at the full size,
written out as literals, with tests on them and four theorems on the stages' sizes. Defined are the
four tests' lists of stages; for each test a job (`TestJob`,
Johnson/Desc/ProofFile/Honest/K12/Test.lean: what a caller says of its test) that holds public
numbers only; and the two parts of each test's prover (`firstPart`, `restPart`,
Johnson/Desc/ProofFile/Honest/K12/Parts.lean) at these jobs. The tests evaluate what the two parts
then state of coins, of ranges of coins and of rounds. The theorems say that in each list every
stage fits the next; they have no hypothesis. The full size is that of the sizes `keyFull`
(Johnson/Goal/PlanValues/KeySizedReturns.lean). The lines that begin with `#guard` are the tests:
Lean's evaluator runs them when the file is compiled, and the kernel does not check them.

Terms. A code (`Fmt.M1.Code`, Fmt/M1Codes.lean) has codewords of length 2^a, messages of l entries
and a tail of r random entries. A stage (`Fmt.M1.Stage`, Fmt/M1Types.lean) has the code C of a main
row, the code Z of a mask row, and k, h, t: tables of 2^k main rows and 2^h mask rows, and t
positions. A test's rounds are "BAT"; for each stage but the last a fold ("FOLD epsilon" and k
rounds) and a code switch into the next stage; and the base case. A fold's fresh table has 2^h mask
rows and holds the 2 k + 1 coefficients of the fold's hiding polynomial. The switch into the last
stage sends a masking word along with its oracle message: a main row and a mask row whose messages
and tails are all coins. A place (`Place`, Johnson/Desc/Block.lean) is a sub-protocol's label:
chain, link, piece, kind. The next three are types of the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest prover is written). An
address (`Addr`) is a place and the number of a part there. A count (`Due`) is a number of coins
(random field elements) of the base field and one of the extension field. A part (`Part`) is the
prover's side of some consecutive rounds of a sub-protocol. It states its own count (`takes`) and
the names and counts of the ranges of other parts' coins that it is given, as spent (`spends`) or as
carried (`carries`), and it has one move for each round (`moves`). A member (the field `members` of
a job) is an oracle message of the test's group: the address of the part that sent it, its number,
from 0, among the oracle messages that this part sends (its sending), and its count. The field
`fresh` names the first fold's fresh table by address and number in the same way; it is `none` where
the fold sends the table itself.

  `fit_ranges`, `fit_folded`, `fit_omega`, `fit_own`: in each of the four lists every stage fits the
    next: `FitAll` (Johnson/Desc/K12/Honest/Stages.lean), which is the library's `CsFit`
    (OnBytes/Slice/CsData.lean) at every code switch, at the stages in the form of `sgOf`
    (Johnson/Desc/K12/Law/ChainOf.lean: g := k - h). At a switch `CsFit` says: the new main table
    has as many entries as an old main row's message; the new mask table has room for two old mask
    rows' messages, an old main row's tail, two old mask rows' tails and the pad (one entry); the
    message lengths of the two new codes are powers of two; the old mask code's codewords are not
    longer than the old main code's
  `stagesRanges`, `stagesFolded`, `stagesOmega`, `stagesOwn`, `allStages`: definitions: the stages
    of the test on the group of the lookups' own message, on the folded row's group, on Omega's
    group and on the own group; the list of the four
  `skeleton place stages own members fresh`: a definition: the job that has this place, these
    stages, the flag own (`ownMask`: the first fold sends its own table), these members and this
    sender of the fresh table, and nothing else. The place's other numbers are those of `H2U.noP12`
    (Johnson/Desc/K12/AtPlan.lean): 0, false or an empty list. The three functions `rec₀`, `rows₀`,
    `trees₀` are constants: a state of defaults and zeros, rows of zeros, no tree
  `jobRanges`, `jobFolded`, `jobOmega`, `jobOwn`, `allJobs`: definitions: `skeleton` at the four
    tests' values; the list of the four
  `sIdx`, `sMsg`, `sW`, `sFolded`, `sOmega`: definitions: the addresses of the five parts that send
    the members: the index-mask message; the lookups' own message; W; the folded row; Omega with the
    split's mask message
  `part0 J`, `part1 J`: definitions: `firstPart J` ("BAT" and the first fold) and `restPart J` (all
    later rounds), with `Unit` for each of the three type parameters
  `packs l`: a definition: the test that in every stage of l but the last h + 2 (k - h) + 1 ≤ l',
    where l' is the mask code's message length: the fold's fresh table has room for the packing.
    Where this fails, the library's packing (`packedN`, Johnson/Prover/Link/BodyPack.lean) is the
    table of zeros

The tests. The stages in `keyFull`, taken through `H2U.stageNums`
(Johnson/Desc/K12/Plan/PlaceOfPlan.lean), are the four written lists; the places of the description
(the key file's IOP as written in Lean) take their stages from the sizes through the same function
(Johnson/Desc/Key/Ranges.lean, Places.lean). In each job `fresh` and `ownMask` agree
(`TestJob.freshFits`). The counts and marks of Johnson/Desc/ProofFile/Honest/K12/Coins.lean at the
four lists, and what the eight parts state, have the written values. `packs` is true at the four
lists.

By what. Each theorem splits `FitAll` into the five fields of `CsFit` at each switch and proves each
field by `decide`.

Where the jobs' values come from. None is computed here. The stages were copied from printed values
of the codes and notices at the full size (a notice is an oracle message as it is announced). The
members were read off the description's calls of `joinP`, by which an oracle message joins a group
(Johnson/Desc/Key/One.lean; K13/Text.lean, K14/Text.lean and Third/K14BatchLinearConstraintsSecondPart.lean under
Johnson/Desc/), and off the openings of the written rounds; they are listed in the order of sending.
The counts were reckoned from the notices: for each main row its tail; one coin for a pad in a main
row where the message has no mask row; for each mask row all its entries and its tail. The numbers
of rows in the docstrings are those of the library's written shapes (`shIdx`, `shMul`,
Johnson/Top/H/KeyRows.lean; `shW`, `shU`, `shO`, `shSp`, Johnson/Top/H/KeyFamilies.lean), which no
test here reads.

Limits.
- The jobs' values are literals. No theorem ties members, senders or counts to the description.
  E2E/KeyBookHeldK12.lean compares, by tests, the jobs' places and what the two parts state at these
  jobs (`takes`, `spends`, `carries`, the numbers of moves) with the key file's book of coins
  (`keyBook`, E2E/KeyBook.lean). A book (`ProverCoinCounts`) is the frame's public table of the parts' own
  counts, of the ranges that other parts are given, and of each sub-protocol's cut into parts.
  `keyBook` is written separately: it calls nothing of this file and no count of K12/Coins.lean. The
  names on both sides are made by `runName` and `carriedName`
  (Johnson/Desc/ProofFile/Honest/ForKinds.lean).
- In the place's numbers of a `skeleton` only the stages and the one flag are filled. Its oracle
  messages are the empty list, so its rounds with their oracle messages (`TestJob.laid`) are the
  empty list too. What a part's move computes at a skeleton is of no use. Only counts, names and
  numbers of moves are read here.
- The four theorems are on numbers. `FitAll` is a hypothesis of `stages_eq`
  (Johnson/Desc/K12/Honest/Stages.lean), `stages_yes_first` (Johnson/Desc/K12/Honest/FirstYes.lean),
  `stages_accept_body` and `stages_left_body` (Johnson/Prover/Link/BodyBehindFirst.lean). No other
  file calls the four theorems, and by themselves they state nothing on a prover.
- `CsFit` states the powers of two of the new stage, and of the old stage that the mask code is not
  the longer one. So `FitAll` does not state the former of a list's first stage, nor the latter of
  its last.
- The full size only.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Desc.K12.Plan.PlaceOfPlan

set_option autoImplicit false

namespace AtPublicFiles.KeyTest
open OnBytes.Slice
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open H2K.Pub (sgOf)
open ProofFile.Honest (Addr Due Part)
open ProofFile.Honest.K12

/-! ## 1 The stages -/

/-- The stages of the test on the group of the lookups' own message. -/
def stagesRanges : List Fmt.M1.Stage :=
  [⟨⟨22, 262144, 49⟩, ⟨16, 4096, 49⟩, 4, 4, 49⟩, ⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 4, 3, 39⟩,
   ⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 3, 33⟩, ⟨⟨20, 2048, 25⟩, ⟨20, 4096, 25⟩, 0, 0, 25⟩]
/-- The stages of the test on the folded row's group. -/
def stagesFolded : List Fmt.M1.Stage :=
  [⟨⟨24, 4194304, 97⟩, ⟨13, 64, 146⟩, 7, 0, 97⟩, ⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 5, 2, 52⟩,
   ⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 4, 2, 52⟩, ⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 4, 2, 52⟩,
   ⟨⟨14, 512, 49⟩, ⟨14, 1024, 49⟩, 0, 0, 49⟩]
/-- The stages of the test on Omega's group. -/
def stagesOmega : List Fmt.M1.Stage :=
  [⟨⟨22, 262144, 98⟩, ⟨13, 64, 146⟩, 4, 0, 49⟩, ⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 4, 3, 49⟩,
   ⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 4, 3, 49⟩, ⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩]
/-- The stages of the test on the own group. -/
def stagesOwn : List Fmt.M1.Stage :=
  [⟨⟨22, 262144, 98⟩, ⟨13, 256, 49⟩, 5, 1, 49⟩, ⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 4, 3, 49⟩,
   ⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 3, 49⟩, ⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 3, 41⟩,
   ⟨⟨15, 256, 29⟩, ⟨15, 256, 29⟩, 0, 0, 29⟩]

/-- The four lists of stages. -/
def allStages : List (List Fmt.M1.Stage) := [stagesRanges, stagesFolded, stagesOmega, stagesOwn]

-- the stages in the library's sizes `keyFull`, through `H2U.stageNums`, are the four written lists
#guard Lk6.AtPlan.keyFull.ranges.test.stages.map H2U.stageNums == stagesRanges
#guard Lk6.AtPlan.keyFull.once.folded.stages.map H2U.stageNums == stagesFolded
#guard Lk6.AtPlan.keyFull.once.omega.stages.map H2U.stageNums == stagesOmega
#guard Lk6.AtPlan.keyFull.once.own.stages.map H2U.stageNums == stagesOwn

/-! ## 2 The four jobs -/

/-- The job that holds public numbers only: a place, stages, the flag `ownMask`, members and the
fresh table's sender. Its three functions are constants. -/
def skeleton (place : Place) (stages : List Fmt.M1.Stage) (own : Bool)
    (members : List (Addr × ℕ × Due)) (fresh : Option (Addr × ℕ)) : TestJob Unit Unit where
  p := { H2U.noP12 place with
    nums := { (H2U.noP12 place).nums with stages := stages, ownMask := own } }
  members := members
  fresh := fresh
  rec₀ := fun _ _ =>
    { st := default, book := default, roots := 0, g := 0, pass := .nothing, mask := none }
  rows₀ := fun _ _ _ =>
    ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0,
      fun _ => 0⟩
  trees₀ := fun _ _ _ _ => []

/-- The address of the part that sends the index-mask message. -/
def sIdx : Addr := ⟨⟨1, none, 1, .K1⟩, 0⟩
/-- The address of the part that sends the lookups' own message. -/
def sMsg : Addr := ⟨⟨1, none, 2, .K1⟩, 0⟩
/-- The address of the part that sends W. -/
def sW : Addr := ⟨⟨1, none, 14, .K1⟩, 0⟩
/-- The address of the part that sends the folded row. -/
def sFolded : Addr := ⟨⟨2, none, 2, .K1⟩, 0⟩
/-- The address of the part that sends Omega and the split's mask message. -/
def sOmega : Addr := ⟨⟨2, none, 5, .K1⟩, 0⟩

/-- The job of the test on the group of the lookups' own message. One member, that message: 2 main
rows over the base field (tails: 2 · 49 coins of the base field) and 9 mask rows (9 · 4096 entries,
9 · 49 coins of tails). The fresh table is sent along with it, as message 1 of the same sending. -/
def jobRanges : TestJob Unit Unit :=
  skeleton ⟨1, none, 5, .K12⟩ stagesRanges false [(sMsg, 0, ⟨98, 36864 + 441⟩)] (some (sMsg, 1))

/-- The job of the test on the folded row's group. Two members. The folded row: 107 main rows
(tails: 107 · 97 coins) and its pad in a main row (1 coin). The split's mask message: one mask row
(64 entries, a tail of 146). The fresh table is sent along with the folded row, as message 1 of the
same sending. -/
def jobFolded : TestJob Unit Unit :=
  skeleton ⟨2, none, 9, .K12⟩ stagesFolded false
    [(sFolded, 0, ⟨0, 10379 + 1⟩), (sOmega, 1, ⟨0, 64 + 146⟩)] (some (sFolded, 1))

/-- The job of the test on Omega's group. Two members. Omega: 12 main rows (tails: 12 · 98 coins)
and its pad in a main row (1 coin). The split's mask message, as in `jobFolded`. The first fold
sends its own fresh table. -/
def jobOmega : TestJob Unit Unit :=
  skeleton ⟨2, none, 10, .K12⟩ stagesOmega true
    [(sOmega, 0, ⟨0, 1176 + 1⟩), (sOmega, 1, ⟨0, 64 + 146⟩)] none

/-- The job of the test on the own group. Three members. The index-mask message: one mask row (256
entries, a tail of 49). W: one main row (a tail of 98) and one mask row (256 entries, a tail of 49).
Omega, as in `jobOmega`. The fresh table is sent along with W, as message 1 of the same sending. -/
def jobOwn : TestJob Unit Unit :=
  skeleton ⟨3, none, 2, .K12⟩ stagesOwn false
    [(sIdx, 0, ⟨0, 256 + 49⟩), (sW, 0, ⟨0, 98 + 256 + 49⟩), (sOmega, 0, ⟨0, 1176 + 1⟩)]
    (some (sW, 1))

/-- The four jobs. -/
def allJobs : List (TestJob Unit Unit) := [jobRanges, jobFolded, jobOmega, jobOwn]

/-- The first part of a job's test: "BAT" and the first fold. -/
def part0 (J : TestJob Unit Unit) : Part Unit Unit Unit := firstPart J
/-- The second part of a job's test: all later rounds. -/
def part1 (J : TestJob Unit Unit) : Part Unit Unit Unit := restPart J

/-! ## 3 Tests on counts -/

#guard allJobs.all (·.freshFits)

-- counts: all switches' coins (the second part's own); the first fresh table's; the masking word's
#guard allStages.map dueRest == [22273, 7912, 5698, 5046]
#guard allStages.map (fun l => dueFresh (l.headD default)) == [9 + 784, 15 + 146, 9 + 146, 11 + 98]
#guard allStages.map (fun l => dueWord (l.getLastD default)) == [6194, 1634, 1614, 570]
-- `marksAt`: the masking word's range ends where `dueRest` ends; the first coins of three switches
#guard allStages.all fun l =>
  (marksAt l (l.length - 2)).ride + dueWord (l.getLastD default) == dueRest l
#guard (marksAt stagesRanges 0).main == 0 && (marksAt stagesRanges 1).main == 9302 &&
  (marksAt stagesRanges 2).main == 9302 + 4778
-- negative test: with the second stage's main tail at 38 in place of 39 the count changes
#guard dueRest (stagesRanges.modify 1 fun s => { s with C := { s.C with r := 38 } }) != 22273
-- what the parts state: own counts; the counts spent; how many ranges are carried; how many moves
#guard allJobs.map (fun J => ((part0 J).takes, (part1 J).takes)) ==
  [(⟨0, 0⟩, ⟨0, 22273⟩), (⟨0, 0⟩, ⟨0, 7912⟩), (⟨0, 155⟩, ⟨0, 5698⟩), (⟨0, 0⟩, ⟨0, 5046⟩)]
#guard allJobs.map (fun J => (part0 J).spends.map (·.2)) == [[⟨0, 9⟩], [⟨0, 15⟩], [], [⟨0, 11⟩]]
#guard allJobs.map (fun J => ((part0 J).carries.length, (part1 J).carries.length)) ==
  [(1, 2), (2, 3), (2, 3), (3, 4)]
#guard allJobs.map (fun J => [(part0 J).moves.length, (part1 J).moves.length]) ==
  [[6, 17], [9, 26], [6, 18], [7, 23]]
-- the name of a range that is spent and the names of three that are carried, written out
#guard (part0 jobRanges).spends.map (·.1) == ["the fold's fresh mask to 1.-.5.0: fold"]
#guard (part1 jobOmega).carries.map (·.1) ==
  ["message 0 of 2.-.5.0 to 2.-.10.1: carried", "message 1 of 2.-.5.0 to 2.-.10.1: carried",
    "message 0 of 2.-.10.0 to 2.-.10.1: carried"]

/-! ## 4 The stages fit -/

/-- The fresh table of each fold has room for the packing (`packedN`): in every stage but the last,
h + 2 (k - h) + 1 is at most the mask code's message length. -/
def packs (l : List Fmt.M1.Stage) : Bool :=
  l.dropLast.all fun s => decide ((sgOf s).h + 2 * (sgOf s).g + 1 ≤ (sgOf s).Z.l)

#guard allStages.all packs

theorem fit_ranges : FitAll (stagesRanges.headD default) stagesRanges.tail := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, trivial⟩ <;> decide

theorem fit_folded : FitAll (stagesFolded.headD default) stagesFolded.tail := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    trivial⟩ <;> decide

theorem fit_omega : FitAll (stagesOmega.headD default) stagesOmega.tail := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, trivial⟩ <;> decide

theorem fit_own : FitAll (stagesOwn.headD default) stagesOwn.tail := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    trivial⟩ <;> decide

end AtPublicFiles.KeyTest

#print axioms AtPublicFiles.KeyTest.fit_ranges
#print axioms AtPublicFiles.KeyTest.fit_folded
#print axioms AtPublicFiles.KeyTest.fit_omega
#print axioms AtPublicFiles.KeyTest.fit_own
#print axioms AtPublicFiles.KeyTest.stagesRanges
#print axioms AtPublicFiles.KeyTest.stagesFolded
#print axioms AtPublicFiles.KeyTest.stagesOmega
#print axioms AtPublicFiles.KeyTest.stagesOwn
#print axioms AtPublicFiles.KeyTest.allStages
#print axioms AtPublicFiles.KeyTest.skeleton
#print axioms AtPublicFiles.KeyTest.sIdx
#print axioms AtPublicFiles.KeyTest.sMsg
#print axioms AtPublicFiles.KeyTest.sW
#print axioms AtPublicFiles.KeyTest.sFolded
#print axioms AtPublicFiles.KeyTest.sOmega
#print axioms AtPublicFiles.KeyTest.jobRanges
#print axioms AtPublicFiles.KeyTest.jobFolded
#print axioms AtPublicFiles.KeyTest.jobOmega
#print axioms AtPublicFiles.KeyTest.jobOwn
#print axioms AtPublicFiles.KeyTest.allJobs
#print axioms AtPublicFiles.KeyTest.part0
#print axioms AtPublicFiles.KeyTest.part1
#print axioms AtPublicFiles.KeyTest.packs

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/TestToyShapes.lean: tests of OnBytes/Plan/ToyShapes.lean. They run when this file
compiles.

The C++ tools blocks/frame/handover_files.cpp and handover_proof.cpp make a toy's key, entry and
proof files, and write beside them the toy's two public files and the parameter bytes of every
chain. Here the chains' parameter bytes are derived from three pairs of public files and compared,
by length and digest, with those that the tools wrote: four chains for the first pair (its tool
makes no proof), seven for the second, and seven for the third, whose one link names arrays. The
public files are spelled out; TestKeyOneTime.toyFile says on which lines of the tools they hang.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Plan.ToyShapes
import OnBytes.Plan.TestKeyOneTime

namespace OnBytes.Plan.TestToyShapes

open OnBytes.Params

/-- The length and the digest of parameter bytes. -/
def fact (b : ByteArray) : Nat × String := (b.size, Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm b))

/-- The parameter file of the second pair: the first pair's with two lines changed. -/
def secondFile : List String :=
  TestKeyOneTime.toyFile.map fun l =>
    if l == "slots 2" then "slots 4"
    else if l == "group link 1 13 9 13 5" then "group link 1 13 9 13 6" else l

#guard secondFile != TestKeyOneTime.toyFile

/-- The facts of a key's three chains and of an entry's chain. -/
def committers (c : Configured) : List (Nat × String) :=
  [fact c.keyOneTime, fact c.keyShared, fact c.keySecond, fact c.entryLink]

/-- The facts of a proof's three chains. -/
def provers (c : Configured) : List (Nat × String) := [fact c.first, fact c.shared, fact c.second]

#guard ((toyConfigure toyShapes (TestFile.fileOf TestKeyOneTime.toyFile)
    TestKeyOneTime.toyShapes.toUTF8).toOption.map committers) == some [
  (76647, "37d50efc5a1d3a11ec7e86353f53e9fe8c644210ea14f275a080e39a59ef88ff"),
  (4982, "bb25514f624c19c02f286e5cf11ad5bac682819b60243d913acf7573438ea1b1"),
  (1521, "b37528e31370674d3b996313a062c619806ea1037a2a92ec94c5af194299f735"),
  (2648, "2c73aaba13e5b95b2e4ffc7f4b442858638a59b4b3f30eadd357edcdbf49cb35")]

#guard ((toyConfigure seamShapes (TestFile.fileOf secondFile)
    "links 3\npending 3\nmatrix 100\nidentifiers 1 2 3\n".toUTF8).toOption.map fun c =>
      committers c ++ provers c) == some [
  (76647, "0db7bd6f73bd1cf163b97f75876ad197ba440c617d02561e5737ac5e0fcc7e17"),
  (4982, "59f70db6286208db03e108c10e3a23f94cd246fdc74b1a81eec37f4cb4d7a89b"),
  (1521, "f507364d49b24538fa275ff13421bb349cf399f1f6a571d9ee53de550c06770a"),
  (2648, "8e1e18123000c8824af595c59aaafaafc293f0888ba6d43588b5a1c508c5593d"),
  (13685, "850751621b7332efab70a79d659a44c0f578d4abed9c40ce420fdb6ab76657cb"),
  (4982, "827bc8400b6701e7166445f557deb7d03ec79551dbb41a08bad2c35d48878117"),
  (1521, "04bbcb6fb2eafb5a2c363bd667fbeb62bbf8deb72712a3038190109ef75ebf28")]

#guard ((toyConfigure seamShapes (TestFile.fileOf secondFile)
    "links 1\npending 1\nmatrix 100\nidentifiers 1\narrays\n".toUTF8).toOption.map fun c =>
      committers c ++ provers c) == some [
  (76647, "3061dc96b51e0ce296ffbca802ad6c81a056d063b5cb60e01dc1d87fedc0b56a"),
  (4982, "4dfcf9236033aed38440da0c705a1fecef3f48ee399ffe64b82aa6c53ac615fe"),
  (1521, "86461eaea71163895b7a53ce84d66470f4a8680f3edece985b5c1c1a23ffe08a"),
  (2648, "365fa8dd385037f68744d06699edd980f397abfc6bbd89626d164e01cbc93baa"),
  (7033, "2df86d6084b0fe2131618fde5d8e4343248a4a3353d312b9d7b09b5c70512119"),
  (4982, "b86c3a2e91560810fa530a1765d05e00ca314c5fbf7068830ec5ea08bbe3b4dd"),
  (1415, "3675d4851990b297ce9f1d2e95d1e90187a903d2cbc68e3c8e16adc7f8d33847")]

-- where both readings admit a pair of files, they give the same chains of key and entry
#guard ((toyConfigure toyShapes (TestFile.fileOf secondFile)
    "links 3\npending 3\nmatrix 100\nidentifiers 1 2 3\n".toUTF8).toOption.map committers) ==
  ((toyConfigure seamShapes (TestFile.fileOf secondFile)
    "links 3\npending 3\nmatrix 100\nidentifiers 1 2 3\n".toUTF8).toOption.map committers)
-- the first pair is admitted by one reading alone, and the routine for committers finds it
#guard (toyConfigure seamShapes (TestFile.fileOf TestKeyOneTime.toyFile)
    TestKeyOneTime.toyShapes.toUTF8).toOption.isNone
#guard ((toyForCommitters (TestFile.fileOf TestKeyOneTime.toyFile)
    TestKeyOneTime.toyShapes.toUTF8).toOption.map fun c => fact c.keyOneTime) ==
  some (76647, "37d50efc5a1d3a11ec7e86353f53e9fe8c644210ea14f275a080e39a59ef88ff")

#guard readToyModel "links 3\npending 2\nmatrix 100\nidentifiers 1 2 3\n".toUTF8 ==
  some (3, 2, 100, [1, 2, 3], [])
#guard readToyModel "links3 pending  2matrix\n100 identifiers 7 x 8".toUTF8 ==
  some (3, 2, 100, [7], "x 8".toUTF8.toList)
/-- What the C library's formatted scan gave for the three numbers on some texts, in a run of that
one call by itself (g++ 13.3, glibc 2.39): the text, and the numbers if the call read all three and
reached the end of the word "identifiers". -/
def scanCases : List (String × Option (Nat × Nat × Nat)) := [
  ("links 3\npending 2\nmatrix 100\nidentifiers 1 2 3\n", some (3, 2, 100)),
  ("links3 pending  2matrix\n100 identifiers 7", some (3, 2, 100)),
  (" links 3\npending 2\nmatrix 100\nidentifiers", none),
  ("links 3\npending 2\nmatrix 100\n", none),
  ("links 4294967299\npending -1\nmatrix +007\nidentifiers", some (3, 4294967295, 7)),
  ("links 99999999999999999999999\npending 18446744073709551617\nmatrix 100\nidentifiers",
    some (4294967295, 4294967295, 100)),
  ("links -\npending 2\nmatrix 100\nidentifiers", none),
  ("links 3\npending 2\nmatrix 100identifiers", some (3, 2, 100)),
  ("links 3\npending 2\nmatrix 100\nidentifierz", none)]

#guard scanCases.all fun c =>
  (readToyModel c.1.toUTF8).map (fun x => (x.1, x.2.1, x.2.2.1)) == c.2

/-- What the C++ loop that reads the identifiers and then the words gave on some texts, in a run of
that loop by itself, compiled by g++ 13.3 with its own library: the text, the numbers, the
words. -/
def streamCases : List (String × List Nat × List String) := [
  (" 1 2 3 99999999999999999999999 arrays", [1, 2, 3], ["arrays"]),
  (" 1 -arrays", [1], ["arrays"]),
  (" 1 - arrays", [1], ["arrays"]),
  (" -1 +2", [18446744073709551615, 2], []),
  (" 1 +", [1], []),
  (" 7 x 8", [7], ["x", "8"]),
  (" 12abc", [12], ["abc"]),
  (" 1 18446744073709551615 18446744073709551616 later", [1, 18446744073709551615], ["later"]),
  (" 1 -18446744073709551616 class", [1], ["class"]),
  (" 007 0x10", [7, 0], ["x10"]),
  ("", [], [])]

#guard streamCases.all fun c =>
  let x := numbersFrom c.1.length c.1.toUTF8.toList
  x.1 == c.2.1 && wordsOf x.2 == c.2.2.map (·.toUTF8.toList)

-- very many identifiers: the reading is a loop
#guard (numbersFrom 400000 ((List.replicate 200000 [32, 55]).flatten)).1.length == 200000

-- a number of 2^64 or more, and a sign alone, end the identifiers and are passed over
#guard readToyModel
    "links 3\npending 3\nmatrix 100\nidentifiers 1 2 3 99999999999999999999999 arrays".toUTF8 ==
  some (3, 3, 100, [1, 2, 3], " arrays".toUTF8.toList)
#guard readToyModel "links 1\npending 1\nmatrix 100\nidentifiers 1 -arrays".toUTF8 ==
  some (1, 1, 100, [1], "arrays".toUTF8.toList)
#guard readToyModel "links 1\npending 1\nmatrix 100\nidentifiers -1 +2".toUTF8 ==
  some (1, 1, 100, [2 ^ 64 - 1, 2], [])
#guard TestFile.smallLines.any fun l => (seamShapes l ByteArray.empty
  "links 1\npending 1\nmatrix 100\nidentifiers 1 99999999999999999999999 arrays\n".toUTF8).isSome
-- another word after the identifiers, or a word twice
#guard TestFile.smallLines.any fun l => (seamShapes l ByteArray.empty
  "links 1\npending 1\nmatrix 100\nidentifiers 1\narrays\nother\n".toUTF8).isNone
#guard TestFile.smallLines.any fun l => (seamShapes l ByteArray.empty
  "links 1\npending 1\nmatrix 100\nidentifiers 1\narrays\narrays\n".toUTF8).isNone
#guard TestFile.smallLines.any fun l => (seamShapes l ByteArray.empty
  "links 1\npending 1\nmatrix 100\nidentifiers 1\nlater class\n".toUTF8).isSome

end OnBytes.Plan.TestToyShapes

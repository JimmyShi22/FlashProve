-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/TestWhole.lean: tests of how the program reads its arguments, of the lines that it
prints for a result, and of the limits on the lengths of files. The tests try examples and prove
nothing about other inputs. All values are made up by hand and come from no file: `id64` is a
pattern of hex digits, 999999999999999999 and 10^18 are the border of `num`, and 4294967276 and the
like are 2^32 less an error code of the operating system. The program does not import this file.
-/
import OnBytes.Shell.Call
import OnBytes.Model.TestStages

namespace OnBytes.ShellTest

open OnBytes.Shell

-- numbers on the command line
#guard decimal 256 "0" == some 0 && decimal 256 "256" == some 256 && decimal 256 "257" == none
#guard decimal 1000000 "1000000" == some 1000000 && decimal 1000000 "1000001" == none
#guard decimal 256 "" == none && decimal 256 "01" == none && decimal 256 "+1" == none
#guard decimal 256 " 1" == none && decimal 256 "1 " == none && decimal 256 "1.0" == none
#guard decimal 100000000 "12345678" == none && decimal 256 "0x10" == none

/-- 64 hex digits, made up, in the place of an ID. -/
def id64 : String := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"

#guard isId id64 && isId id64.toUpper && !isId (id64.drop 1).toString && !isId (id64 ++ "0")
#guard !isId ((id64.drop 1).toString ++ "g")

/-- 0 if the options are taken, 1 for wrong usage, 2 for a malformed ID, 3 for a malformed
policy. -/
def code (l : List String) : Nat :=
  match readOptions l {} with
  | .ok _ => 0
  | .error .usage => 1
  | .error .idForm => 2
  | .error .policyForm => 3

#guard code [] == 0 && code ["-id", id64] == 0 && code ["-id", id64, "-id", id64] == 1
#guard code ["-id"] == 1 && code ["-id", "12"] == 2 && code ["-x"] == 1 && code ["x"] == 1
#guard code ["-bits", "128"] == 0 && code ["-bits", "128", "-bits", "128"] == 1
#guard code ["-bits", "0128"] == 1 && code ["-bits"] == 1 && code ["-bits", "1000001"] == 1
#guard code ["-j", "4"] == 0 && code ["-j", "0"] == 1 && code ["-j", "257"] == 1
#guard code ["-j", "4", "-j", "4"] == 1 && code ["-q", "-q", "-next-token", "-next-token"] == 0
#guard code ["-policy", "exact-match,256,256,0,15,8"] == 0 && code ["-policy", "x"] == 3
#guard code ["-policy", "exact-match,256,256,0,15,8", "-policy", "exact-match,256,256,0,15,8"] == 1

/-- What the options hold, if they are taken. -/
def asked (l : List String) : Option Asked := (readOptions l {}).toOption

#guard (asked ["-bits", "96", "-id", id64, "-next-token"]).any fun a =>
  a.options.bits == 96 && a.options.id == some id64 && a.options.nextToken
#guard (asked []).any fun a =>
  a.options.bits == 128 && a.options.id == none && !a.options.nextToken &&
    !a.options.noProofOfWork
#guard (asked ["-no-proof-of-work"]).any (·.options.noProofOfWork)
#guard (asked ["-q", "-no-proof-of-work", "-bits", "128", "-no-proof-of-work"]).any
  (·.options.noProofOfWork)
#guard code ["-no-proof-of-work", "x"] == 1 && code ["-no-work"] == 1
#guard code ["-bits", "-no-proof-of-work"] == 1 && code ["-id", "-no-proof-of-work"] == 2

/-- 0 for a call on test files, 1 for a whole call, 2 for a bad command line, 3 for a planning
call, 4 and 5 for a call on a key file and on an entry file alone. -/
def kind (l : List String) : Nat :=
  match kindOf l with
  | .toy .. => 0
  | .whole .. => 1
  | .bad _ => 2
  | .plan .. => 3
  | .keyPart .. => 4
  | .leafPart .. => 5

#guard kind [] == 2 && kind ["product", "a", "b"] == 0 && kind ["product", "a"] == 2
#guard kind ["key", "a", "b", "c"] == 0 && kind ["verify", "a", "b", "c", "d"] == 2
#guard kind ["key", "a", "b", "c", "-bits", "10"] == 0
#guard kind ["key", "a", "b", "c", "-bits", "x"] == 2
#guard kind ["key", "a", "b", "c", "d"] == 2 && kind ["product", "a", "b", "-bits", "10"] == 0
#guard cutBits ["a", "-bits", "10"] == some (["a"], 10) && cutBits ["a"] == some (["a"], 128)
#guard cutBits ["a", "-bits", "010"] == none && cutBits ["-bits"] == some (["-bits"], 128)
#guard (bitsNote 10).map Note.text == ["the bits asked in this call: 10"] && (bitsNote 128).isEmpty
#guard code ["-show-stages"] == 0 && code ["-show-stages", "-show-stages", "-q"] == 0
#guard kind ["verify", "a", "b", "c", "d", "e"] == 1
#guard kind ["verify", "a", "b", "c", "d", "e", "f"] == 2
#guard kind ["a", "b", "c", "d", "e"] == 2
#guard kind ["verify", "-key", "a", "b"] == 4 && kind ["verify", "-key", "a"] == 2
#guard kind ["verify", "-key", "a", "b", "-bits", "128", "-q"] == 4
#guard kind ["verify", "-key", "a", "b", "-next-token"] == 2
#guard kind ["verify", "-leaf", "a", "b", "c"] == 5 && kind ["verify", "-leaf", "a", "b"] == 2
#guard kind ["verify", "-leaf", "a", "b", "c", "-policy", "exact-match,256,256,0,15,8"] == 2
#guard kind ["plan", "a"] == 3 && kind ["plan", "a", "-bits", "96"] == 3 && kind ["plan"] == 2
#guard kind ["plan", "a", "-bits", "096"] == 2 && kind ["plan", "a", "-q"] == 2
/-- Whether a call hands `-no-proof-of-work` on to the checks. Nothing for a call without such
options. -/
def refusesWork (l : List String) : Option Bool :=
  match kindOf l with
  | .whole _ _ _ _ _ a => some a.options.noProofOfWork
  | .keyPart _ _ a => some a.options.noProofOfWork
  | .leafPart _ _ _ a => some a.options.noProofOfWork
  | _ => none

-- a whole call and both calls on one file alone take -no-proof-of-work, behind the paths, and hand
-- it on; of the other calls plan and product are tried: they do not take it
#guard refusesWork ["verify", "a", "b", "c", "d", "e", "-no-proof-of-work"] == some true
#guard refusesWork ["verify", "-key", "a", "b", "-no-proof-of-work"] == some true
#guard refusesWork ["verify", "-leaf", "a", "b", "c", "-no-proof-of-work"] == some true
#guard refusesWork ["verify", "a", "b", "c", "d", "e"] == some false
#guard refusesWork ["verify", "-key", "a", "b"] == some false
#guard refusesWork ["verify", "-leaf", "a", "b", "c"] == some false
#guard kind ["verify", "-no-proof-of-work", "a", "b", "c", "d", "e"] == 2
#guard kind ["plan", "a", "-no-proof-of-work"] == 2
#guard kind ["product", "a", "b", "-no-proof-of-work"] == 2

/-- Lists for the tests. -/
def L0 : Lists := ⟨ownNames ++ ["model-statement", "policy"], ["key: CS"]⟩

/-- cp_verify's clause on a record, copied from RECORDCLAUSE (verifier/src/vf_common.h), not from
OnBytes/Shell/Lines.lean. -/
def clause61 : String :=
  "; the table has a record: the binding of the weights rests on the theorem on codes " ++
    "(ePrint 2025/2055, Theorem 4.6), taken as given"

/-- What a result is about, for the tests. -/
def a0 : Model.Stages.Covered := ⟨63, 64, 64, 256, 256, 0, 15, 8, 4, 24, 0, .exactMatch⟩

/-- Closing values for the tests. -/
def c0 : Model.Stages.Closing :=
  { idHex := some id64, idNamed := true, hPar := id64, stageWork := [], work := none,
    leastRound := 12800, leastWithoutWork := 12800, oneTimeAssumed := 0 }

/-- All lines of a result. -/
def linesOf (e : Model.Stages.CallEnd) : List String :=
  (before { bits := 128, leaf := 0 } e ++ [verdict {} e]).map (Line.text L0)

#guard (Line.no "reader").text L0 == "NO: reader"
#guard (Line.no "a name from a file").text L0 == "NO: unlisted-check"
#guard (Line.notChecked "x y").text L0 == "NOT CHECKED: unlisted-check"
#guard (Line.hPar "x y").text L0 == "h_par=not-a-digest"
#guard (Line.hPar id64.toUpper).text L0 == "h_par=not-a-digest"
#guard num 999999999999999999 == "999999999999999999" && num 1000000000000000000 == "out-of-range"
#guard cents 9602 == "96.02" && cents 5 == "0.05" && cents 1000000000000000000 == "out-of-range"
#guard ((Line.covered a0).text L0).startsWith
  ("covered: r=63 e=64 T=64 C=256 theta=256 cap=0 s=15 sh=8 positions=63..63 tokens=none y=yes " ++
   "next-token=yes policy=exact-match above-clip=0 (places in the request, counted from 0;")
#guard (Line.work (some ⟨32, 38, 12802⟩) 9602).text L0 ==
  "proof of work: up to 32 bits counted in 38 rounds; with it the least round has 128.02 bits, " ++
    "without it 96.02 bits"
#guard (Line.work (some ⟨32, 1, 12802⟩) 9602).text L0 ==
  "proof of work: up to 32 bits counted in 1 round; with it the least round has 128.02 bits, " ++
    "without it 96.02 bits"
#guard (Line.work none 12800).text L0 == "proof of work: none counted"
#guard (Line.stageWork .key ⟨9602, 32, "key: CS"⟩).text L0 ==
  "stage key: work: 96.02 + 32 (one round's error without its work, in bits, + its bits of " ++
    "work; key: CS)"
#guard (Line.stageWork .key ⟨9602, 32, "x"⟩).text L0 ==
  "stage key: work: 96.02 + 32 (one round's error without its work, in bits, + its bits of " ++
    "work; unlisted-place)"
#guard (Line.unreadable .proof .noSuch).text L0 ==
  "input-unreadable-proof: the proof file cannot be read: No such file or directory"
#guard (Line.unreadable .KL (Unread.ofCode 13)).text L0 ==
  "input-unreadable-KL: KL.bin cannot be read: Permission denied"
#guard [2, 13, 20, 40, 36, 24, 5, 1].map Unread.ofCode ==
  [.noSuch, .denied, .notDirectory, .loop, .nameTooLong, .tooManyOpen, .device, .other]
#guard [4294967276, 4294967256, 4294967260, 4294967294].map Unread.ofCode ==
  [.notDirectory, .loop, .nameTooLong, .noSuch]
#guard (Line.withinLimits { a0 with policy := .clippedGap, C := 100000, theta := 40000 }).text L0 ==
  "WITHIN LIMITS: clipped-gap C=100000 theta=40000 cap=0 s=15 sh=8"
#guard (linesOf (.yes a0 c0)).length == 10 && (linesOf (.yes a0 c0)).getLast? == some "YES"
#guard ((linesOf (.yes a0 c0)).drop 6).take 3 ==
  ["commitment: every closeness round of the one-time files rests on the proved lemma" ++ clause61,
   "proof of work: none counted",
   "result-v1 status=0 claim=next-token id=" ++ id64 ++ " bits=128 work=0 work-rounds=0 " ++
   "least-round=128.00 least-round-without-work=128.00 commitment-assumed-rounds=0 record=1 " ++
   "r=63 e=64 T=64 tokens=none y=yes policy=exact-match C=256 theta=256 cap=0 s=15 sh=8 sT=4 F=24 " ++
   "above-clip=0 leaf=0 stages=key,leaf,request dw=8 build=lean-verify-on-bytes"]

/-- Closing values in which work is counted, so that the two least rounds differ. -/
def c1 : Model.Stages.Closing :=
  { c0 with work := some ⟨30, 7, 12803⟩, leastRound := 12803, leastWithoutWork := 9855 }

/-- The line on work for `c1`. -/
def work1 : String :=
  "proof of work: up to 30 bits counted in 7 rounds; with it the least round has 128.03 bits, " ++
    "without it 98.55 bits"

-- in a whole call and in a call on one file alone the line on work has the number without work,
-- which the line for programs has as least-round-without-work
#guard [.yes a0 c1, .withinLimits a0 c1, .notVer [] (some a0) c1].all
  fun (e : Model.Stages.CallEnd) => ((linesOf e).drop 7).head? == some work1
#guard ((linesOf (.partPassed .key c1)).drop 4).head? == some work1
#guard ((linesOf (.notVer [] none c1)).drop 4).head? == some work1
#guard ((linesOf (.partPassed .leaf c1)).drop 5).head? == some work1
#guard ((linesOf (.yes a0 c1)).drop 8).head?.any fun l =>
  (l.splitOn " work=30 work-rounds=7 least-round=128.03 least-round-without-work=98.55 ").length
    == 2
-- the call's own cause: cp_verify's sentence; this program prints it directly behind the heading; a
-- stage's cause is not printed; a result that is a verification has none
#guard (Line.callCause .idNamed).text L0 ==
  "the call: not the standard parameter form: id-named (the call named no ID: add -id with " ++
    "the commitment ID)"
#guard ((linesOf (.notVer ["stage key: fewer-bits-requested", "id-named"] (some a0)
    { c0 with idHex := none, idNamed := false })).take 4) ==
  ["---- the call ----", (Line.callCause .idNamed).text L0, "commitment ID: not-shown-without-id",
   "id: not compared: the call named none"]
#guard (linesOf (.notVer ["stage key: fewer-bits-requested"] (some a0) c0)).take 2 ==
  ["---- the call ----", "commitment ID: " ++ id64]
#guard (linesOf (.notVer ["stage key: id-named"] none c0)).take 2 ==
  ["---- the call ----", "id: named by the caller and equal"]
#guard ((closingPart [.idNamed] false c0).map (Line.text L0)).take 3 ==
  ["---- the call ----", (Line.callCause .idNamed).text L0, "id: named by the caller and equal"]
-- a call on one file alone that named no ID and is not refused says that none was compared
#guard [.partPassed .key, .partPassed .leaf, .notVer [] none].all
  fun (e : Model.Stages.Closing → Model.Stages.CallEnd) =>
    (linesOf (e { c0 with idNamed := false })).take 2 ==
      ["---- the call ----", "id: not compared: the call named none"]
-- the number of closeness rounds that rest on another source stands in both lines that show it
#guard [.yes a0, .notVer [] (some a0)].all
  fun (e : Model.Stages.Closing → Model.Stages.CallEnd) =>
    let ls := linesOf (e { c0 with oneTimeAssumed := 3 })
    ls.contains ("commitment: 3 closeness rounds of the one-time files rest on another source " ++
      "than the proved lemma" ++ clause61) &&
    ls.any fun l => (l.splitOn " commitment-assumed-rounds=3 ").length == 2
-- both lines that show it say that the table has a record, whatever the verdict.
-- The field's place is cp_verify's: right behind commitment-assumed-rounds= (cp_verify.cpp,
-- resultLine)
#guard [.yes a0, .withinLimits a0, .notVer [] (some a0)].all
  fun (e : Model.Stages.Closing → Model.Stages.CallEnd) =>
    let ls := linesOf (e { c0 with oneTimeAssumed := 2, tableRecord := true })
    ls.contains ("commitment: 2 closeness rounds of the one-time files rest on another source " ++
      "than the proved lemma" ++ clause61) &&
    ls.any fun l => (l.splitOn " commitment-assumed-rounds=2 record=1 r=63 ").length == 2
#guard !(linesOf (.yes a0 c0)).any (·.startsWith "the call:")
#guard (Line.callCause (.noProofOfWork 74)).text L0 ==
  "the call: not the standard parameter form: no-proof-of-work (the call had -no-proof-of-work, " ++
    "and 74 rounds meet the parameter file's target only with proof of work counted)"
#guard (Line.callCause (.noProofOfWork 1)).text L0 ==
  "the call: not the standard parameter form: no-proof-of-work (the call had -no-proof-of-work, " ++
    "and 1 round meets the parameter file's target only with proof of work counted)"
-- both causes, in cp_verify's order, whatever the order of the short names; the number of rounds is
-- that of the line on work
#guard ((linesOf (.notVer ["no-proof-of-work", "id-named"] (some a0) c1)).take 3) ==
  ["---- the call ----", (Line.callCause .idNamed).text L0,
   (Line.callCause (.noProofOfWork 7)).text L0]
#guard ((linesOf (.notVer ["no-proof-of-work"] none c1)).take 3) ==
  ["---- the call ----", (Line.callCause (.noProofOfWork 7)).text L0,
   "id: named by the caller and equal"]
#guard ((linesOf (.notVer ["no-proof-of-work"] (some a0) c1)).drop 8).take 4 ==
  [work1] ++ ((linesOf (.notVer [] (some a0) c1)).drop 8).take 1 ++ ["NOT-A-VERIFICATION"]
#guard ((linesOf (.notVer ["no-proof-of-work"] (some a0) c1)).drop 9).head?.any fun l =>
  l.startsWith "result-v1 status=14 " && (l.splitOn " work-rounds=7 ").length == 2
#guard callCauses ["no-proof-of-work"] c0 == [.noProofOfWork 0]
#guard ((Line.callCause (.noProofOfWork 0)).text L0).endsWith
  "and 0 rounds meet the parameter file's target only with proof of work counted)"
#guard callCauses ["stage key: no-proof-of-work"] c1 == []
-- the short names that `cpStagesRun` gives are those that `callCauses` takes: three made-up stages
-- that passed with work, 38 rounds in the call's record; no ID named; the option
#guard ((linesOf (Model.Stages.cpStagesRun Model.Stages.allWorked none false 128
    { noProofOfWork := true } Model.Stages.next)).take 3) ==
  ["---- the call ----", (Line.callCause .idNamed).text L0,
   (Line.callCause (.noProofOfWork 38)).text L0]
-- a bad command line from the checks: a fixed line on standard error, not the result's words
#guard match finish L0 {} (.usage "x") with
  | .err w (.done .fault) => w == "verify-on-bytes: bad command line"
  | _ => false

/-- The rows of the table in the usage text: how a row begins, and the exit code that the program
has for such an ending. -/
def rows : List (String × UInt32) :=
  [("YES", (Model.Stages.CallEnd.yes a0 c0).status),
   ("WITHIN LIMITS:", (Model.Stages.CallEnd.withinLimits a0 c0).status),
   ("NOT-A-VERIFICATION", (Model.Stages.CallEnd.notVer [] none c0).status),
   ("NO:", (Model.Stages.CallEnd.no "reader").status),
   ("NOT CHECKED:", (Model.Stages.CallEnd.notChecked "reader").status),
   ("PART PASSED:", (Model.Stages.CallEnd.partPassed .key c0).status),
   ("TEST FILES PASSED", Ending.testPassed.status), ("PLAN ONLY:", Ending.planned.status),
   ("input-unreadable-", (Model.Stages.CallEnd.unreadable .proof).status),
   ("not to be relied on", Ending.unwritten.status)]

-- the usage text has one row for each, with that exit code; no line of it is above 100 characters
#guard rows.all fun (w, code) =>
  match (usage.splitOn "\n").filter (·.startsWith ("  " ++ w)) with
  | [l] => (l.splitOn ("  " ++ toString code ++ "  ")).length == 2
  | _ => false
#guard (usage.splitOn "\n").all fun l => decide (l.length ≤ 100)
-- a fault, after which standard output is empty, shares its exit code with an unreadable input
#guard Ending.fault.status == (Model.Stages.CallEnd.unreadable .proof).status
#guard !(bitsNote 127).isEmpty && (bitsNote 128).isEmpty
-- cp_verify's clause (RECORDCLAUSE, verifier/src/vf_common.h) ends the line
#guard (Line.commitment 0 true).text L0 ==
  "commitment: every closeness round of the one-time files rests on the proved lemma" ++ clause61
#guard (Line.commitment 1 true).text L0 ==
  "commitment: 1 closeness round of the one-time files rests on another source than the proved " ++
    "lemma" ++ clause61
#guard (Line.commitment 2 true).text L0 ==
  "commitment: 2 closeness rounds of the one-time files rest on another source than the proved " ++
    "lemma" ++ clause61
#guard (linesOf (.yes a0 c0)).take 5 == ["---- the call ----", "commitment ID: " ++ id64,
  "id: named by the caller and equal", "h_par=" ++ id64,
  "weight hiding: NOT CHECKED BY THIS CALL (it rests on how the commitment was made)"]
#guard linesOf .wrongId ==
  ["id: these are not the files of the commitment that you named; nothing in them was checked",
   "id: take the commitment ID from your own record of where it was published, never from " ++
     "these files", "NO: model-statement"]
#guard linesOf (.refusedBy .request (some "reader") "proof-refused") ==
  ["---- the call ----", "refused by the stage request: reader", "NO: unlisted-check"]
#guard linesOf (.refusedBy .request (some "x y") "reader") ==
  ["---- the call ----", "refused by the stage request", "NO: reader"]
#guard (linesOf (.partPassed .leaf c0)).getLast? == some "PART PASSED: leaf"
#guard (linesOf (.partPassed .leaf c0)).length == 7 && (linesOf (.partPassed .key c0)).length == 6
-- a call on an entry file alone that ends as not a verification says that the key is not checked
#guard ((before { leafCall := true } (.notVer [] none c0)).map (Line.text L0)).any
  (·.startsWith "key: NOT CHECKED BY THIS CALL")
#guard !((before {} (.notVer [] none c0)).map (Line.text L0)).any
  (·.startsWith "key: NOT CHECKED BY THIS CALL")
-- a name with a line feed is not printed, even if it is in the list
#guard (Line.no "x\nYES").text ⟨["x\nYES"], []⟩ == "NO: unlisted-check"
#guard (linesOf (.policy .notNamed)).getLast? == some "NO: policy"
-- the last line is `CallEnd.lastLine`; an unreadable file and a bad command line are left out
#guard [.yes a0 c0, .withinLimits a0 c0, .partPassed .key c0, .notVer [] none c0,
    .refusedBy .key none "reader", .wrongId, .policy .differs, .no "reader",
    .notChecked "reader"].all fun (e : Model.Stages.CallEnd) =>
  (verdict {} e).text L0 == e.lastLine
/-- What follows a read, on the answer r; nothing if q does not begin with a read. -/
def afterRead (r : FileRead) : Ask Ending → Option (Ask Ending)
  | .read _ _ next => some (next r)
  | _ => none

/-- The number of bytes that q asks for, if it begins with a read. -/
def askedBytes : Ask Ending → Option Nat
  | .read _ n _ => some n
  | _ => none

/-- The line that q prints, if it begins with a printed line. -/
def firstLine : Ask Ending → Option String
  | .say l _ => some l
  | _ => none

/-- n zero bytes, as the answer to a read. -/
def zeros (n : Nat) : FileRead := .bytes (Fmt.zeroBytes n)

/-- A read under the limit 3 that goes on to print `next`. -/
def fetch3 : Ask Ending := fetch L0 3 "p" fun _ => .say "next" fun _ => .done .fault

-- the three limits
#guard fileLimit == 2 ^ 28 && textLimit == 2 ^ 20 && listLimit == 2 ^ 22
-- a read asks for one byte more than its limit; a file of the limit's length goes on, one byte more
-- is refused
#guard askedBytes fetch3 == some 4
#guard ((afterRead (zeros 3) fetch3).bind firstLine) == some "next"
#guard ((afterRead (zeros 4) fetch3).bind firstLine) == some "NO: file-too-long"
#guard ((afterRead .absent fetch3).bind firstLine) == some "next"
-- which limit the reads of a call have; not tried: a whole call's entry and four of five test calls
/-- Checks that refuse everything: the tests below look only at what a call reads. -/
def modelChecks0 : Checks :=
  { names := [], places := [], entryNumber := fun _ _ => .error (.no "reader"),
    wholeCall := fun _ _ => .no "reader", keyCall := fun _ _ => .no "reader",
    leafCall := fun _ _ => .no "reader", plan := fun _ _ _ _ => .error (.no "reader") }

/-- The numbers of bytes that the first k reads of q ask for, if each is answered with no byte. -/
def askedAll : Nat → Ask Ending → List Nat
  | 0, _ => []
  | k + 1, q =>
    match q with
    | .read _ n next => n :: askedAll k (next (zeros 0))
    | _ => []

#guard askedAll 3 (call modelChecks0 ["plan", "c"]) == [textLimit + 1, fileLimit + 1, textLimit + 1]
#guard askedAll 7 (call modelChecks0 ["verify", "c", "i", "r", "y", "p"]) ==
  [textLimit + 1, fileLimit + 1, textLimit + 1, fileLimit + 1, fileLimit + 1, fileLimit + 1,
   fileLimit + 1]
#guard askedAll 4 (call modelChecks0 ["verify", "-key", "c", "k"]) ==
  [textLimit + 1, fileLimit + 1, textLimit + 1, fileLimit + 1]
#guard askedAll 5 (call modelChecks0 ["verify", "-leaf", "c", "k", "e"]) ==
  [textLimit + 1, fileLimit + 1, textLimit + 1, fileLimit + 1, fileLimit + 1]
#guard askedAll 2 (call modelChecks0 ["product", "a", "b"]) == [listLimit + 1, listLimit + 1]
-- every name is at most 80 characters: letters, digits and eight signs
#guard ownNames.all fun s => decide (s.length ≤ 80) && s.toList.all fun c =>
  c.isAlphanum || "-.:_@ ()".toList.contains c
#guard !ownNames.contains "unlisted-check"

-- The default values. Compiled code that reads beyond the end of an array returns the type's
-- default value. So no type that has a passing value may have a passing default. Two of the four
-- defaults below come from `deriving Inhabited`, which takes the first constructor: these guards
-- fail if the constructors are put in another order.
#guard (default : Verdict) == .refused ⟨.configuration, "internal-default-value"⟩
#guard (default : Ending) == .fault
#guard (default : Model.Stages.StageEnd) == .no ""
#guard (default : Model.Stages.CallEnd) == .notChecked "internal-stage"

end OnBytes.ShellTest

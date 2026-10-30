-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyHeads.lean: tests of the parts of a whole call that need no files of a
model: the tests before the stages, their order, and the names with which a stage refuses. The
expected ends are read off the C++ source (cpMain, cpStagesRun, cpPolicySays, cpPolicyHeld,
cpLengthHeld, verifier/src/cp_verify.cpp; vf_input_files.h; blocks/frame/version.h); no guard
compares with a run of it. The words of a bad command line (.usage) are the C++ verifier's for the
ID's form; the others are shorter than its words or empty. The name internal-policy-empty is this
program's own. No guard here runs a stage of a call: the one stage's result that is judged here,
`keyWithWork`, is made by hand. This file is not part of the program.

Whence the numbers and strings come. All were typed by hand. None was copied from a program's
output, and none is taken from a key, an entry, a proof or a model's weights. Read off the C++
source: the first five numbers of each of the ten guards on saysEnd that open the section on a named
policy that is refused by its numbers (the cases that verifier/src/vf_common.h tests of
policyEmpty), and that routine's codes 0 to 4; the served version's word H821
(blocks/frame/version.h); the exit codes 1, 2, 3, 5 and 14; the place 7 that one guard expects with
noneBarred, T - 1 at T = 8; the bytes 0x37 and 0x47, the marks 7 and G of an earlier format
(blocks/frame/version.h). Three policies also stand in vf_common.h, among the cases that it tests of
policyKind: 300 299 0 15 8 15, 300 299 0 15 8 14, and 256 256 0 15 8 4, which is the policy of the
example of OnBytes/Model/TestConfig.lean as well. The other policies are these with C, theta, cap,
sh or sT changed. The changed numbers and all others were chosen by hand for the test that they try,
many of them at or beside a bound that the C++ source sets: 129 requested bits; 63 and 64 hex
digits; headers of 8 and 12 bytes, and a byte fewer; 255 and 256 around 2^sh at sh 8; lt 21; sh 63;
numbers of ten and eleven digits (9999999999, 12345678901), which are there for their length alone;
the version words H811 and H822, one sign away from H821; in `keyWithWork` 100.00 bits without work
and 28 bits of work, which together make the target 128, in three rounds. The files are empty, zero
bytes, right headers (one lacks its last byte), or a few lines of a parameter file. A request is
eight tokens 0 and two or three small numbers. The strings are words of the C++ verifier or of this
library (names of refusals and of one cause, last lines, kinds of policies, the words of a bad
command line), lines of a parameter file or pieces of them, an ID of two digits, and one name that
stands in no list. The letters A, a and g, repeated, make up the other IDs.
-/
import OnBytes.Model.Verify

namespace OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- A call in which no file can be read. -/
def noFiles : Files :=
  { policy := none, KL := none, layout := none, key := none, request := none, y := none,
    proof := none }

/-! ## The command line comes before the files, and the ID's form before the bits -/

#guard wholeCall {} noFiles == .unreadable .policy
#guard (wholeCall {} noFiles).status == 2
#guard (wholeCall { bits := 129 } noFiles).lastLine == "NO: cp-bits-above-digest"
#guard wholeCall { id := some "12" } noFiles == .usage "-id requires 64 hex digits"
#guard (wholeCall { id := some "12", bits := 129 } noFiles).status == 2
#guard keyCall {} noFiles == .unreadable .policy
#guard leafCall {} noFiles == .unreadable .policy

/-! ## The scale file's length and the key's header come before the later files are read -/

#guard (wholeCall {} { noFiles with policy := some .empty, KL := some ⟨#[0, 0, 0]⟩ }).lastLine ==
  "NO: KL-length"

/-- A call with a parameter file of the served version, a scale file of eight zero words and a key
file of eight zero bytes. The request, the reply and the proof cannot be read. -/
def wrongKeyHead : Files :=
  { noFiles with
    policy := some "version H821\nsec 128\n".toUTF8
    KL := some (Fmt.zeroBytes 32)
    key := some ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ }

#guard (wholeCall {} wrongKeyHead).lastLine == "NO: cp-key-head"

/-! ## A named policy -/

/-- A policy of the kind that no command line can name. -/
def fourthKind : PolicyNamed := ⟨"another-table", 1, 1, 0, 15, 8⟩

#guard !kindNamed fourthKind
#guard kindNamed { fourthKind with kind := "exact-match" }
#guard kindNamed { fourthKind with kind := "clipped-gap" }
#guard !kindNamed { fourthKind with kind := "log-probability" }
#guard wholeCall { policy := some fourthKind } noFiles ==
  .usage "-policy requires kind,C,theta,cap,s,sh"
#guard wholeCall { policy := some { fourthKind with kind := "log-probability" } } noFiles ==
  .usage "-policy requires kind,C,theta,cap,s,sh"

/-! ## A named policy that is refused by its numbers

The first ten guards are the values that the C++ program tests of its routine policyEmpty when it is
built (verifier/src/vf_common.h), each with the end of the call that follows from it by `policyEnd`,
whose four reasons stand in the order of the C++ routine cpPolicySays. The sixth argument, 63, is
not one of that routine's: it is the position that the reason noneBarred reports. -/

/-- The end of the call that follows from a named policy's numbers, if they end it. -/
def saysEnd (n C theta cap sh place : Nat) : Option CallEnd :=
  match policyEnd (policyEmpty n C theta cap sh) place with
  | .error e => some e
  | .ok _ => none

#guard saysEnd 1 256 256 0 8 63 == none
#guard saysEnd 0 255 255 0 8 63 == some (.policy .clipBelowLeast)
#guard saysEnd 0 300 255 0 8 63 == some (.policy .meanBelowLeast)
#guard saysEnd 0 256 257 0 8 63 == some (.policy .meanAboveClip)
#guard saysEnd 3 256 256 3 8 63 == some (.policy (.noneBarred 63))
#guard saysEnd 4 256 256 3 8 63 == none
#guard saysEnd 0 256 256 3 8 63 == none
#guard saysEnd 500 4096 300 10 8 63 == none
#guard saysEnd 1 128 128 0 7 63 == none
#guard saysEnd 1 128 128 0 8 63 == some (.policy .clipBelowLeast)

-- policyEnd by itself: 0 lets a call go on; 1 to 6 and 255 do not; 5, 6 and 255, which stand for no
-- reason, end it as not checked. No guard brings a call to that end.
#guard (policyEnd 0 63).isOk
#guard [1, 2, 3, 4, 5, 6, 255].all fun kind => !(policyEnd kind 63).isOk
#guard [5, 6, 255].all fun kind =>
  match policyEnd kind 63 with
  | .error e => e == .notChecked "internal-policy-empty" && e.status == 5
  | .ok _ => false
#guard namesHeads.contains "internal-policy-empty" && internalName "internal-policy-empty"

-- the numbers of a named policy are tested before any file is opened, and after the bits
#guard wholeCall { policy := some ⟨"clipped-gap", 255, 255, 0, 15, 8⟩ } noFiles ==
  .policy .clipBelowLeast
#guard wholeCall { policy := some ⟨"clipped-gap", 300, 301, 0, 15, 8⟩ } noFiles ==
  .policy .meanAboveClip
#guard (wholeCall { policy := some ⟨"clipped-gap", 255, 255, 0, 15, 8⟩ } noFiles).lastLine ==
  "NO: policy"
#guard (wholeCall { policy := some ⟨"clipped-gap", 255, 255, 0, 15, 8⟩ } noFiles).status == 1
#guard (wholeCall { bits := 129, policy := some ⟨"clipped-gap", 255, 255, 0, 15, 8⟩ }
  noFiles).lastLine == "NO: cp-bits-above-digest"
#guard wholeCall { policy := some ⟨"clipped-gap", 300, 299, 0, 15, 8⟩ } noFiles ==
  .unreadable .policy

/-! ## The parameter file's policy against the call -/

/-- The lines of a parameter file that the test on the policy reads, without the file's first 32
lines. T is 8. -/
def policyLines (C theta cap s sh sT : Nat) : ByteArray :=
  ("lt 3\nC " ++ toString C ++ "\ntheta " ++ toString theta ++ "\ncap " ++ toString cap ++ "\ns " ++
    toString s ++ "\nsh " ++ toString sh ++ "\nsT " ++ toString sT ++ "\n").toUTF8

/-- A request of eight tokens that covers the positions r to e - 1. -/
def requestOf (r e : Nat) : Array Nat := Array.replicate 8 0 ++ #[r, e]

/-- The end of the call that the test on the policy gives, if it gives one. -/
def heldEnd (p : Option PolicyNamed) (pol : ByteArray) (request : Array Nat) : Option CallEnd :=
  match cpPolicyHeld p pol request with
  | .error e => some e
  | .ok _ => none

-- the exact match, no policy named: nothing to refuse, whatever is covered
#guard heldEnd none (policyLines 256 256 0 15 8 4) (requestOf 0 8) == none
-- another kind of table than the two
#guard heldEnd none (policyLines 300 299 0 15 8 15) (requestOf 7 8) ==
  some (.policy (.fileKind true))
#guard heldEnd none (policyLines 300 299 0 15 8 14) (requestOf 7 8) ==
  some (.policy (.fileKind false))
-- a named policy that is not the file's
#guard heldEnd (some ⟨"clipped-gap", 300, 298, 0, 15, 8⟩) (policyLines 300 299 0 15 8 4)
  (requestOf 7 8) == some (.policy .differs)
#guard heldEnd (some ⟨"exact-match", 300, 299, 0, 15, 8⟩) (policyLines 300 299 0 15 8 4)
  (requestOf 7 8) == some (.policy .differs)
-- a clipped gap, none named: refused if a token of the request is covered
#guard heldEnd none (policyLines 300 299 0 15 8 4) (requestOf 6 8) == some (.policy .notNamed)
#guard heldEnd none (policyLines 300 299 0 15 8 4) (requestOf 7 8) == none
-- theta = C and cap not below the number of checked tokens
#guard heldEnd (some ⟨"clipped-gap", 300, 300, 3, 15, 8⟩) (policyLines 300 300 3 15 8 4)
  (requestOf 4 8) == some (.policy (.noneBarred 7))
#guard heldEnd (some ⟨"clipped-gap", 300, 300, 3, 15, 8⟩) (policyLines 300 300 3 15 8 4)
  (requestOf 3 8) == none
#guard heldEnd (some ⟨"clipped-gap", 300, 300, 3, 15, 8⟩) (policyLines 300 300 3 15 8 4)
  (requestOf 7 8) == none
-- not decided here: a request of another length or range, a file without one of the lines, an lt
-- above 20. That a stage then refuses is not tested in this file
#guard heldEnd none (policyLines 300 299 0 15 8 4) (requestOf 6 8 ++ #[0]) == none
#guard heldEnd none (policyLines 300 299 0 15 8 4) (requestOf 6 9) == none
#guard heldEnd none (policyLines 300 299 0 15 8 4) (requestOf 6 6) == none
#guard heldEnd none "lt 3\nC 300\n".toUTF8 (requestOf 6 8) == none
#guard heldEnd none ("lt 21\n".toUTF8 ++ policyLines 300 299 0 15 8 4) (requestOf 6 8) == none
-- the file's kind is tested before the named policy is compared with the file's
#guard heldEnd (some ⟨"clipped-gap", 300, 298, 0, 15, 8⟩) (policyLines 300 299 0 15 8 15)
  (requestOf 7 8) == some (.policy (.fileKind true))
-- the file's own policy, named, with C below the least cost of a token
#guard heldEnd (some ⟨"clipped-gap", 255, 255, 0, 15, 8⟩) (policyLines 255 255 0 15 8 4)
  (requestOf 7 8) == some (.policy .clipBelowLeast)
-- from sh = 63 on the least cost counts as 2^64 - 1, so this C of ten digits is below it
#guard saysEnd 0 9999999999 9999999999 0 63 7 == some (.policy .clipBelowLeast)
-- how the lines are read: of a line that occurs twice the first decides
#guard heldEnd none ("C 300\n".toUTF8 ++ policyLines 256 256 0 15 8 4) (requestOf 6 8) ==
  some (.policy .notNamed)
-- a value of eleven digits is no value
#guard heldEnd none (policyLines 12345678901 299 0 15 8 15) (requestOf 7 8) == none
-- a name with a blank and nothing after it is passed over
#guard heldEnd none ("C \n".toUTF8 ++ policyLines 300 299 0 15 8 15) (requestOf 7 8) ==
  some (.policy (.fileKind true))
-- a whole file whose first lines are refused gives no numbers
#guard heldEnd none ("version H821\n".toUTF8 ++ policyLines 300 299 0 15 8 15) (requestOf 7 8) ==
  none

/-! ## An entry that cannot be read -/

/-- A call whose files pass every test before the entry is read. There is no entry. -/
def noEntry : Files :=
  { noFiles with
    policy := some "version H821\nsec 128\n".toUTF8
    KL := some (Fmt.zeroBytes 32)
    key := some (Proof.FileKind.key.tag ++ servedVersion)
    request := some .empty
    y := some (Fmt.zeroBytes 4)
    proof := some (Proof.FileKind.proof.tag ++ servedVersion ++ Fmt.zeroBytes 4) }

-- in a call on an entry alone the path is the caller's own word; in a whole call it is the proof's
#guard leafCall {} noEntry == .unreadable .entry
#guard wholeCall {} noEntry == .no "cp-entry-missing"

/-! ## The test on a file's length by itself, and the reply's length in a whole call

The request's length in a whole call, and the order against a file that cannot be read, are in
OnBytes/Model/TestVerifyLengths.lean. -/

/-- The end of the call that the test on a file's length gives, if it gives one. -/
def lengthEnd (f : FileIn) (words : Nat) : Option CallEnd :=
  match cpLengthHeld f words with
  | .error e => some e
  | .ok _ => none

#guard lengthEnd (some (Fmt.zeroBytes 40)) 10 == none
#guard lengthEnd (some (Fmt.zeroBytes 44)) 10 == some (.no "statement-range")
#guard lengthEnd (some (Fmt.zeroBytes 41)) 10 == some (.no "statement-required")
#guard lengthEnd (some .empty) 10 == some (.no "statement-required")
#guard lengthEnd (some (Fmt.zeroBytes 8)) 1 == some (.no "statement-range")
-- a file that cannot be read is left to the read
#guard lengthEnd none 1 == none
-- a reply of a wrong length is refused before the proof is read
#guard wholeCall {} { noEntry with y := some (Fmt.zeroBytes 8) } == .no "statement-range"
#guard wholeCall {} { noEntry with y := some (Fmt.zeroBytes 8), proof := none } ==
  .no "statement-range"

/-! ## A file that cannot be read, and the names of the headers' tests

Whole calls only. Six files are taken away one at a time: KL, layout, key, request, y, proof. Each
ends the call under its own role. The parameter file is tried at the top of this file. A missing
entry ends a whole call with a no (the section on an entry that cannot be read). Of the headers'
four names three are here; cp-key-head is further up. -/

#guard wholeCall {} { noEntry with KL := none } == .unreadable .KL
#guard wholeCall {} { noEntry with layout := some none } == .unreadable .layout
#guard wholeCall {} { noEntry with key := none } == .unreadable .key
#guard wholeCall {} { noEntry with request := none } == .unreadable .request
#guard wholeCall {} { noEntry with y := none } == .unreadable .y
#guard wholeCall {} { noEntry with proof := none } == .unreadable .proof
#guard wholeCall {} { noEntry with key := some (Fmt.zeroBytes 7) } == .no "cp-key-length"
#guard wholeCall {} { noEntry with proof := some (Fmt.zeroBytes 12) } == .no "cp-proof-head"

/-- `noEntry` with a proof file of eleven bytes: its tag, the served version and three bytes. -/
def shortProof : Files :=
  { noEntry with proof := some (Proof.FileKind.proof.tag ++ servedVersion ++ Fmt.zeroBytes 3) }

#guard wholeCall {} shortProof == .no "cp-proof-length"

/-- `noEntry` with another field's version in the parameter file's first line, and a key file of
eight zero bytes. -/
def otherField : Files :=
  { noEntry with
    policy := some "version H811\nsec 128\n".toUTF8
    key := some (Fmt.zeroBytes 8) }

-- the version in the first line is tested before the key's header
#guard wholeCall {} otherField == .no "version-of-another-field (policy)"
-- the other byte that marks an earlier format; the first is tried further down
#guard versionRefusal [0x48, 0x37, 0x32, 0x31] == "version-of-an-earlier-format (policy)"

/-! ## The options of a whole call, given to a call on one file -/

#guard keyCall { nextToken := true } noFiles == .usage ""
#guard leafCall { nextToken := true } noFiles == .usage ""
-- leafCall's own test, where the files can be read and the entry is missing
#guard leafCall { nextToken := true } noEntry == .usage ""
#guard keyCall { policy := some { fourthKind with kind := "exact-match" } } noFiles == .usage ""
#guard leafCall { policy := some { fourthKind with kind := "exact-match" } } noFiles == .usage ""

/-! ## The option -no-proof-of-work -/

-- it belongs to a call on one file too: such calls go on to the files
#guard keyCall { noProofOfWork := true } noFiles == .unreadable .policy
#guard leafCall { noProofOfWork := true } noFiles == .unreadable .policy
#guard leafCall { noProofOfWork := true } noEntry == .unreadable .entry
-- readFirst hands the option on in id, which cpStagesRun reads, and its default is off. It does so
-- for a whole call (needed is true) and for a call on one file alone (needed is false)
#guard ((readFirst { noProofOfWork := true } noEntry true).toOption.map (·.id.noProofOfWork)) ==
  some true
#guard ((readFirst { noProofOfWork := true } noEntry false).toOption.map (·.id.noProofOfWork)) ==
  some true
#guard ((readFirst {} noEntry true).toOption.map (·.id.noProofOfWork)) == some false
#guard ((readFirst {} noEntry false).toOption.map (·.id.noProofOfWork)) == some false
-- readCall keeps it. On these files a whole call ends with the option as it does without it
#guard ((readCall { noProofOfWork := true } noEntry).toOption.map (·.id.noProofOfWork)) == some true
#guard wholeCall { noProofOfWork := true } noEntry == .no "cp-entry-missing"

/-- A stage key that has passed with work, made by hand: no stage is run. -/
def keyWithWork : StageOut :=
  { name := .key, ending := .passed, idHex := String.ofList (List.replicate 64 'a'),
    acct := some { target := 128, needsWork := true, centibits := 10000, work := 28, byWork := 3,
                   mostWork := 28, leastRound := 12800 },
    work := some ⟨10000, 28, ""⟩ }

/-- The end of a call on the key alone as partCall (OnBytes/Model/Verify.lean) forms it, but for its
test on -next-token and -policy and for the stage: id comes from readFirst at needed = false, on the
options o, and the stage is `keyWithWork`. -/
def partEnd (o : Options) : Option CallEnd :=
  (readFirst o noEntry false).toOption.map fun r =>
    cpStagesRun [keyWithWork] (some .key) (askedBelowBar o.bits) o.bits r.id none

-- where the stage passed with work, the option makes a call on one file not a verification
#guard (partEnd {}).map (·.status) == some 3
#guard (partEnd { noProofOfWork := true }).map (·.status) == some 14
#guard (partEnd { noProofOfWork := true }).map (·.lastLine) == some "NOT-A-VERIFICATION"
#guard (partEnd { noProofOfWork := true }).map
    (fun e => match e with | .notVer causes _ _ => causes | _ => []) == some ["no-proof-of-work"]
-- That wholeCall and partCall themselves pass id on to cpStagesRun is not tested here

/-! ## What readFirst returns besides the configuration files and the key -/

-- policyGiven says whether the options name a policy
#guard ((readFirst {} noEntry true).toOption.map (·.id.policyGiven)) == some false
#guard ((readFirst { policy := some ⟨"clipped-gap", 300, 299, 0, 15, 8⟩ } noEntry true).toOption.map
    (·.id.policyGiven)) == some true
-- named, asked and needed: from the option -id, in lower-case digits, and from the argument
#guard ((readFirst { id := some (String.ofList (List.replicate 64 'A')) } noEntry true).toOption.map
    fun r => (r.id.named, r.id.asked, r.id.needed)) ==
  some (true, String.ofList (List.replicate 64 'a'), true)
#guard ((readFirst {} noEntry false).toOption.map fun r => (r.id.named, r.id.asked, r.id.needed)) ==
  some (false, "", false)
-- hPar: the digest of the configuration files, in hex digits, by this program's own hPar
#guard ((readFirst {} noEntry true).toOption.map (·.id.hPar)) ==
  (hPar "version H821\nsec 128\n".toUTF8 (Fmt.zeroBytes 32) none).toOption.map hex64
#guard ((readFirst {} noEntry true).toOption.map (·.id.hPar.length)) == some 64
-- the request, the reply and the proof are left empty, and the entry's number is 0
#guard ((readFirst {} noEntry true).toOption.map
    fun r => (r.request.size, r.y.size, r.proof.size, r.entry)) == some (0, 0, 0, 0)
-- named does not depend on needed
#guard ((readFirst { id := some (String.ofList (List.replicate 64 'A')) } noEntry
    false).toOption.map fun r => (r.id.named, r.id.needed)) == some (true, false)

/-- Every option but -no-proof-of-work is set. -/
def allButNoWork : Options :=
  { id := some (String.ofList (List.replicate 64 'A')), bits := 100, nextToken := true,
    policy := some ⟨"clipped-gap", 300, 299, 0, 15, 8⟩ }

-- no other option turns -no-proof-of-work off or on, in readFirst or in readCall
#guard ((readFirst { allButNoWork with noProofOfWork := true } noEntry true).toOption.map
    (·.id.noProofOfWork)) == some true
#guard ((readCall { allButNoWork with noProofOfWork := true } noEntry).toOption.map
    (·.id.noProofOfWork)) == some true
#guard ((readFirst allButNoWork noEntry true).toOption.map (·.id.noProofOfWork)) == some false
#guard ((readCall allButNoWork noEntry).toOption.map (·.id.noProofOfWork)) == some false
-- nor does -no-proof-of-work turn policyGiven or named
#guard ((readFirst { noProofOfWork := true } noEntry true).toOption.map
    fun r => (r.id.policyGiven, r.id.named)) == some (false, false)
-- the same where needed is false, and to the end of a call on the key alone that names the ID
#guard ((readFirst { allButNoWork with noProofOfWork := true } noEntry false).toOption.map
    (·.id.noProofOfWork)) == some true
#guard ((readFirst allButNoWork noEntry false).toOption.map (·.id.noProofOfWork)) == some false
#guard (partEnd { id := allButNoWork.id }).map (·.status) == some 3
#guard (partEnd { id := allButNoWork.id, noProofOfWork := true }).map (·.status) == some 14
-- the commonest call: a whole call with -id and -no-proof-of-work and no other option
#guard ((readFirst { id := allButNoWork.id, noProofOfWork := true } noEntry true).toOption.map
    (·.id.noProofOfWork)) == some true
#guard ((readCall { id := allButNoWork.id, noProofOfWork := true } noEntry).toOption.map
    (·.id.noProofOfWork)) == some true

/-! ## The ID's form -/

#guard idAsked (String.ofList (List.replicate 64 'A')) ==
  some (String.ofList (List.replicate 64 'a'))
#guard idAsked (String.ofList (List.replicate 63 'a')) == none
#guard idAsked (String.ofList (List.replicate 64 'g')) == none

/-! ## The first line of the parameter file -/

#guard (cpPolicyWord "version H821\nsec 128\n".toUTF8).isOk
#guard !(cpPolicyWord "version H821".toUTF8).isOk
#guard !(cpPolicyWord "version H821 \n".toUTF8).isOk
#guard versionRefusal [0x48, 0x47, 0x32, 0x31] == "version-of-an-earlier-format (policy)"
#guard versionRefusal [0x48, 0x38, 0x31, 0x31] == "version-of-another-field (policy)"
#guard versionRefusal [0x48, 0x38, 0x32, 0x32] == "version-of-another-hash (policy)"
#guard versionRefusal [] == "version-unknown (policy)"

/-! ## The headers of key and proof -/

#guard !(cpKeyHead .empty).isOk
#guard !(cpProofHead ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩).isOk

/-! ## The name with which a stage refuses -/

#guard refusalName ⟨.configuration, "table-shape"⟩ "key-refused" "internal-key-parameters" ==
  "internal-key-parameters"
#guard refusalName ⟨.key, "one-time-chain-parameters"⟩ "key-refused" "internal-key-parameters" ==
  "internal-key-parameters"
#guard refusalName ⟨.key, "table"⟩ "key-refused" "internal-key-parameters" == "key-refused"
#guard refusalName ⟨.proof, "first-chain-decision"⟩ "proof-refused" "internal-proof-parameters" ==
  "proof-refused"

-- the name taken to mean "the proof is about another reply" is one that the checker can give
#guard Proof.fileNames.contains replyRefusal

-- a sub-proof's own name is passed on; a name of the proof's checker or an unknown one is not
#guard proofRefusalName ⟨.proof, "header-y"⟩ == "header-y"
#guard proofRefusalName ⟨.proof, replyRefusal⟩ == "reply-differs"
#guard proofRefusalName ⟨.proof, "first-chain-decision"⟩ == "proof-refused"
#guard proofRefusalName ⟨.proof, "first-chain-reader-opening"⟩ == "proof-refused"
#guard proofRefusalName ⟨.proof, "first-chain-parameters"⟩ == "internal-proof-parameters"
#guard proofRefusalName ⟨.proof, "a name that stands in no list"⟩ == "proof-refused"
#guard Proof.fileNames.all fun n => !subProofNames.contains n
#guard !subProofNames.contains "proof-refused" && !subProofNames.contains "reply-differs"

-- the three names for a checker's refusal on its own parameters end a call as not checked
#guard ["internal-key-parameters", "internal-entry-parameters", "internal-proof-parameters"].all
  fun n => internalName n && names.contains n
#guard names.contains "reply-differs" && !internalName "reply-differs"

end OnBytes.Model.Verify

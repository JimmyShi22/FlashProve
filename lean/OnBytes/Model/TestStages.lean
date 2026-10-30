-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestStages.lean: tests of OnBytes/Model/Stages.lean: what a refusal's name means, what
a call's answer is about, the result of a stage, and the rules by which the stages' results make the
result of a call. The expected values were written by hand from the C++ source
(verifier/src/cp_verify.cpp, cpStagesRun and cpCovered; verifier/src/vf_common.h), except those of
the guards on the defaults, which are this library's own. The program does not import this file.
-/
import OnBytes.Model.Stages

namespace OnBytes.Model.Stages

#guard internalName "internal-stage"
#guard internalName "G0:internal-slot-twice"
#guard internalName "H:internal-h-free-slot"
#guard !internalName "proof-refused"
#guard !internalName ":internal-x"
#guard !internalName "G0:proof-length"
#guard !internalName "a b:internal-x"

#guard hundredths 9602 == "96.02"

/-- An ID of 64 digits. -/
def someId : String := String.ofList (List.replicate 64 'a')

/-- A stage that has passed without work, at the target 128. -/
def passedStage (n : StageName) : StageOut :=
  { name := n, ending := .passed, idHex := someId,
    acct := some { target := 128, needsWork := false } }

/-- The three stages, all passed. -/
def allPassed : List StageOut := [passedStage .key, passedStage .leaf, passedStage .request]

/-- The caller has named the ID. -/
def named : CpId := { asked := someId, named := true }

/-! ## What the answer is about -/

/-- The lines of the exact match. -/
def exactLines : PolicyLines := ⟨256, 256, 0, 15, 8, 4, 24⟩

/-- The lines of a clipped-gap policy. -/
def gapLines : PolicyLines := ⟨120000000, 119999999, 63, 15, 8, 4, 24⟩

/-- A request of 64 tokens with the given r and e. -/
def request (r e : Nat) : Array UInt32 :=
  (Array.replicate 64 (0 : UInt32)).push r.toUInt32 |>.push e.toUInt32

/-- The reply's token alone, under the exact match. -/
def nextAlone : Covered :=
  { r := 63, e := 64, T := 64, C := 256, theta := 256, cap := 0, s := 15, sh := 8, sT := 4, F := 24,
    aboveClip := 0, policy := .exactMatch }

/-- The name with which x refuses, or the empty text. -/
def whyNot (x : Except String Covered) : String :=
  match x with
  | .error name => name
  | .ok _ => ""

#guard (cpCovered (request 63 64) exactLines).toOption == some nextAlone
#guard nextAlone.tokens == none && nextAlone.y && nextAlone.nextToken && !nextAlone.otherKind
#guard nextAlone.claim == .nextToken
#guard ((cpCovered (request 60 64) exactLines).toOption.map fun a =>
    (a.tokens, a.y, a.nextToken, a.otherKind, a.claim)) ==
  some (some (61, 63), true, false, false, .exactMatch)
#guard ((cpCovered (request 60 62) gapLines).toOption.map fun a =>
    (a.tokens, a.y, a.nextToken, a.otherKind, a.claim, a.policy)) ==
  some (some (61, 62), false, false, true, .policy, .clippedGap)
#guard ((cpCovered (request 63 64) gapLines).toOption.map fun a =>
    (a.tokens, a.otherKind, a.claim, a.policy)) == some (none, false, .nextToken, .clippedGap)
#guard ((cpCovered (request 31 64) ⟨100000, 40000, 64, 15, 8, 4, 24⟩).toOption.map
    (·.aboveClip)) == some 12
#guard whyNot (cpCovered (request 64 64) exactLines) == "internal-covered-line"
#guard whyNot (cpCovered (request 63 65) exactLines) == "internal-covered-line"
#guard whyNot (cpCovered #[0, 1] exactLines) == "internal-covered-line"
#guard whyNot (cpCovered (request 63 64) ⟨300, 299, 0, 15, 8, 15, 24⟩) == "internal-policy-kind"

/-! ## The result of a call -/

/-- `about` for a whole call on the reply's token alone, under the exact match. -/
def next : Option (Array UInt32 × PolicyLines) := some (request 63 64, exactLines)

/-- What a call without work says besides its verdict, if the caller has named the ID. -/
def plain : Closing :=
  { idHex := some someId, idNamed := true, hPar := "", stageWork := [], work := none,
    leastRound := 0, leastWithoutWork := 0, oneTimeAssumed := 0 }

#guard cpStagesRun allPassed none false 128 named next == .yes nextAlone plain
#guard (cpStagesRun allPassed none false 128 named next).lastLine == "YES"
#guard (cpStagesRun allPassed none false 128 named next).status == 0
-- Without a named ID the files' own ID is not shown.
#guard cpStagesRun allPassed none false 128 {} next ==
  .notVer ["id-named"] (some nextAlone) { plain with idHex := none, idNamed := false }
#guard (cpStagesRun allPassed none true 64 named next).status == 14
#guard (cpStagesRun allPassed none true 64 named next).lastLine == "NOT-A-VERIFICATION"
#guard cpStagesRun [passedStage .key] (some .key) false 128 { named with needed := false } none ==
  .partPassed .key plain
-- The stages must be those that the call runs, in their order.
#guard cpStagesRun [passedStage .key] none false 128 named next == .notChecked "internal-stage"
#guard cpStagesRun [passedStage .key, passedStage .key, passedStage .key] none false 128 named
    next == .notChecked "internal-stage"
#guard cpStagesRun [passedStage .leaf] (some .key) false 128 named none ==
  .notChecked "internal-stage"
#guard cpStagesRun allPassed (some .key) false 128 named none == .notChecked "internal-stage"
#guard cpStagesRun [passedStage .request] (some .request) false 128 named none ==
  .notChecked "internal-stage"
-- A refusal by a later stage takes precedence over a fault of the program in an earlier one.
#guard cpStagesRun [{ passedStage .key with ending := .no "internal-x", acct := none },
    passedStage .leaf, { passedStage .request with ending := .no "proof-refused", acct := none }]
    none false 128 named next == .refusedBy .request none "proof-refused"
#guard cpStagesRun [{ passedStage .key with ending := .no "key-refused", acct := none },
    passedStage .leaf, { passedStage .request with ending := .no "proof-refused", acct := none }]
    none false 128 named next == .refusedBy .key none "key-refused"
-- The refusing stage's word on the failed check is passed on.
#guard cpStagesRun [passedStage .key, passedStage .leaf,
    { passedStage .request with ending := .no "proof-refused", acct := none, why := some "w" }]
    none false 128 named next == .refusedBy .request (some "w") "proof-refused"
#guard (CallEnd.refusedBy .request none "token-range").lastLine == "NO: token-range"
#guard (CallEnd.refusedBy .request none "token-range").status == 1
-- An ID other than the files'.
#guard cpStagesRun
    (allPassed.map fun x => { x with ending := .no "model-statement", acct := none })
    none false 128 named next == .wrongId
#guard CallEnd.wrongId.lastLine == "NO: model-statement" && CallEnd.wrongId.status == 1
#guard cpStagesRun [{ passedStage .key with ending := .no "G0:internal-x", acct := none },
    passedStage .leaf, passedStage .request] none false 128 named next ==
  .notChecked "G0:internal-x"
#guard cpStagesRun [passedStage .key, { passedStage .leaf with idHex := "" }, passedStage .request]
    none false 128 named next == .notChecked "internal-id-two-ways"
#guard cpStagesRun [passedStage .key, passedStage .leaf,
    { passedStage .request with ending := .notVer ["exact-match"] }] none false 128 named next ==
  .notVer ["stage request: exact-match"] (some nextAlone) plain

/-- A stage that has passed with work. Its record holds rb, rw and the number m of rounds that need
their work; its note holds bits and work. The parameter file declares at most 32 bits of work. -/
def workedStage (n : StageName) (rb rw m bits work : Nat) : StageOut :=
  { name := n, ending := .passed, idHex := someId,
    acct := some { target := 128, needsWork := true, centibits := rb, work := rw, byWork := m,
                   mostWork := 32, leastRound := 12800 },
    work := some ⟨bits, work, ""⟩ }

/-- Three stages that have passed with work. -/
def allWorked : List StageOut :=
  [workedStage .key 9602 32 14 9602 32, workedStage .leaf 9602 32 5 9602 32,
   workedStage .request 9602 32 38 10011 28]

-- A pass with work is a yes. The counted work is that of the call's record, the last stage's.
#guard cpStagesRun allWorked none false 128 named next ==
  .yes nextAlone { plain with
    stageWork := [(.key, ⟨9602, 32, ""⟩), (.leaf, ⟨9602, 32, ""⟩), (.request, ⟨10011, 28, ""⟩)]
    work := some ⟨32, 38, 12800⟩, leastRound := 12800, leastWithoutWork := 9602 }
#guard (cpStagesRun allWorked none false 128 named next).status == 0
#guard cpStagesRun [workedStage .key 9602 32 14 9602 32] (some .key) false 128 named none ==
  .partPassed .key { plain with
    stageWork := [(.key, ⟨9602, 32, ""⟩)], work := some ⟨32, 14, 12800⟩, leastRound := 12800,
    leastWithoutWork := 9602 }
#guard (CallEnd.partPassed .key plain).lastLine == "PART PASSED: key"
#guard (CallEnd.partPassed .key plain).status == 3
-- The call's record must name the work of the stages' note with the fewest bits.
#guard cpStagesRun [workedStage .key 9702 30 14 9702 30, workedStage .leaf 9602 32 5 9602 32,
    workedStage .request 9602 31 38 9602 28] none false 128 named next ==
  .notChecked "internal-sums-line"
-- A note with 33 bits of work; the most is 32.
#guard cpStagesRun [workedStage .key 9702 33 14 9702 33, passedStage .leaf, passedStage .request]
    none false 128 named next == .notChecked "internal-stage"
-- A stage that ended as not a verification never counts as passed, whatever its list of causes.
#guard cpStagesRun [passedStage .key, passedStage .leaf,
    { passedStage .request with ending := .notVer [] }] none false 128 named next ==
  .notVer ["stage request: no cause printed"] (some nextAlone) plain
#guard cpStagesRun allPassed none false 128 named none == .notChecked "internal-covered-line"
#guard cpStagesRun allPassed none false 128 named (some (request 64 64, exactLines)) ==
  .notChecked "internal-covered-line"
#guard !workFits none none
-- The defaults of five types. CallEnd, StageEnd, StageOut: no pass. Served: a condition is missed.
-- CpId: an ID is needed and none is named, and no option. These four guards run no call.
#guard (default : CallEnd) == .notChecked "internal-stage"
#guard (default : CpId).needed && !(default : CpId).named && !(default : CpId).policyGiven &&
  !(default : CpId).noProofOfWork
#guard (default : StageEnd) == .no "" && (default : StageOut).ending == .no ""
#guard !(servedForm default).isEmpty
-- A record whose two words on work disagree is not read.
#guard cpStagesRun [{ passedStage .key with
      acct := some { target := 128, needsWork := false, byWork := 3 } }]
    (some .key) false 128 named none == .notChecked "internal-sums-line"
#guard cpStagesRun [passedStage .key, passedStage .leaf, { passedStage .request with
      acct := some { target := 128, needsWork := false, byWork := 3 } }]
    none false 128 named next == .notChecked "internal-sums-line"
#guard cpStagesRun [workedStage .key 9602 32 0 9602 32] (some .key) false 128 named none ==
  .notChecked "internal-sums-line"

/-! ## The option -no-proof-of-work -/

/-- The caller has named the ID and passed -no-proof-of-work. -/
def noWork : CpId := { named with noProofOfWork := true }

/-- What a whole call on `allWorked` says besides its verdict, if the caller has named the ID. -/
def workedClosing : Closing :=
  { plain with
    stageWork := [(.key, ⟨9602, 32, ""⟩), (.leaf, ⟨9602, 32, ""⟩), (.request, ⟨10011, 28, ""⟩)]
    work := some ⟨32, 38, 12800⟩, leastRound := 12800, leastWithoutWork := 9602 }

-- Where work is counted, the option makes a yes not a verification. The rest is the same.
#guard cpStagesRun allWorked none false 128 { named with noProofOfWork := false } next ==
  .yes nextAlone workedClosing
#guard cpStagesRun allWorked none false 128 noWork next ==
  .notVer ["no-proof-of-work"] (some nextAlone) workedClosing
#guard (cpStagesRun allWorked none false 128 noWork next).status == 14
-- The same where the last stage alone has passed with work.
#guard cpStagesRun [passedStage .key, passedStage .leaf, workedStage .request 9602 32 38 9602 32]
    none false 128 named next ==
  .yes nextAlone { plain with
    stageWork := [(.request, ⟨9602, 32, ""⟩)], work := some ⟨32, 38, 12800⟩, leastRound := 12800,
    leastWithoutWork := 9602 }
#guard cpStagesRun [passedStage .key, passedStage .leaf, workedStage .request 9602 32 38 9602 32]
    none false 128 noWork next ==
  .notVer ["no-proof-of-work"] (some nextAlone) { plain with
    stageWork := [(.request, ⟨9602, 32, ""⟩)], work := some ⟨32, 38, 12800⟩, leastRound := 12800,
    leastWithoutWork := 9602 }
-- The same where the middle stage alone has passed with work.
#guard cpStagesRun [passedStage .key, workedStage .leaf 9602 32 5 9602 32,
      { workedStage .request 9602 32 5 9602 32 with work := none }]
    none false 128 noWork next ==
  .notVer ["no-proof-of-work"] (some nextAlone) { plain with
    stageWork := [(.leaf, ⟨9602, 32, ""⟩)], work := some ⟨32, 5, 12800⟩, leastRound := 12800,
    leastWithoutWork := 9602 }
-- The same in a call on one file alone.
#guard cpStagesRun [workedStage .key 9602 32 14 9602 32] (some .key) false 128 noWork none ==
  .notVer ["no-proof-of-work"] none { plain with
    stageWork := [(.key, ⟨9602, 32, ""⟩)], work := some ⟨32, 14, 12800⟩, leastRound := 12800,
    leastWithoutWork := 9602 }
-- cp_verify runs such a call with `needed` false. The cause depends neither on that nor on -id.
#guard cpStagesRun [workedStage .key 9602 32 14 9602 32] (some .key) false 128
    { noWork with needed := false } none ==
  .notVer ["no-proof-of-work"] none { plain with
    stageWork := [(.key, ⟨9602, 32, ""⟩)], work := some ⟨32, 14, 12800⟩, leastRound := 12800,
    leastWithoutWork := 9602 }
#guard cpStagesRun [workedStage .leaf 9602 32 5 9602 32] (some .leaf) false 128
    { needed := false, noProofOfWork := true } none ==
  .notVer ["no-proof-of-work"] none { plain with
    idNamed := false, stageWork := [(.leaf, ⟨9602, 32, ""⟩)], work := some ⟨32, 5, 12800⟩,
    leastRound := 12800, leastWithoutWork := 9602 }
#guard cpStagesRun [workedStage .leaf 9602 32 5 9602 32] (some .leaf) false 128
    { needed := false } none ==
  .partPassed .leaf { plain with
    idNamed := false, stageWork := [(.leaf, ⟨9602, 32, ""⟩)], work := some ⟨32, 5, 12800⟩,
    leastRound := 12800, leastWithoutWork := 9602 }
-- Where no work is counted, the option changes nothing.
#guard cpStagesRun allPassed none false 128 noWork next == .yes nextAlone plain
#guard cpStagesRun [passedStage .key] (some .key) false 128 noWork none == .partPassed .key plain
-- Nor does it where the parameter file declares work that no round needs.
#guard cpStagesRun (allPassed.map fun x =>
      { x with acct := some { target := 128, needsWork := false, mostWork := 32 } })
    none false 128 noWork next == .yes nextAlone plain
-- The cause comes after id-named.
#guard cpStagesRun allWorked none false 128 { noProofOfWork := true } next ==
  .notVer ["id-named", "no-proof-of-work"] (some nextAlone)
    { workedClosing with idHex := none, idNamed := false }

/-- A stage has passed with work, and the call's record says that none is needed. -/
def noteAlone : List StageOut :=
  [workedStage .key 9602 32 14 9602 32, passedStage .leaf, passedStage .request]

/-- No stage has passed with work, and the call's record says that work is needed. `last`: how the
stage request ended. -/
def recordAlone (last : StageEnd) : List StageOut :=
  [passedStage .key, passedStage .leaf, { passedStage .request with
    ending := last, acct := some { target := 128, needsWork := true, byWork := 3 } }]

-- Stages and record disagree on work: not checked, with the option as without it.
#guard cpStagesRun noteAlone none false 128 noWork next == .notChecked "internal-sums-line"
#guard cpStagesRun noteAlone none false 128 named next == .notChecked "internal-sums-line"
#guard cpStagesRun (recordAlone .passed) none false 128 noWork next ==
  .notChecked "internal-sums-line"
#guard cpStagesRun (recordAlone .passed) none false 128 named next ==
  .notChecked "internal-sums-line"
-- With the option that test comes before the missing ID, without it after.
#guard cpStagesRun (recordAlone .passed) none false 128 { noProofOfWork := true } next ==
  .notChecked "internal-sums-line"
#guard cpStagesRun (recordAlone .passed) none false 128 { noProofOfWork := false } next ==
  .notVer ["id-named"] (some nextAlone)
    { plain with idHex := none, idNamed := false, work := some ⟨0, 3, 0⟩ }
#guard cpStagesRun noteAlone none false 128 { noProofOfWork := true } next ==
  .notChecked "internal-sums-line"
-- Nor does the test depend on `needed`.
#guard cpStagesRun (recordAlone .passed) none false 128 { noWork with needed := false } next ==
  .notChecked "internal-sums-line"
-- It stands between the test on the stages' IDs and the test on the caller's.
#guard cpStagesRun ((recordAlone .passed).map fun x => { x with idHex := "" }) none false 128
    noWork next == .notChecked "internal-id-two-ways"
#guard cpStagesRun (recordAlone .passed) none false 128 { noWork with asked := "" } next ==
  .notChecked "internal-sums-line"
#guard cpStagesRun allWorked none false 128 { noWork with asked := "" } next ==
  .notChecked "internal-id-two-ways"
-- Where a stage ended as not a verification the test is not made, and the record's word is enough.
#guard cpStagesRun (recordAlone (.notVer ["exact-match"])) none false 128 noWork next ==
  .notVer ["stage request: exact-match", "no-proof-of-work"] (some nextAlone)
    { plain with work := some ⟨0, 3, 0⟩ }
-- There a stage that passed with work is enough too.
#guard cpStagesRun [workedStage .key 9602 32 14 9602 32, passedStage .leaf,
      { passedStage .request with ending := .notVer ["exact-match"] }] none false 128 noWork next ==
  .notVer ["stage request: exact-match", "no-proof-of-work"] (some nextAlone)
    { plain with stageWork := [(.key, ⟨9602, 32, ""⟩)] }
-- The note of a stage that has not passed does not count.
#guard cpStagesRun [passedStage .key, passedStage .leaf, { passedStage .request with
      ending := .notVer ["exact-match"], work := some ⟨9602, 32, ""⟩ }]
    none false 128 noWork next ==
  .notVer ["stage request: exact-match"] (some nextAlone)
    { plain with stageWork := [(.request, ⟨9602, 32, ""⟩)] }
-- The three kinds of cause in their order: a stage's, the missing ID, the option's.
#guard cpStagesRun (recordAlone (.notVer ["exact-match"])) none false 128 { noProofOfWork := true }
    next ==
  .notVer ["stage request: exact-match", "id-named", "no-proof-of-work"] (some nextAlone)
    { plain with idHex := none, idNamed := false, work := some ⟨0, 3, 0⟩ }
-- With `belowBar` set the cause is named all the same, and the test on stages and record is made.
#guard cpStagesRun allWorked none true 64 noWork next ==
  .notVer ["no-proof-of-work"] (some nextAlone) workedClosing
#guard cpStagesRun (recordAlone .passed) none true 64 noWork next ==
  .notChecked "internal-sums-line"
#guard cpStagesRun (recordAlone .passed) none true 64 named next ==
  .notVer [] (some nextAlone) { plain with work := some ⟨0, 3, 0⟩ }
-- A stage's refusal takes precedence over the option.
#guard cpStagesRun [workedStage .key 9602 32 14 9602 32, workedStage .leaf 9602 32 5 9602 32,
      { passedStage .request with ending := .no "proof-refused", acct := none }]
    none false 128 noWork next == .refusedBy .request none "proof-refused"
#guard cpStagesRun [workedStage .key 9602 32 14 9602 32, workedStage .leaf 9602 32 5 9602 32,
      { passedStage .request with ending := .no "model-statement", acct := none }]
    none false 128 noWork next == .wrongId

/-- Three stages that have passed with work. The call's record and the least note differ in the
bits. -/
def otherBits : List StageOut :=
  [workedStage .key 9602 32 14 9602 32, workedStage .leaf 9602 32 5 9602 32,
   workedStage .request 9000 32 38 10011 28]

-- That difference is looked for after the causes: not a verification with the option, not checked
-- without it.
#guard cpStagesRun otherBits none false 128 noWork next ==
  .notVer ["no-proof-of-work"] (some nextAlone) { workedClosing with leastWithoutWork := 9000 }
#guard cpStagesRun otherBits none false 128 named next == .notChecked "internal-sums-line"

/-! ## A policy other than the exact match -/

/-- The caller has named the ID and a policy. -/
def withPolicy : CpId := { named with policyGiven := true }

#guard (cpStagesRun allPassed none false 128 withPolicy
    (some (request 60 64, gapLines))).lastLine ==
  "WITHIN LIMITS: clipped-gap C=120000000 theta=119999999 cap=63 s=15 sh=8"
#guard (cpStagesRun allPassed none false 128 withPolicy
    (some (request 60 64, gapLines))).status == 0
-- With the reply's token alone covered the answer is a yes, with and without a named policy.
#guard (cpStagesRun allPassed none false 128 withPolicy
    (some (request 63 64, gapLines))).lastLine == "YES"
#guard (cpStagesRun allPassed none false 128 named
    (some (request 63 64, gapLines))).lastLine == "YES"
-- Under the exact match the answer is a yes whatever the request covers.
#guard (cpStagesRun allPassed none false 128 named
    (some (request 0 64, exactLines))).lastLine == "YES"
#guard cpStagesRun allPassed none false 128 named (some (request 60 64, gapLines)) ==
  .notChecked "internal-policy-not-given"
#guard cpStagesRun allPassed none false 128 withPolicy
    (some (request 63 64, ⟨300, 299, 0, 15, 8, 15, 24⟩)) ==
  .notChecked "internal-policy-kind"
-- Where work is counted, -no-proof-of-work bars the result within limits too.
#guard (cpStagesRun allWorked none false 128 withPolicy
    (some (request 60 64, gapLines))).lastLine ==
  "WITHIN LIMITS: clipped-gap C=120000000 theta=119999999 cap=63 s=15 sh=8"
#guard (cpStagesRun allWorked none false 128 { withPolicy with noProofOfWork := true }
    (some (request 60 64, gapLines))).status == 14
-- So it is where the caller named no policy. Without the option that call is not checked.
#guard (cpStagesRun allWorked none false 128 noWork (some (request 60 64, gapLines))).status == 14
#guard cpStagesRun allWorked none false 128 named (some (request 60 64, gapLines)) ==
  .notChecked "internal-policy-not-given"
-- Where no work is counted, the option lets the result within limits through.
#guard (cpStagesRun allPassed none false 128 { withPolicy with noProofOfWork := true }
    (some (request 60 64, gapLines))).lastLine ==
  "WITHIN LIMITS: clipped-gap C=120000000 theta=119999999 cap=63 s=15 sh=8"
-- The test on stages and record is made under a named policy too.
#guard cpStagesRun noteAlone none false 128 { withPolicy with noProofOfWork := true } next ==
  .notChecked "internal-sums-line"

/-! ## Further decisions, one by one -/

/-- An ID of 64 other digits. -/
def otherId : String := String.ofList (List.replicate 64 'b')

/-- The call's record where the key alone needs work. -/
def keyWorks : Acct :=
  { target := 128, needsWork := true, centibits := 9602, work := 32, byWork := 14, mostWork := 32,
    leastRound := 12800 }

-- A record whose target is below the bits asked.
#guard cpStagesRun [{ passedStage .key with acct := some { target := 96, needsWork := false } },
    passedStage .leaf, passedStage .request] none false 128 named next ==
  .notChecked "internal-sums-line"
-- A stage whose own record needs work and which has no note.
#guard cpStagesRun [{ passedStage .key with acct := some keyWorks }, passedStage .leaf,
    passedStage .request] none false 128 named next == .notChecked "internal-sums-line"
-- The last stage of a whole call holds the call's record, not its own file's: it may need work
-- where the stage has no note.
#guard (cpStagesRun [workedStage .key 9602 32 14 9602 32, passedStage .leaf,
    { passedStage .request with acct := some keyWorks }] none false 128 named next).lastLine ==
  "YES"
-- In a call on one file alone the one stage's record is its own.
#guard cpStagesRun [{ passedStage .key with acct := some keyWorks }] (some .key) false 128 named
    none == .notChecked "internal-sums-line"
#guard cpStagesRun [{ passedStage .key with ending := .no "", acct := none }, passedStage .leaf,
    passedStage .request] none false 128 named next == .notChecked "internal-stage"
#guard cpStagesRun [{ passedStage .key with acct := none }, passedStage .leaf,
    passedStage .request] none false 128 named next == .notChecked "internal-sums-line"
-- A stage that ended as not a verification and has no record.
#guard cpStagesRun [passedStage .key, passedStage .leaf,
    { passedStage .request with ending := .notVer ["exact-match"], acct := none }]
    none false 128 named next == .notChecked "internal-sums-line"
-- Three of the four tests on the ID; two stages with different IDs are above.
#guard cpStagesRun (allPassed.map fun x => { x with idHex := "ab" }) none false 128
    { asked := "ab", named := true } next == .notChecked "internal-id-two-ways"
#guard cpStagesRun allPassed none false 128 { asked := "", named := true } next ==
  .notChecked "internal-id-two-ways"
#guard cpStagesRun allPassed none false 128 { asked := someId, named := false } next ==
  .notChecked "internal-id-two-ways"
#guard cpStagesRun allPassed none false 128 { asked := otherId, named := true } next ==
  .notChecked "internal-id-two-ways"
-- A fault of the program goes before an ending as not a verification.
#guard cpStagesRun [{ passedStage .key with ending := .no "internal-x", acct := none },
    passedStage .leaf, { passedStage .request with ending := .notVer ["exact-match"] }]
    none false 128 named next == .notChecked "internal-x"
-- An ending as not a verification goes before the rule on work and before the rule on the policy.
#guard (cpStagesRun [workedStage .key 9702 30 14 9702 30, workedStage .leaf 9602 32 5 9602 32,
    workedStage .request 9602 31 38 9602 28] none false 128 {} next).status == 14
#guard (cpStagesRun allPassed none false 128 {} (some (request 60 64, gapLines))).status == 14
-- The test on the kind of policy goes before that ending. This order is this library's own:
-- cp_verify makes the test after that ending and would end this call with NOT-A-VERIFICATION (see
-- cpStagesRun).
#guard cpStagesRun allPassed none false 128 {}
    (some (request 63 64, ⟨300, 299, 0, 15, 8, 15, 24⟩)) == .notChecked "internal-policy-kind"
-- The bits of note and record may differ by a hundredth.
#guard workFits (some ⟨9602, 32, ""⟩) (some { keyWorks with centibits := 9603 })
#guard workFits (some ⟨9603, 32, ""⟩) (some keyWorks)
#guard !workFits (some ⟨9602, 32, ""⟩) (some { keyWorks with centibits := 9604 })
#guard !workFits (some ⟨9602, 32, ""⟩) (some { target := 128, needsWork := false })
#guard !workFits none (some keyWorks)
-- A call on one file alone needs no named ID. Its argument `about` is ignored.
#guard cpStagesRun [passedStage .key] (some .key) false 128 { needed := false } none ==
  .partPassed .key { plain with idNamed := false }
#guard cpStagesRun [passedStage .key] (some .key) false 128 named
    (some (request 60 64, gapLines)) == .partPassed .key plain
#guard (cpStagesRun [passedStage .key] (some .key) true 64 named none).status == 14
-- Only the first refusal counts.
#guard cpStagesRun [{ passedStage .key with ending := .no "key-refused", acct := none },
    { passedStage .leaf with ending := .no "model-statement", acct := none },
    passedStage .request] none false 128 named next == .refusedBy .key none "key-refused"
-- The rounds of key and entry that rest on a source other than the lemma within a third of the
-- distance (Acct.closeOther) are added up. The last stage's record is the call's and is left out.
#guard cpStagesRun
    [{ passedStage .key with
        ending := .notVer [servedReading]
        acct := some { target := 128, needsWork := false, closeOther := 2 } },
     { passedStage .leaf with acct := some { target := 128, needsWork := false, closeOther := 1 } },
     { passedStage .request with
        acct := some { target := 128, needsWork := false, closeOther := 7 } }]
    none false 128 named next ==
  .notVer ["stage key: reading-as-printed"] (some nextAlone)
    { plain with oneTimeAssumed := 3 }
#guard cpStagesRun [{ passedStage .key with
      acct := some { target := 128, needsWork := false, closeOther := 2 } }]
    (some .key) false 128 named none == .partPassed .key plain
-- the call says that the table has a record if some stage has said so (cp_verify: hasRecord)
#guard [(true, false), (false, true), (true, true), (false, false)].all fun x =>
  cpStagesRun
      [{ passedStage .key with oneTimeLine := x.1 }, { passedStage .leaf with oneTimeLine := x.2 },
       passedStage .request]
      none false 128 named next ==
    .yes nextAlone { plain with tableRecord := x.1 || x.2 }
#guard !Acct.taken { target := 513, needsWork := false }
#guard !Acct.taken { keyWorks with mostWork := 65 }
#guard Acct.taken keyWorks
-- All 64 positions under the clipped gap.
#guard ((cpCovered (request 0 64) gapLines).toOption.map fun a =>
    (a.tokens, a.y, a.claim, a.aboveClip)) == some (some (1, 63), true, .policy, 62)

/-! ## Endings before any stage -/

#guard (CallEnd.policy .differs).lastLine == "NO: policy" && (CallEnd.policy .differs).status == 1
#guard (CallEnd.no "cp-entry-missing").lastLine == "NO: cp-entry-missing"
#guard (CallEnd.unreadable .proof).lastLine ==
  "input-unreadable-proof: the proof file cannot be read"
#guard (CallEnd.unreadable .proof).status == 2
#guard (CallEnd.notChecked "internal-stage").status == 5 && (CallEnd.usage "").status == 2

/-! ## The result of a stage -/

-- The conditions' names come in their fixed order.
#guard servedForm ⟨true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, false, false, false, false, false, true, true⟩ ==
  ["norm-shifts", "reading-as-printed", "two-codes", "record-one-answer", "next-token"]
#guard lastLine false false [] 22 0 == .passed
#guard lastLine false false [] 31 0 == .no "internal-last-line"
#guard lastLine true false ["attention"] 22 0 == .notVer ["profile-below-4", "attention"]

/-- Every condition of the standard parameter form is met but exact-match. -/
def exactMatchMissed : Served :=
  ⟨true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, false, true⟩

-- Then the stage is not a verification, and so is the call. Had the stage passed, the call would
-- end as not checked, since it names no policy.
#guard servedForm exactMatchMissed == ["exact-match"]
#guard lastLine false false (servedForm exactMatchMissed) 22 0 == .notVer ["exact-match"]
#guard (cpStagesRun [passedStage .key, passedStage .leaf, { passedStage .request with
      ending := lastLine false false (servedForm exactMatchMissed) 22 0 }]
    none false 128 named (some (request 60 64, gapLines))).status == 14

/-- The names of the twenty-one conditions, in the order of servedForm (verifier/src/vf_common.h).
Where that routine's text goes on in brackets behind a name, the name here ends before them. -/
def conditionNames : List String :=
  ["attention", "routed-experts", "five-limbs", "both-clamps", "prompt-source", "placement-table",
   "table-digests", "no-range-words", "three-bytes", "ring-degree", "one-shift", "one-placement",
   "softmax-table", "rotary-table", "norm-shifts", "reading-as-printed", "two-codes",
   "record-one-answer", "next-token", "exact-match", "policy-named"]

/-- Every condition is met but the one at place i, counted from 0. From 21 on all are met. -/
def oneMissed (i : Nat) : Served :=
  ⟨i != 0, i != 1, i != 2, i != 3, i != 4, i != 5, i != 6, i != 7, i != 8, i != 9, i != 10,
    i != 11, i != 12, i != 13, i != 14, i != 15, i != 16, i != 17, i != 18, i != 19, i != 20⟩

#guard conditionNames.length == 21
-- All are missed: every name, in that order. All are met: no name.
#guard servedForm ⟨false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false⟩ == conditionNames
#guard servedForm (oneMissed 21) == []
-- One is missed: its name alone, and the stage is not a verification. None is missed: it passes.
#guard (List.range 21).all fun i => servedForm (oneMissed i) == (conditionNames.drop i).take 1
#guard (List.range 21).all fun i =>
  lastLine false false (servedForm (oneMissed i)) 22 0 == .notVer ((conditionNames.drop i).take 1)
#guard lastLine false false (servedForm (oneMissed 21)) 22 0 == .passed

end OnBytes.Model.Stages

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestStagesMore.lean: further tests of OnBytes/Model/Stages.lean.

A test that expects a refusal gives an input that meets every other condition of the function under
test, so that this one condition decides. An input that meets all of them is beside it or in
OnBytes/Model/TestStages.lean, whose records are used here. Each test is checked when the file
compiles. The program does not import this file.
-/
import OnBytes.Model.TestStages

namespace OnBytes.Model.Stages.TestMore

-- goodEnding: each of the three alone
#guard goodEnding false false false
#guard !goodEnding true false false
#guard !goodEnding false true false
#guard !goodEnding false false true
-- lastLine: the ranges of the two lines, each edge alone
#guard lastLine false false [] lidbSealed 0 == .passed
#guard lastLine false false [] lidbMost nminHMost == .passed
#guard lastLine false false [] (lidbSealed - 1) 0 == .no "internal-last-line"
#guard lastLine false false [] (lidbMost + 1) 0 == .no "internal-last-line"
#guard lastLine false false [] lidbSealed (nminHMost + 1) == .no "internal-last-line"
-- firstNo: a refusal without a name is passed over, as an internal one is
#guard (firstNo [{ passedStage .key with ending := .no "" },
  { passedStage .leaf with ending := .no "entry-refused" }]).map (fun x => (x.1.name, x.2)) ==
  some (.leaf, "entry-refused")
#guard (firstNo [{ passedStage .key with ending := .no "internal-x" },
  { passedStage .leaf with ending := .no "entry-refused" }]).map (fun x => (x.1.name, x.2)) ==
  some (.leaf, "entry-refused")
-- stageFault: a note on work with 0 bits, and with one bit too many
#guard stageFault 128 false { passedStage .key with work := some ⟨9602, 1, ""⟩ } == none
#guard stageFault 128 false { passedStage .key with work := some ⟨9602, workMost, ""⟩ } == none
#guard stageFault 128 false { passedStage .key with work := some ⟨9602, 0, ""⟩ } ==
  some "internal-stage"
#guard stageFault 128 false { passedStage .key with work := some ⟨9602, workMost + 1, ""⟩ } ==
  some "internal-stage"

/-- A record with work: 96.02 bits without it, 32 bits of work. -/
def withWork : Acct := { target := 128, needsWork := true, centibits := 9602, work := 32 }

-- workFits: each of the four conditions alone
#guard workFits (some ⟨9602, 32, ""⟩) (some withWork)
#guard workFits (some ⟨9603, 32, ""⟩) (some withWork)
#guard workFits (some ⟨9601, 32, ""⟩) (some withWork)
#guard !workFits (some ⟨9602, 32, ""⟩) (some { withWork with needsWork := false })
#guard !workFits (some ⟨9604, 32, ""⟩) (some withWork)
#guard !workFits (some ⟨9600, 32, ""⟩) (some withWork)
#guard !workFits (some ⟨9602, 31, ""⟩) (some withWork)
-- cpStagesRun: a stage with another ID than the first's, which is the caller's
#guard cpStagesRun [passedStage .key, passedStage .leaf,
  { passedStage .request with idHex := String.ofList (List.replicate 64 'b') }] none false 128 named
  next == .notChecked "internal-id-two-ways"
-- an ID that was not named
#guard cpStagesRun allPassed none false 128 { asked := someId, named := false } next ==
  .notChecked "internal-id-two-ways"
-- an ID that is not needed and not named costs nothing
#guard (cpStagesRun [passedStage .key] (some .key) false 128 { needed := false } none).lastLine ==
  "PART PASSED: key"
-- fewer bits than the threshold, and no other cause
#guard (cpStagesRun allPassed none true 64 named next).lastLine == "NOT-A-VERIFICATION"

end OnBytes.Model.Stages.TestMore

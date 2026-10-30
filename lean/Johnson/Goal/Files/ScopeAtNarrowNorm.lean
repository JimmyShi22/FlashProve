-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Files/ScopeAtNarrowNorm.lean: tests by evaluation: two sets of public files whose final
normalisation has MF ≤ KF + 11 are in scope of the goals (`InScope`, Ladder.lean), and so is a third
that also states a policy with theta < C and cap = 0. Lean's evaluator runs the tests whenever this
file is compiled. They are evaluations, not proofs checked by the kernel (the head of
Ladder/Guards.lean says what an evaluation trusts). Five helper definitions for the tests; no
theorem; no goal is stated.

Why. MF and KF are the lines of these names in a parameter file: the two exponents of the final
normalisation. Policy/Front/MeetsPolicyIdleAtScales.lean bounds a token's gap at all valid settings
by a ceiling that depends on MF - KF alone. Where MF ≤ KF + 11 the ceiling is below 2^32, and at a
difference of 12 it is above. Where MF ≤ KF + 11 there is a policy with theta < C < 2^32 and cap = 0
that, whatever the weights, "excludes no output by its scores", in that file's words
(`exists_policy_of_close_scales`). That says something of files in scope only if some file in scope
has such numbers. The stored files have MF = 44 and KF = 30: a difference of 14. Ladder/Guards.lean
shows that some other MF is in scope; this file names values.
Policy/Front/MeetsPolicyIdleAtScales.lean is not imported here, and nothing here checks what is said
of it. No Lean statement joins that file and this one: that its theorems apply at what the reader
returns at these files follows by hand, from these tests, `valid_of_read` (Ladder/Ties.lean) and the
definitions (the settings' `finalBits` and `finalShift` are MF and KF).

The tests. Each takes the stored full-size files, writes MF (a difference of 11) or MF and KF (a
difference of 7) anew in the parameter file, and checks that the files are in scope and that the
reader returns the two numbers as written. One more writes, beside MF = 41, the policy (C, theta,
cap) = (4294967295, 2436593409, 0), which is the one of `exists_policy_of_close_scales` in the file
named above (2436593409 is 2^8 plus that file's ceiling at a difference of 11, at the width 5,120
and 13-bit weights in the output matrix), and checks that the files are in scope and that the reader
returns MF, KF and these three numbers as written: so one set of files in scope is shown that STATES
such a policy, where the two others state exact match. Controls: the stored numbers must be in
scope. MF = 45 beside KF = 30 (a difference of 15) must not, while the same MF beside KF = 31 (14)
must: so it is the difference that is refused (`NormPar.OK`, Inst/Model/Program.lean), not the size
of MF. MF = 23 beside KF = 17 must not, while MF = 24 must. Both refusals are the reader's own
("scales-not-lawful"), which names no number.

Limits. Evaluation only: `Read.scope_of_check` (Ladder/FilesReadLaws.lean) cannot prove scope here,
because `CheckKL` asks for the reference's final normalisation. The pairs are test values: whether a
table fitted to a model has MF ≤ KF + 11 is not said. But for the control at the stored numbers,
which is `storedPublicFiles` itself, these files are not among the two named sets: the goal on
acceptance (`G3'pol`) asks nothing at them, the goals on soundness and binding speak of them as of
all
files in scope (the goals at exact match, such as `G7`, say nothing of the set that states another
policy), and no goal takes these tests as a premise. Their settings are not `settingsOf Cm.sRef` (by
the definitions: MF and KF are fields of the settings; not tested here), so
Johnson/Goal/Files/FilesReadAtRef.lean does not apply to them: what is proved at the reference
scales and what is proved for MF ≤ KF + 11 meet at no files, since the reference's difference is 14.
The scale file and the layout file are the stored ones. Whether the tests on the public files that
`VerifierAndGoals.theDescription` makes (`FlashProve.protocolDataWellFormed`, Johnson/Goal/Description/Live.lean) pass at
these files has not been evaluated.

-/
import Ladder.Guards

namespace VerifierAndGoals.NarrowNorm

/-- The final normalisation's two numbers (MF, KF) as the reader returns them. For the tests
below. -/
def normRead (Z : PublicFiles) : Option (Nat × Nat) :=
  match readFiles Z with
  | .ok pp => some (pp.nf.M, pp.nf.K)
  | .error _ => none

/-- The policy's three numbers (C, theta, cap) as the reader returns them. For the tests below. -/
def polRead (Z : PublicFiles) : Option (Nat × Nat × Nat) :=
  match readFiles Z with
  | .ok pp => some (pp.pol.C, pp.pol.theta, pp.pol.cap)
  | .error _ => none

/-- The reader's message where it refuses the files. For the tests below. -/
def refusal (Z : PublicFiles) : Option String :=
  match readFiles Z with
  | .ok _ => none
  | .error e => some e

/-- The stored full-size files with MF and KF written anew in the parameter file. For the tests
below. -/
def atNorm (MF KF : Nat) : PublicFiles :=
  { storedPublicFiles with pol := policyFile { storedLines with MF := MF, KF := KF } }

/-- The stored full-size files with MF = 41 and the policy (4294967295, 2436593409, 0) written anew
in the parameter file. For the tests below. -/
def atIdle : PublicFiles :=
  { storedPublicFiles with
    pol := policyFile
      { storedLines with MF := 41, C := 4294967295, theta := 2436593409, cap := 0 } }

-- The stored numbers, as a control on the helpers.
#guard InScope (atNorm 44 30) && normRead (atNorm 44 30) == some (44, 30)
-- A difference of 11: MF alone is written anew.
#guard InScope (atNorm 41 30) && normRead (atNorm 41 30) == some (41, 30)
-- The same with a policy written anew as well: theta < C < 2^32 and cap = 0.
#guard InScope atIdle && normRead atIdle == some (41, 30) &&
  polRead atIdle == some (4294967295, 2436593409, 0)
-- A difference of 7, at the low end of both.
#guard InScope (atNorm 24 17) && normRead (atNorm 24 17) == some (24, 17)
-- A difference of 15 is out of scope; the same MF at a difference of 14 is in scope.
#guard !InScope (atNorm 45 30) && refusal (atNorm 45 30) == some "scales-not-lawful"
#guard InScope (atNorm 45 31) && normRead (atNorm 45 31) == some (45, 31)
-- MF = 23 is out of scope.
#guard !InScope (atNorm 23 17) && refusal (atNorm 23 17) == some "scales-not-lawful"

end VerifierAndGoals.NarrowNorm

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyLengths.lean: tests of what readCall (OnBytes/Model/VerifyHeads.lean) does
with the lengths of the request and of the reply: under a parameter file that has a line lt, under
one whose line lt gives no number or is missing, and beside a fault that an earlier test finds. Some
guards are controls on the parameter files (valueLines, Params.readLines, Config.polWord). One guard
at the end is on cpPolicyHeld instead, on lines and a request of its own: how a line of the policy
is read.

The parameter file is the small example of OnBytes/Model/TestConfig.lean. Its line lt is 6: a
request has 64 tokens and two words more, 264 bytes. That line is also replaced or taken out, and
once the first line is replaced. The scale file is the example's too, but for one guard, and there
is no layout file. The request, the reply and the proof are zero bytes of a given length, or cannot
be read. The key file is a right header and no more, but for two guards. A proof file of twelve zero
bytes is refused for its header. That end shows that the tests before it have passed. The expected
ends are read off the C++ source (cpMain, cpLengthHeld, polWord, cpPolicySays, cpPolicyHeld,
cpPolicyWord, verifier/src/cp_verify.cpp; verifier/src/vf_input_files.h; verifier/src/vf_common.h;
blocks/frame/version.h; blocks/frame/parameters.h); no guard compares with a run of it.

Whence the numbers and strings come. All were typed by hand. None was copied from a program's
output, and none is taken from a key, an entry, a proof or a model's weights. Given by something
else: lt 6 and prof 20 are the example's own lines, lt 6 at index 1 of its value lines, and 264 = 4
(2^6 + 2) follows from it; the 1 of drop 1 is the frame's first line, version H821, which is left
out; 4 bytes are the reply's one word; 12 bytes are a proof's header and 8 a key's; 20 is the bound
on lt in cpMain and 21 is one above it, whence the lines lt 20 and lt 21, and 4 (2^20 + 2) follows
from 20; 129 requested bits are one above 128, half a digest's bits (hashLeast; DIGEST_HALF_BITS,
verifier/src/vf_common.h); H811 is one character away from the served version's word H821
(blocks/frame/version.h). The other lengths are wrong ones: a word more or less (268, 260, 8), a
byte more (265, 5), none (0), and three zero bytes for a scale file. The four other forms of the
line lt were chosen for what polWord does with them: lt 06 has a leading zero and gives 6; lt 6
with a blank behind it, lt 6a and lt 12345678901 give no number. The named policy (300, 299, 0, 15,
8) has the example's cap, s and sh and another C and theta than the example's 256 and 256. Its
numbers pass the test on a named policy by themselves; those of a second one (255, 255, 0, 15, 8) do
not: 255 is one below 2^sh. The last guard has the numbers of a guard of
OnBytes/Model/TestVerifyHeads.lean: a C of eleven digits (12345678901), there for its length alone,
five more lines of a policy (299, 0, 15, 8, 15), a request of eight tokens 0 with r = 7 and e = 8;
and behind them a line C 300. The strings are the seven forms of the line lt (lt 6, lt 20, lt 21 and
these four), the line C 300, the first line version H811, the names lt and prof, an ID of two
digits, a kind of policy, the words of a bad command line on the ID, and names of refusals of the
C++ verifier.
What the example's two files are is said in OnBytes/Model/TestConfig.lean.

Each test is checked when the file compiles. The file is no part of the program.
-/
import OnBytes.Model.TestConfig
import OnBytes.Model.TestVerifyHeads

namespace OnBytes.Model.TestVerifyLengths

open Verify Stages

/-- The example's parameter file with another line in the place of its line lt. -/
def policyWith (lt : String) : ByteArray :=
  TestConfig.withLines (TestConfig.setLine TestConfig.valueLines 1 lt) TestConfig.optionalLines
    TestConfig.callLines

/-- The files of a whole call. lt: the parameter file's line lt. request, y, proof: the length of
the file in bytes, or none for a file that cannot be read. -/
def files (lt : String) (request y : Option Nat) (proof : Option Nat := some 12) : Files :=
  { policy := some (policyWith lt)
    KL := some TestConfig.klFile
    layout := none
    key := some (Proof.FileKind.key.tag ++ servedVersion)
    request := request.map Fmt.zeroBytes
    y := y.map Fmt.zeroBytes
    proof := proof.map Fmt.zeroBytes }

/-- The end that readCall gives to a call, if it ends it. -/
def endOf (f : Files) (o : Options := {}) : Option CallEnd :=
  match readCall o f with
  | .error e => some e
  | .ok _ => none

-- the line that is replaced is the line lt
#guard TestConfig.valueLines[1]? == some "lt 6"
-- right lengths: the call gets as far as the proof's header
#guard endOf (files "lt 6" (some 264) (some 4)) == some (.no "cp-proof-head")

/-! ## A wrong length, by itself -/

#guard endOf (files "lt 6" (some 268) (some 4)) == some (.no "statement-range")
#guard endOf (files "lt 6" (some 260) (some 4)) == some (.no "statement-range")
#guard endOf (files "lt 6" (some 265) (some 4)) == some (.no "statement-required")
#guard endOf (files "lt 6" (some 0) (some 4)) == some (.no "statement-required")
#guard endOf (files "lt 6" (some 264) (some 8)) == some (.no "statement-range")
#guard endOf (files "lt 6" (some 264) (some 5)) == some (.no "statement-required")
#guard endOf (files "lt 6" (some 264) (some 0)) == some (.no "statement-required")

/-! ## A wrong length comes before an unreadable request, reply or proof; request before reply -/

#guard endOf (files "lt 6" (some 268) none) == some (.no "statement-range")
#guard endOf (files "lt 6" (some 268) (some 4) none) == some (.no "statement-range")
#guard endOf (files "lt 6" none (some 8)) == some (.no "statement-range")
#guard endOf (files "lt 6" (some 268) (some 5)) == some (.no "statement-range")
-- with right lengths the file that cannot be read ends the call
#guard endOf (files "lt 6" (some 264) none) == some (.unreadable .y)
#guard endOf (files "lt 6" none (some 4)) == some (.unreadable .request)
#guard endOf (files "lt 6" (some 264) (some 4) none) == some (.unreadable .proof)

/-! ## A wrong length of the request comes before the comparison of the policies -/

/-- A call that names a policy other than the example's. -/
def otherPolicy : Options := { policy := some ⟨"clipped-gap", 300, 299, 0, 15, 8⟩ }

#guard endOf (files "lt 6" (some 264) (some 4)) otherPolicy == some (.policy .differs)
#guard endOf (files "lt 6" (some 268) (some 4)) otherPolicy == some (.no "statement-range")

/-! ## The request's length is tested only up to lt 20 -/

#guard endOf (files "lt 20" (some 264) (some 4)) == some (.no "statement-range")
#guard endOf (files "lt 20" (some (4 * (2 ^ 20 + 2))) (some 4)) == some (.no "cp-proof-head")
-- above 20 there is no test on the request here, and the reply's stays
#guard endOf (files "lt 21" (some 264) (some 4)) == some (.no "cp-proof-head")
#guard endOf (files "lt 21" (some 264) (some 8)) == some (.no "statement-range")

/-! ## A line lt that gives no number, or no line lt: the request's length is not tested here -/

/-- The files of `files "lt 6"` with another parameter file. -/
def filesOn (pol : ByteArray) (request y : Option Nat) : Files :=
  { files "lt 6" request y with policy := some pol }

/-- The example's parameter file without its line lt. -/
def policyWithoutLt : ByteArray :=
  TestConfig.withLines (TestConfig.valueLines.filter (· != "lt 6")) TestConfig.optionalLines
    TestConfig.callLines

-- the frame of that file is accepted and another line is read, so it is the line lt that is missing
#guard (Params.readLines policyWithoutLt).toOption.isSome
#guard Config.polWord policyWithoutLt "prof" == some 20
#guard Config.polWord policyWithoutLt "lt" == none
#guard endOf (filesOn policyWithoutLt (some 268) (some 4)) == some (.no "cp-proof-head")
#guard endOf (filesOn policyWithoutLt (some 268) (some 8)) == some (.no "statement-range")
-- a leading zero is read: lt 06 is 6, and the test is made
#guard endOf (files "lt 06" (some 264) (some 4)) == some (.no "cp-proof-head")
#guard endOf (files "lt 06" (some 268) (some 4)) == some (.no "statement-range")
-- a blank behind the digit, a letter, eleven digits: no number, and no test on the request
#guard ["lt 6 ", "lt 6a", "lt 12345678901"].all fun l =>
  endOf (files l (some 268) (some 4)) == some (.no "cp-proof-head")
-- what polWord gives for these forms: by its end alone, eleven digits could be a number above 20
#guard Config.polWord (policyWith "lt 06") "lt" == some 6
#guard ["lt 6 ", "lt 6a", "lt 12345678901"].all fun l => Config.polWord (policyWith l) "lt" == none

/-! ## An earlier test comes before a wrong length -/

/-- A whole call whose request is a word too long. -/
def long : Files := files "lt 6" (some 268) (some 4)

/-- The example's parameter file with another first line. -/
def policyOfVersion (line : String) : ByteArray :=
  TestConfig.fileOf (line :: TestConfig.frameLines.drop 1 ++ TestConfig.valueLines ++
    TestConfig.optionalLines ++ TestConfig.callLines)

#guard endOf long == some (.no "statement-range")
#guard endOf long { id := some "12" } == some (.usage "-id requires 64 hex digits")
#guard endOf long { bits := 129 } == some (.no "cp-bits-above-digest")
#guard endOf long { policy := some ⟨"clipped-gap", 255, 255, 0, 15, 8⟩ } ==
  some (.policy .clipBelowLeast)
#guard endOf { long with KL := some ⟨#[0, 0, 0]⟩ } == some (.no "KL-length")
#guard endOf { long with key := none } == some (.unreadable .key)
#guard endOf { long with policy := some (policyOfVersion "version H811") } ==
  some (.no "version-of-another-field (policy)")
#guard endOf { long with key := some (Fmt.zeroBytes 8) } == some (.no "cp-key-head")

/-! ## How the policy's lines are read: a value that is no value, and a later line of that name -/

-- a value of eleven digits is no value, and no later line C is looked at: with a C that is read
-- these lines end as fileKind (OnBytes/Model/TestVerifyHeads.lean)
#guard heldEnd none (policyLines 12345678901 299 0 15 8 15 ++ "C 300\n".toUTF8) (requestOf 7 8) ==
  none

end OnBytes.Model.TestVerifyLengths

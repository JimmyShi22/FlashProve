-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/TestRecordToyStrictCopies.lean: the second compiler's strict verifier of the link on
altered copies of the programs' toy entry file, on the honest file under another first root, and on
the stored file with two openings swapped; behind the lenient converter, so that a damaged file can
reach the verifier.
What is expected, and why. The twelve copies, with the names that the programs' table holds for
them: OnBytes/Entry/TestRecordToy.lean.
A byte of an opening turned: copies 06, 07, 09 (held name "reader-opening"), and byte 1000 of the
file. That byte lies in the first table's opening, which begins at byte 352, behind the nonce of the
round LINK: an opening holds, for each opened position, the column and its salt, then the given
digests (R7.8); here a column has 8 words of 8 bytes and a salt 40 bytes, and 1000 = 352 + 6 · 104 +
24 is the first byte of the fourth word of the seventh column (the opening has more than seven: its
length is held in OnBytes/Entry/TestRecordToySplice.lean). No opening enters the hash chain: so the
lenient converter cuts the file at the same places and the chain returns; the leaf or the path does
not lead to its root. Held: the first line that says no is "after 3". Nothing in front of "after 5"
reads the decision. At byte 1000 the root is the one read off the key file.
A byte turned that enters the hash chain in front of a draw of positions (the copy's root, the
random bytes, a root, an answer: copies 03, 04, 05, 12; the first table's root): the draws move, and
whether the file can then be cut depends on the bytes. Copy 08, for which the programs' table and
the port name different checks, stands with them; in which part of the file its byte lies is not
held. Held: the run does not end in "yes", with the decision and with the decision taken out. Not
held: at which stage it ends; so these guards do not show that the compiled verifier is reached.
The head, a byte cut, a byte added (01, 02, 10, 11): "converter".
The two tables' openings swapped as blocks of bytes (bentSwap): behind the strict converter:
"converter"; behind the lenient one: not "yes", with the decision and with the decision taken out;
at which stage is not held.
What is run, what the stages' names and the two switches mean, and what is not claimed:
Johnson/RunOne/TestRecordToyStrict.lean's head.
-/
import Johnson.RunOne.TestRecordToyStrict

set_option autoImplicit false

namespace Johnson.RunOne.RecordToyStrict
open OnBytes OnBytes.Entry.RecordToy

/-- The copy of that number. -/
def copyOf (n : String) : Option ByteArray := (copies.find? fun c => c.1 == n).map (·.2.1)

/-- The endings of the copies of these numbers, behind the lenient converter. -/
def endingsOf (noDecision : Bool) (ns : List String) : List (Option String) :=
  ns.map fun n => (copyOf n).bind (voice true noDecision)

/-- The run has ended, and not in "yes". -/
def refused (e : Option String) : Bool := e.isSome && e != some "yes"

end Johnson.RunOne.RecordToyStrict

open Johnson.RunOne.RecordToyStrict OnBytes.Entry.RecordToy

#guard endingsOf false ["06", "07", "09"] == [some "after 3", some "after 3", some "after 3"]
-- a byte of the first table's opening
#guard voice true false (flipAt entryFile 1000) == some "after 3"
#guard (endingsOf false ["03", "04", "05", "08", "12"]).all refused &&
  (endingsOf true ["03", "04", "05", "08", "12"]).all refused
#guard endingsOf false ["01", "02", "10", "11"] == List.replicate 4 (some "converter")
-- the honest entry under another first root
#guard [false, true].all fun nd => refused (firstTable.map fun t =>
  (endingAt id true nd { t with root := flipAt t.root 0 } entryFile).1)
-- two openings swapped
#guard [false, true].all fun nd => refused (voice true nd Fmt.MustBeRefused.RecordToy.bentSwap)
#guard voice false false Fmt.MustBeRefused.RecordToy.bentSwap == some "converter"

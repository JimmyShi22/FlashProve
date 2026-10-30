-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/TestRecordToy.lean: Key.check on the toy key file of OnBytes/Entry/RecordToyFiles.lean:
the honest file says yes; twelve altered copies, each made here by a recipe from the honest bytes,
are refused.

The recipes and the table are as in OnBytes/Entry/TestRecordToy.lean. At copies 06, 07 and 08 the
programs' reader says that the linear claim fails, and this one that a proof of work fails: these
copies are held to be refused, and their names are not asserted.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Entry.TestRecordToy

namespace OnBytes.Entry.RecordToy

/-- How Key.check ends: "yes", or the refusal's name. -/
def keyEnding (file : ByteArray) : Option String :=
  chains.map fun k =>
    match Key.check k file with
    | .ok _ => "yes"
    | .error r => r.check

/-- The altered copies of the key file. -/
def keyCopies : List (String × ByteArray × Option String) :=
  [("01", flipAt keyFile 0, some "file-of-another-kind"),
   ("02", flipAt keyFile 4, some "version-unknown"),
   ("03", flipAt keyFile 8, some "one-time-chain-reader-work"),
   ("04", flipAt keyFile 232, some "one-time-chain-reader-work"),
   ("05", flipAt keyFile 264, some "one-time-chain-reader-work"),
   ("06", flipAt keyFile 125936, none),
   ("07", flipAt keyFile 251872, none),
   ("08", flipAt keyFile 377808, none),
   ("09", flipAt keyFile 503743, some "second-chain-reader-opening"),
   ("10", keyFile.extract 0 (keyFile.size - 1), some "second-chain-reader-form"),
   ("11", keyFile.push 0, some "bytes-left-over"),
   ("12", flipAt keyFile 40, some "one-time-chain-reader-work")]

/-- Refused, and by the held name if there is one. -/
def keyAsHeld (c : String × ByteArray × Option String) : Bool :=
  match keyEnding c.2.1, c.2.2 with
  | some "yes", _ => false
  | none, _ => false
  | some n, some m => n == m
  | some _, none => true

#guard keyEnding keyFile == some "yes"
#guard keyCopies.length == 12
#guard (keyCopies.filter fun c => !keyAsHeld c).map (·.1) == []

end OnBytes.Entry.RecordToy

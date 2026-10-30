-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestRecordToy.lean: Entry.check on the toy entry file of
OnBytes/Entry/RecordToyFiles.lean: the honest file says yes; twelve altered copies, each made here
by a recipe from the honest bytes, are refused.

The recipes are the copies that blocks/frame/handover_files.cpp writes, read off byte by byte: bit 0
of one named byte turned, the last byte cut off, a zero byte added. Its table altered.tsv names what
the programs' reader says of each copy. A refusal's name is held here where it says the same thing
as that table. At copy 08 the programs' reader says that the linear claim fails, and this one that a
proof of work fails: that copy is held to be refused, and its name is not asserted.

Further: the honest entry under a first table whose root has bit 0 turned, and the stored false
entries of Fmt/MustBeRefused/RecordToy.lean.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Entry.File
import OnBytes.Key.File
import OnBytes.Entry.RecordToyFiles
import Fmt.MustBeRefused.RecordToy

namespace OnBytes.Entry.RecordToy

/-- Bit 0 of byte n turned. -/
def flipAt (b : ByteArray) (n : Nat) : ByteArray := b.set! n (b.get! n ^^^ 1)

/-- The key file's chains. -/
def chains : Option Params.KeyChains :=
  Params.KeyChains.read oneTimeParameters sharedParameters secondParameters

/-- What a reader keeps of the first table: the head of the key file, before its chains. -/
def firstTable : Option Params.TableName :=
  chains.bind fun k =>
    match Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg keyFile with
    | .ok x => some x.1
    | .error _ => none

/-- How Entry.check ends: "yes", or the refusal's name. -/
def ending (file : ByteArray) : Option String :=
  firstTable.map fun t =>
    match Entry.check entryParameters t file with
    | .ok _ => "yes"
    | .error r => r.check

/-- The altered copies: number, bytes, the name that is held, none where no name is. -/
def copies : List (String × ByteArray × Option String) :=
  [("01", flipAt entryFile 0, some "file-of-another-kind"),
   ("02", flipAt entryFile 4, some "version-unknown"),
   ("03", flipAt entryFile 8, some "reader-work"),
   ("04", flipAt entryFile 232, some "reader-work"),
   ("05", flipAt entryFile 264, some "reader-work"),
   ("06", flipAt entryFile 32858, some "reader-opening"),
   ("07", flipAt entryFile 65716, some "reader-opening"),
   ("08", flipAt entryFile 98574, none),
   ("09", flipAt entryFile 131431, some "reader-opening"),
   ("10", entryFile.extract 0 (entryFile.size - 1), some "reader-form"),
   ("11", entryFile.push 0, some "bytes-left-over"),
   ("12", flipAt entryFile 40, some "reader-work")]

/-- Refused, and by the held name if there is one. -/
def asHeld (c : String × ByteArray × Option String) : Bool :=
  match ending c.2.1, c.2.2 with
  | some "yes", _ => false
  | none, _ => false
  | some n, some m => n == m
  | some _, none => true

#guard entryFile.size == 131432 && keyFile.size == 503744
#guard copies.length == 12
#guard ending entryFile == some "yes"
#guard (copies.filter fun c => !asHeld c).map (·.1) == []
-- the honest entry under another first table: refused
#guard (firstTable.map fun t =>
  match Entry.check entryParameters { t with root := flipAt t.root 0 } entryFile with
  | .ok _ => false
  | .error _ => true) == some true
-- the stored false entries
#guard ending Fmt.MustBeRefused.RecordToy.bentSwap == some "reader-opening"
#guard ending Fmt.MustBeRefused.RecordToy.linkOneCell == some "decision-linear-claim"
#guard ending Fmt.MustBeRefused.RecordToy.baseWrongWord == some "decision-symbols-at-positions"
#guard ending Fmt.MustBeRefused.RecordToy.foldeqOtherRow == some "decision-linear-claim"
#guard ending Fmt.MustBeRefused.RecordToy.linkFarTable == some "decision-linear-claim"
#guard ending Fmt.MustBeRefused.RecordToy.linkOtherCopyRow == some "decision-linear-claim"
#guard ending Fmt.MustBeRefused.RecordToy.linkOtherCopyTail == some "decision-linear-claim"
#guard ending Fmt.MustBeRefused.RecordToy.linkShortCut == some "decision-linear-claim"

end OnBytes.Entry.RecordToy

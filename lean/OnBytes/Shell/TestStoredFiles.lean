-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/TestStoredFiles.lean: what the program's checks answer on the files that are stored in
this library, and that they refuse, by name, public files whose tables have no out-of-domain sample.

The functions are those that the program verify-on-bytes calls: `Shell.key` and `Shell.entry`
(OnBytes/Shell/Toys.lean), which derive every chain's parameter bytes from the two public files, and
three of the four checks of `Shell.frontChecks` (OnBytes/Shell/Front.lean).

1. The toy of OnBytes/Entry/RecordToyFiles.lean, under its two public files: the honest key and
   entry; the twelve altered copies of each, made by the recipes of
   OnBytes/Entry/TestRecordToy.lean and OnBytes/Key/TestRecordToy.lean; the eight stored entries of
   Fmt/MustBeRefused/RecordToy.lean. For each file the verdict and the refusal's name.
2. The toy's first public file with the line "answers 0", with "record 0", and with both: both calls
   refuse, under the name "parameters-not-admitted".
3. The small parameter file of OnBytes/Model/TestRecordWork.lean with the same three changes: the
   plan and the calls on a key file and on an entry file alone refuse, under the name
   "parameter-range (policy)". Under the unchanged file the plan has seven chains, and the two calls
   get as far as the files: they refuse the toy's key and entry, which are none of these public
   files', as "key-refused" and "entry-refused".

Where the names come from. They are this library's own names for its checks. The test holds them
fast, so that a change of the code that is meant to change no answer can be seen to change none. It
is no comparison with the C++ programs. Where the programs' own tables say the same thing of a file,
that is held in the two test files named under 1; at the key's copies 06, 07 and 08 and at the
entry's copy 08 the programs' reader names another check, as the heads of these two files say.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. No key, entry, request or proof of a model is stored in this library: so
the whole call is not tried, and under 3 no file passes a stage. The call on a test batch's proof
files is not tried here. Nothing on the compiled program: the tests are evaluated by Lean when this
file compiles. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Shell.Front
import OnBytes.Key.TestRecordToy
import OnBytes.Model.TestRecordWork

namespace OnBytes.ShellTest.StoredFiles

open OnBytes.Shell
open OnBytes.Entry.RecordToy

/-- A verdict in a word: "yes", or the refusal's name. -/
def said : Verdict → String
  | .accepted => "yes"
  | .refused r => r.check

/-- What the call `key` says of a key file under the toy's public files. -/
def keySaid (file : ByteArray) (first : ByteArray := publicFileOne) : String :=
  said (key 128 first publicFileTwo file)

/-- What the call `entry` says of an entry file under the toy's public files and honest key. -/
def entrySaid (file : ByteArray) (first : ByteArray := publicFileOne) : String :=
  said (entry 128 first publicFileTwo keyFile file)

-- the honest files
#guard keySaid keyFile == "yes"
#guard entrySaid entryFile == "yes"

-- the twelve altered copies of the key file
#guard keyCopies.map (fun c => (c.1, keySaid c.2.1)) ==
  [("01", "file-of-another-kind"), ("02", "version-unknown"),
   ("03", "one-time-chain-reader-work"), ("04", "one-time-chain-reader-work"),
   ("05", "one-time-chain-reader-work"), ("06", "one-time-chain-reader-work"),
   ("07", "shared-chain-reader-work"), ("08", "shared-chain-reader-work"),
   ("09", "second-chain-reader-opening"), ("10", "second-chain-reader-form"),
   ("11", "bytes-left-over"), ("12", "one-time-chain-reader-work")]

-- the twelve altered copies of the entry file
#guard copies.map (fun c => (c.1, entrySaid c.2.1)) ==
  [("01", "file-of-another-kind"), ("02", "version-unknown"), ("03", "reader-work"),
   ("04", "reader-work"), ("05", "reader-work"), ("06", "reader-opening"),
   ("07", "reader-opening"), ("08", "reader-work"), ("09", "reader-opening"),
   ("10", "reader-form"), ("11", "bytes-left-over"), ("12", "reader-work")]

-- the eight stored entries that must be refused
#guard [Fmt.MustBeRefused.RecordToy.bentSwap, Fmt.MustBeRefused.RecordToy.linkOneCell,
    Fmt.MustBeRefused.RecordToy.baseWrongWord, Fmt.MustBeRefused.RecordToy.foldeqOtherRow,
    Fmt.MustBeRefused.RecordToy.linkFarTable, Fmt.MustBeRefused.RecordToy.linkOtherCopyRow,
    Fmt.MustBeRefused.RecordToy.linkOtherCopyTail, Fmt.MustBeRefused.RecordToy.linkShortCut].map
      (entrySaid ·) ==
  ["reader-opening", "decision-linear-claim", "decision-symbols-at-positions",
   "decision-linear-claim", "decision-linear-claim", "decision-linear-claim",
   "decision-linear-claim", "decision-linear-claim"]

/-- The bytes of a text file with some whole lines replaced. -/
def withLines (file : ByteArray) (pairs : List (String × String)) : ByteArray :=
  ("\n".intercalate (((String.fromUTF8? file).getD "").splitOn "\n" |>.map fun l =>
    (pairs.lookup l).getD l)).toUTF8

/-- The three changes: no answer; no record; neither. -/
def changes : List (List (String × String)) :=
  [[("answers 1", "answers 0")], [("record 1", "record 0")],
   [("answers 1", "answers 0"), ("record 1", "record 0")]]

-- each change turns the toy's first public file, and the file without a change comes back as it was
#guard changes.all fun c => withLines publicFileOne c != publicFileOne
#guard withLines publicFileOne [] == publicFileOne

-- the toy's public file without a sample: refused by name, by both calls
#guard changes.map (fun c => (keySaid keyFile (withLines publicFileOne c),
    entrySaid entryFile (withLines publicFileOne c))) ==
  List.replicate 3 ("parameters-not-admitted", "parameters-not-admitted")

/-- The small parameter file. -/
def policy : ByteArray := Model.Verify.TestRecordWork.policyOf Model.Verify.TestRecordWork.smallHead

/-- The files of a call on a model's files: the three public files, and the toy's key and entry in
the places of a key and an entry. They are no key and no entry of these public files. -/
def filesWith (p : ByteArray) : Model.Verify.Files :=
  { policy := some p, KL := some Params.SmallFiles.scales,
    layout := some (some Params.SmallFiles.layout), key := some keyFile, request := none,
    y := none, proof := none, entry := some entryFile }

/-- The name under which a call refuses, for the endings that are met here. -/
def ended : Model.Stages.CallEnd → String
  | .no name => name
  | .refusedBy _ _ name => name
  | _ => "another ending"

/-- The plan and the two calls on one file alone, under a parameter file. -/
def threeCalls (p : ByteArray) : List String :=
  [match frontChecks.plan 128 (some p) (some Params.SmallFiles.scales)
      (some (some Params.SmallFiles.layout)) with
    | .ok chains => "chains: " ++ toString chains.length
    | .error e => ended e,
   ended (frontChecks.keyCall {} (filesWith p)), ended (frontChecks.leafCall {} (filesWith p))]

#guard changes.all fun c => withLines policy c != policy
-- the parameter file without a sample: refused by name, by all three calls
#guard changes.map (fun c => threeCalls (withLines policy c)) ==
  List.replicate 3 (List.replicate 3 "parameter-range (policy)")
-- under the unchanged parameter file the calls get further
#guard threeCalls policy == ["chains: 7", "key-refused", "entry-refused"]

end OnBytes.ShellTest.StoredFiles

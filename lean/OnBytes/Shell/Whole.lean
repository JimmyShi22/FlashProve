-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Whole.lean: the whole call, which checks one request, the calls on one file alone, and
the planning call.

The whole call has the arguments of the C++ verifier cp_verify (cpMain,
verifier/src/cp_verify.cpp): the configuration folder, the folder with the key file and the entry
files, the request file, the file with the reply, the proof file, and options. The checks are pure
functions of the options and of the files' bytes (`Checks`; the program's are those of
OnBytes/Model/Verify.lean). This file reads the options, says which files are read and in which
order, and prints the result.

What is printed: cp_verify's closing lines and the verdict, and none of its other lines; both are
listed in OnBytes/Shell/Lines.lean. The line `covered:` repeats the numbers r and e of the request,
so that the caller sees which positions the answer is about.

A file that is missing or cannot be read does not end the call in a fault. The checks are told, and
the call ends as in cp_verify: with one line that names the file's role, and the exit code 2, which
is not a verdict. Refused instead: a missing layout.txt, and a whole call's entry that is missing or
cannot be read. All files but the entry are read before the checks; cp_verify checks between reads.
One exception: a y, or under a line lt of at most 20 a request, that is a regular file of a wrong
length and cannot be opened. cp_verify asks for the length first and ends with
`NO: statement-required` or `NO: statement-range`, exit code 1; this program, with exit code 2.
A file above its limit (`fileLimit`, `textLimit`, OnBytes/Shell/Ask.lean) ends the call with
`NO: file-too-long`, a line that cp_verify does not have: it can stand where cp_verify says YES.

The calls on a key file alone and on an entry file alone are cp_verify's part-calls `-key` and
`-leaf`, which are meant for the committer's own test. They never end in a yes: at best they end
with `PART PASSED`.

The planning call checks no proof. It derives the parameter bytes of the seven chains from the three
configuration files and prints a digest of each. cp_verify has no call that prints these lines. The
last line and the exit code 4 are those of its planning calls.

Main definitions: `Checks`, `decimal`, `Asked`, `readOptions`, `earlyEnd`, `whole`, `partEnd`,
`keyPart`, `leafPart`, `planLines`, `planCall`. What is not claimed: no theorem is stated here, and
nothing about the checks themselves.
-/
import OnBytes.Shell.Ask
import OnBytes.Model.VerifyInputs
import OnBytes.Hash.H
import Fmt.Rules4

namespace OnBytes.Shell

open OnBytes.Model
open OnBytes.Model.Stages (CallEnd)

/-- The checks of the calls on a model's files (the whole call, the calls on one file alone and the
planning call), as the shell sees them. -/
structure Checks where
  /-- the names under which these checks refuse -/
  names : List String
  /-- the places of rounds that their notes on work name -/
  places : List String
  /-- the tests that come before the entry is read: the number of the entry that the proof names,
  or the result of the call -/
  entryNumber : Verify.Options → Verify.Files → Except CallEnd Nat
  /-- the whole verdict -/
  wholeCall : Verify.Options → Verify.Files → CallEnd
  /-- the result of a call on a key file alone -/
  keyCall : Verify.Options → Verify.Files → CallEnd
  /-- the result of a call on an entry file alone -/
  leafCall : Verify.Options → Verify.Files → CallEnd
  /-- the parameter bytes of the chains, derived from the requested bits and the three
  configuration files, each with its chain's name; or the result of the call -/
  plan : Nat → Verify.FileIn → Verify.FileIn → Option Verify.FileIn →
    Except CallEnd (List (String × ByteArray))

/-- The lists by which the program prints: its own names and those of the checks, and the checks'
places of rounds. -/
def Checks.lists (C : Checks) : Lists := { names := ownNames ++ C.names, places := C.places }

/-- A number on the command line: one to seven decimal digits and nothing else, no leading zero
except in "0" itself, and at most `most`. C++: decimal (verifier/src/vf_common.h). -/
def decimal (most : Nat) (s : String) : Option Nat :=
  let l := s.toList
  if l.isEmpty || decide (7 < l.length) || (decide (1 < l.length) && l.head? == some '0') ||
      l.any (fun c => !c.isDigit) then none
  else (some (l.foldl (fun x c => 10 * x + (c.toNat - 48)) 0)).filter fun v => decide (v ≤ most)

/-- True for a hex digit, capital or not. -/
def isHexDigit (c : Char) : Bool :=
  c.isDigit || (decide ('a' ≤ c) && decide (c ≤ 'f')) || (decide ('A' ≤ c) && decide (c ≤ 'F'))

/-- True for 64 hex digits. -/
def isId (s : String) : Bool := s.length == 64 && s.toList.all isHexDigit

/-- What the options of a call ask for. -/
structure Asked where
  /-- the options that the checks see -/
  options : Verify.Options := {}
  /-- `-bits` was there -/
  bitsSeen : Bool := false
  /-- `-j` was there -/
  threadsSeen : Bool := false

/-- Why the options of a call are refused. -/
inductive BadOptions where
  /-- an unknown option, one that is there twice, one without its value, a number that is not
  spelled as `decimal` asks or is above its bound, or `-j 0` -/
  | usage
  /-- the value of `-id` is not 64 hex digits -/
  | idForm
  /-- the value of `-policy` does not have the form kind,C,theta,cap,s,sh -/
  | policyForm

/-- Reads the options of a call, from the left. `-q`, `-show-stages`, `-next-token` and
`-no-proof-of-work` may be repeated; every other option may be there once. `-q`, `-show-stages` and
`-j` bear on cp_verify's printing and threads. The value of `-j` must be 1 to 256, as there; beyond
that the three options change nothing here. C++: the loop over the options in cpMain
(verifier/src/cp_verify.cpp). That loop gathers all options before it tests a number or the ID. So
on a command line with two faults the words on standard error can differ; the exit code is 2 in both
programs. -/
def readOptions : List String → Asked → Except BadOptions Asked
  | [], a => .ok a
  | "-q" :: t, a => readOptions t a
  | "-show-stages" :: t, a => readOptions t a
  | "-next-token" :: t, a =>
    readOptions t { a with options := { a.options with nextToken := true } }
  | "-no-proof-of-work" :: t, a =>
    readOptions t { a with options := { a.options with noProofOfWork := true } }
  | "-bits" :: x :: t, a =>
    match a.bitsSeen, decimal 1000000 x with
    | false, some v =>
      readOptions t { a with bitsSeen := true, options := { a.options with bits := v } }
    | _, _ => .error .usage
  | "-j" :: x :: t, a =>
    match a.threadsSeen, decimal 256 x with
    | false, some v =>
      if v == 0 then .error .usage else readOptions t { a with threadsSeen := true }
    | _, _ => .error .usage
  | "-id" :: x :: t, a =>
    if a.options.id.isSome then .error .usage
    else if isId x then readOptions t { a with options := { a.options with id := some x } }
    else .error .idForm
  | "-policy" :: x :: t, a =>
    if a.options.policy.isSome then .error .usage
    else
      match Model.policyNamedRead x with
      | some p => readOptions t { a with options := { a.options with policy := some p } }
      | none => .error .policyForm
  | _, _ => .error .usage

/-- The bytes of a file, or nothing if it is missing or cannot be read. -/
def fileIn : FileRead → Verify.FileIn
  | .bytes b => some b
  | _ => none

/-- The layout file. `none`: the operating system reports no file of that name
(`FileRead.absent`). `some none`: the name exists and cannot be read (`FileRead.unreadable`).
C++: cpConfRead (verifier/src/vf_input_files.h), which asks lstat whether the name exists: a name
that exists must be readable. -/
def layoutIn : FileRead → Option Verify.FileIn
  | .bytes b => some (some b)
  | .absent => none
  | .unreadable _ => some none

/-- Why a read gave no bytes. -/
def unreadOf : FileRead → Unread
  | .absent => .noSuch
  | .unreadable u => u
  | .bytes _ => .other

/-- The result of a call that ends before the whole verdict is formed: for the program's checks a
refusal, an input that cannot be read, a bad command line, or a failed guard of their own
(`internal-policy-empty`, OnBytes/Model/VerifyHeads.lean). If the checks return a passing result
there (a yes, a result within limits, or a part that passed), the result says that nothing was
checked. -/
def earlyEnd : CallEnd → CallEnd
  | .yes _ _ => .notChecked "internal-early-end"
  | .withinLimits _ _ => .notChecked "internal-early-end"
  | .partPassed _ _ => .notChecked "internal-early-end"
  | e => e

/-- The whole call, once its options are read. It reads the three configuration files, the key file,
the request, the reply and the proof. The checks then name the entry, or end the call. It reads that
entry and ends with the checks' result. -/
def whole (C : Checks) (config ivk request y proof : String) (a : Asked) : Ask Ending :=
  fetch C.lists textLimit (config ++ "/policy.txt") fun pol =>
  fetch C.lists fileLimit (config ++ "/KL.bin") fun kl =>
  fetch C.lists textLimit (config ++ "/layout.txt") fun lay =>
  fetch C.lists fileLimit (ivk ++ "/key.bin") fun key =>
  fetch C.lists fileLimit request fun req =>
  fetch C.lists fileLimit y fun yy =>
  fetch C.lists fileLimit proof fun prf =>
  let files : Verify.Files :=
    { policy := fileIn pol, KL := fileIn kl, layout := layoutIn lay, key := fileIn key,
      request := fileIn req, y := fileIn yy, proof := fileIn prf }
  let p : Fields :=
    { why := fun
        | .policy => unreadOf pol
        | .KL => unreadOf kl
        | .layout => unreadOf lay
        | .key => unreadOf key
        | .request => unreadOf req
        | .y => unreadOf yy
        | .proof => unreadOf prf
        | .entry => .other
      bits := a.options.bits }
  match C.entryNumber a.options files with
  | .error e => finish C.lists p (earlyEnd e)
  | .ok k =>
    fetch C.lists fileLimit (ivk ++ "/leaf/" ++ toString k ++ ".bin") fun ent =>
    finish C.lists { p with leaf := k } (C.wholeCall a.options { files with entry := fileIn ent })

/-- The result of a call on one file alone. Such a call is never a verification. If the checks
return a yes or a result within limits there, the result says that nothing was checked. -/
def partEnd : CallEnd → CallEnd
  | .yes _ _ => .notChecked "internal-part-yes"
  | .withinLimits _ _ => .notChecked "internal-part-yes"
  | e => e

/-- Why each file of a call on one file alone, or of a planning call, could not be read. -/
def partFields (pol kl lay kb ent : FileRead) : Fields :=
  { why := fun
      | .policy => unreadOf pol
      | .KL => unreadOf kl
      | .layout => unreadOf lay
      | .key => unreadOf kb
      | .entry => unreadOf ent
      | _ => .other }

/-- The call on a key file alone. It reads the three configuration files and the key file. -/
def keyPart (C : Checks) (config key : String) (a : Asked) : Ask Ending :=
  fetch C.lists textLimit (config ++ "/policy.txt") fun pol =>
  fetch C.lists fileLimit (config ++ "/KL.bin") fun kl =>
  fetch C.lists textLimit (config ++ "/layout.txt") fun lay =>
  fetch C.lists fileLimit key fun kb =>
  finish C.lists (partFields pol kl lay kb .absent) (partEnd (C.keyCall a.options
    { policy := fileIn pol, KL := fileIn kl, layout := layoutIn lay, key := fileIn kb,
      request := none, y := none, proof := none }))

/-- The call on an entry file alone. It reads the three configuration files, the key file and the
entry file. The key's table is taken from the key file's first bytes, on its form alone, and none of
the key's proofs is looked at. So a pass counts only beside a call on the key file alone that passed
on the same key file, configuration folder and bits (cpUsage, verifier/src/cp_verify.cpp).
As cp_verify does, the call prints a line that says that the key was not checked. -/
def leafPart (C : Checks) (config key entry : String) (a : Asked) : Ask Ending :=
  fetch C.lists textLimit (config ++ "/policy.txt") fun pol =>
  fetch C.lists fileLimit (config ++ "/KL.bin") fun kl =>
  fetch C.lists textLimit (config ++ "/layout.txt") fun lay =>
  fetch C.lists fileLimit key fun kb =>
  fetch C.lists fileLimit entry fun ent =>
  finish C.lists { partFields pol kl lay kb ent with leafCall := true }
    (partEnd (C.leafCall a.options
    { policy := fileIn pol, KL := fileIn kl, layout := layoutIn lay, key := fileIn kb,
      request := none, y := none, proof := none, entry := fileIn ent }))

/-- All values of `ChainIx`, in their order. -/
def allChains : List ChainIx :=
  [.keyOneTime, .keyShared, .keySecond, .entry, .first, .shared, .second]

/-- One line for each chain: its name, a blank, and the digest of its parameter bytes
(docs/format/FORMAT.md, R4.4) in 64 hex digits, or `not derived` if l lacks the chain. -/
def planLines (l : List (String × ByteArray)) : List Line :=
  allChains.map fun c =>
    match l.lookup c.text with
    | none => .noPlan c
    | some b => .planLine c (Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm b))

/-- The planning call. It reads the three configuration files, prints one line for each chain and
ends with the line that no proof was checked. If the checks refuse the files it ends as a whole
call does. -/
def planCall (C : Checks) (config : String) (bits : Nat) : Ask Ending :=
  fetch C.lists textLimit (config ++ "/policy.txt") fun pol =>
  fetch C.lists fileLimit (config ++ "/KL.bin") fun kl =>
  fetch C.lists textLimit (config ++ "/layout.txt") fun lay =>
  match C.plan bits (fileIn pol) (fileIn kl) (layoutIn lay) with
  | .error e => finish C.lists (partFields pol kl lay .absent .absent) (earlyEnd e)
  | .ok l =>
    sayAll ((planLines l).map (Line.text C.lists)) (lastSay (Line.planOnly.text C.lists) .planned)

end OnBytes.Shell

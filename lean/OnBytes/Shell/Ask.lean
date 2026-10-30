-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Ask.lean: the program as a value.

The whole program is one pure value: a tree of questions to the outside world. A node reads a file,
prints a line, or writes to standard error, and goes on with the answer. So what the program reads,
prints and returns can be stated and proved without speaking of the operating system. The three
operations themselves are in OnBytes/Shell/Ops.lean.

Main definitions: `FileRead`, `Ask`, `Ops`, `Ask.run`, `Ending`, `sayAll`, `lastSay`, `finish`,
`finishTest`, `fileLimit`, `textLimit`, `listLimit`, `fetch`, `need`. What is not claimed: no
theorem is stated here. The theorems are in the files OnBytes/Shell/At*.lean.
-/
import OnBytes.Result
import OnBytes.Shell.Lines

namespace OnBytes.Shell

open OnBytes.Model.Stages (CallEnd)

/-- The answer to a request to read a file. -/
inductive FileRead where
  /-- the file's first bytes, up to the number that was asked for -/
  | bytes (b : ByteArray)
  /-- no file was found at the path, and the question whether the name exists, asked without
  following a link, failed too -/
  | absent
  /-- the name exists and no bytes could be read, for this reason; a link that leads nowhere is such
  a name -/
  | unreadable (why : Unread)

/-- A program: a tree of reads, printed lines and messages on standard error. -/
inductive Ask (α : Type) : Type where
  /-- stop with the result a -/
  | done (a : α) : Ask α
  /-- read at most n bytes of the file at path -/
  | read (path : String) (n : Nat) (next : FileRead → Ask α) : Ask α
  /-- print a line on standard output; the answer says whether that succeeded -/
  | say (line : String) (next : Bool → Ask α) : Ask α
  /-- write a line to standard error -/
  | err (words : String) (next : Ask α) : Ask α

/-- The three operations on the outside world, in a monad m. -/
structure Ops (m : Type → Type) where
  read : String → Nat → m FileRead
  out  : String → m Bool
  err  : String → m Unit

/-- Runs a program with the given operations. -/
def Ask.run {m : Type → Type} [Monad m] {α : Type} (w : Ops m) : Ask α → m α
  | .done a => pure a
  | .read p n next => do (next (← w.read p n)).run w
  | .say l next => do (next (← w.out l)).run w
  | .err s next => do w.err s; next.run w

/-- How a call of the program ends. -/
inductive Ending where
  /-- a bad command line; in a call on a test protocol's files, a file that is missing or cannot be
  read, or an internal fault; an exception in `mainIO` -/
  | fault
  /-- a line could not be written to standard output: the call counts as not made -/
  | unwritten
  /-- the call has the result e, and all its lines were printed. e comes from the checks, or is one
  of the shell's own, made when a file is too long or the checks pass where no pass is allowed -/
  | ended (e : CallEnd)
  /-- a call on the files of a test protocol found no fault, and the line that says so was
  printed -/
  | testPassed
  /-- a call that only derives parameter bytes: no proof was checked, and the line that says so was
  printed -/
  | planned
  deriving DecidableEq, Repr, Inhabited

/-- The exit code of an ending. The codes are those of cp_verify (verifier/src/vf_common.h). There 2
is for a bad command line and for an input that cannot be read; here it is for every fault too. 15
is for an answer that could not be written. 4 is for a planning call. A call on a test protocol's
files, which cp_verify does not have, shares 3 with a part-call that found no fault. -/
def Ending.status : Ending → UInt32
  | .fault => 2
  | .unwritten => 15
  | .ended e => e.status
  | .testPassed => 3
  | .planned => 4

/-- Writes the words to standard error and ends in a fault. -/
def faultWith (words : String) : Ask Ending := .err words (.done .fault)

/-- The end of a call whose answer could not be written to standard output: one sentence on
standard error. -/
def unwritten : Ask Ending :=
  .err ("verify-on-bytes: the answer could not be written to standard output: take this call as " ++
    "not made") (.done .unwritten)

/-- Prints the lines and goes on. A line that cannot be printed ends the call. -/
def sayAll : List String → Ask Ending → Ask Ending
  | [], next => next
  | l :: ls, next => .say l fun ok => if ok then sayAll ls next else unwritten

/-- Prints a call's last line and ends the call with r. -/
def lastSay (l : String) (r : Ending) : Ask Ending :=
  .say l fun ok => if ok then .done r else unwritten

/-- Ends the call with the result e of the checks. A bad command line is a fault: nothing is printed
on standard output, and standard error gets a fixed line, not the words of the result. The shell
refuses such a command line itself when it reads the options (`kindOf`, OnBytes/Shell/Call.lean), so
with the program's own checks this case should not be reached; no theorem says so. Every other
result is printed: the lines of `before`, then the line of `verdict`. -/
def finish (L : Lists) (p : Fields) : CallEnd → Ask Ending
  | .usage _ => faultWith "verify-on-bytes: bad command line"
  | e => sayAll ((before p e).map (Line.text L)) (lastSay ((verdict p e).text L) (.ended e))

/-- Ends a call on the files of a test protocol in which no check failed. The argument is what the
accounting says on proof of work. If it refuses, the call is refused. If not, the line on work is
printed, as in a whole call, and then the passing line. -/
def finishWork (L : Lists) :
    Except String (Option Model.Stages.WorkCount × Nat) → Ask Ending
  | .error name => finish L {} (.no name)
  | .ok (w, least) =>
    sayAll [(Line.work w least).text L] (lastSay (Line.testPassed.text L) .testPassed)

/-- Ends a call on the files of a test protocol with its verdict, and with what w says on proof of
work. Such a call never ends with `YES`, `WITHIN LIMITS` or the exit code 0: those are kept for the
verdict of a whole call on a request. -/
def finishTest (L : Lists) (w : Except String (Option Model.Stages.WorkCount × Nat)) :
    Verdict → Ask Ending
  | .accepted => finishWork L w
  | .refused r => finish L {} (.no r.check)

/-- No file of a call may be longer than this many bytes: 2^28, or 256 MiB. Some files have a
smaller limit (`textLimit`, `listLimit`). The limit is this program's own. The routines with which
cp_verify reads a file have none (`readWholeFile`, `readWords`, verifier/src/vf_common.h), so on a
longer file the two programs can end differently: cp_verify tests the length of y, and under a line
lt of at most 20 that of the request, before it reads them, so a longer one ends there with
`NO: statement-range` or `NO: statement-required`, here with `NO: file-too-long`. A test that
cp_verify makes on a length after the read is named at `textLimit`. -/
def fileLimit : Nat := 268435456

/-- The two text files of a configuration, policy.txt and layout.txt, may not be longer than this
many bytes: 2^20, or 1 MiB. The checks make lists of a file's bytes before they test its first line,
and compare each line of layout.txt that lays out a block with every other, so the limit bounds
memory and time. It is this program's own: cp_verify refuses such a file for its length only from
2^32 bytes on (`rejectLongTextFile`, vf_common.h). A policy.txt that the checks admit has fewer
than 50,000 bytes, by a count that is not proved (OnBytes/Model/Config.lean). The layout.txt of
prover/examples/target_full_f2 has 224,975 bytes. A layout.txt above the limit can be lawful:
cp_verify accepts it and this program refuses it. -/
def textLimit : Nat := 1048576

/-- No file of a call on a test protocol's files may be longer than this many bytes: 2^22, or 4 MiB.
The checks make lists of the bytes of such a protocol's public files before they test a line, so the
limit bounds these lists. -/
def listLimit : Nat := 4194304

/-- Reads the file at path and goes on with the answer. One byte more than the limit is asked for.
If that many bytes come, the file is too long, and the call ends with `NO: file-too-long`. -/
def fetch (L : Lists) (limit : Nat) (path : String) (next : FileRead → Ask Ending) : Ask Ending :=
  .read path (limit + 1) fun r =>
    match r with
    | .bytes b => if b.size ≤ limit then next r else finish L {} (.no "file-too-long")
    | _ => next r

/-- Reads the file at path and goes on with its bytes. A file that is missing or cannot be read ends
the call in a fault, with the path on standard error. For calls on a test protocol's files only: a
whole call, like cp_verify, never prints a path (OnBytes/Shell/Whole.lean). -/
def need (L : Lists) (path : String) (next : ByteArray → Ask Ending) : Ask Ending :=
  fetch L listLimit path fun
    | .bytes b => next b
    | .absent => faultWith ("verify-on-bytes: cannot read " ++ path)
    | .unreadable _ => faultWith ("verify-on-bytes: cannot read " ++ path)

end OnBytes.Shell

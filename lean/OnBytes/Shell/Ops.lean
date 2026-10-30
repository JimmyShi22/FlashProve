-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Ops.lean: the three operations on the outside world, and the program in IO.

This file, `program` (OnBytes/Shell/Checks.lean) and OnBytes/Main.lean hold all the code between the
pure program (OnBytes/Shell/Call.lean) and the operating system.

Main definitions: `readIO`, `outIO`, `errIO`, `mainIO`. What is not claimed: no theorem is stated
here (see OnBytes/Shell/AtOps.lean, AtBottom.lean, AtMain.lean and AtSize.lean).
-/
import OnBytes.Shell.Call

namespace OnBytes.Shell

/-- The most bytes that one read asks for. A read's buffer is allocated whole, however short the
file is. -/
def readChunk : Nat := 1048576

/-- Reads from the handle until n bytes are there or the file ends, at most `readChunk` bytes at a
time. The third argument bounds the number of reads. -/
def readUpTo (h : IO.FS.Handle) (n : Nat) : Nat → ByteArray → IO ByteArray
  | 0, acc => pure acc
  | rounds + 1, acc =>
    if n ≤ acc.size then pure acc else do
      let c ← h.read (min (n - acc.size) readChunk).toUSize
      if c.isEmpty then pure acc else readUpTo h n rounds (acc ++ c)

/-- Reads at most n bytes of a regular file. Only a regular file is read: a device or a pipe may
never end, and opening a named pipe that has no writer would hang. The path is tested before the
file is opened. Unlike `readWholeFile` (vf_common.h), this function does not test the open
file again, so it does not notice a path that comes to mean something else between the two steps.
The bound n on the number of reads is enough: a read that is not empty adds at least one byte. -/
def readBody (p : String) (n : Nat) : IO FileRead := do
  let md ← System.FilePath.metadata p
  if md.type != .file then pure (.unreadable .notRegular) else do
    let h ← IO.FS.Handle.mk p .read
    let b ← readUpTo h n n ByteArray.empty
    pure (.bytes b)

/-- The error code of the operating system in an error, or 0 if it holds none. -/
def codeOf : IO.Error → UInt32
  | .alreadyExists _ c _ => c
  | .otherError c _ => c
  | .resourceBusy c _ => c
  | .resourceVanished c _ => c
  | .unsupportedOperation c _ => c
  | .hardwareFault c _ => c
  | .unsatisfiedConstraints c _ => c
  | .illegalOperation c _ => c
  | .protocolError c _ => c
  | .timeExpired c _ => c
  | .interrupted _ c _ => c
  | .noFileOrDirectory _ c _ => c
  | .invalidArgument _ c _ => c
  | .permissionDenied _ c _ => c
  | .resourceExhausted _ c _ => c
  | .inappropriateType _ c _ => c
  | .noSuchThing _ c _ => c
  | .unexpectedEof => 0
  | .userError _ => 0

/-- For a path at which no file was found. Asks whether the name p exists, without following a link.
If so, it is a link that leads nowhere: `unreadable noSuch`. If not: `absent`. C++: the lstat in
cpConfRead (verifier/src/vf_input_files.h). -/
def nameOf (p : String) : IO FileRead :=
  tryCatch (do
    let _ ← System.FilePath.symlinkMetadata p
    pure (.unreadable .noSuch)) fun _ => pure .absent

/-- Which answer an error of the operating system becomes. -/
def readOf (p : String) : IO.Error → IO FileRead
  | .noFileOrDirectory .. => nameOf p
  | e => pure (.unreadable (Unread.ofCode (codeOf e)))

/-- Reads a file; never throws. -/
def readIO (p : String) (n : Nat) : IO FileRead :=
  tryCatch (readBody p n) (readOf p)

/-- Prints a line on standard output and flushes; says whether that succeeded. -/
def outIO (s : String) : IO Bool :=
  tryCatch
    (do
      let o ← IO.getStdout
      o.putStr (s.push '\n')
      o.flush
      pure true)
    fun _ => pure false

/-- Writes a line to standard error; a failure is ignored. -/
def errIO (s : String) : IO Unit :=
  tryCatch (IO.eprintln s) fun _ => pure ()

/-- The three operations. -/
def opsIO : Ops IO := { read := readIO, out := outIO, err := errIO }

/-- Runs the program and returns its exit code. -/
def mainIO (C : Checks) (args : List String) : IO UInt32 := do
  let e ← tryCatch ((call C args).run opsIO) fun _ => pure Ending.fault
  return e.status

end OnBytes.Shell

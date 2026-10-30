-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Main.lean: the entry function of the Lean text `verify-on-bytes` ("the program" here), a
verifier in Lean for the files that the C++ verifier cp_verify checks; this repository builds no
stand-alone program from it.

Main definition: `main`: one call of `programFront` (OnBytes/Shell/Front.lean): `mainIO` with the
checks in the text that takes the format's hash, and at one call the second hash, as arguments, at
the program's own two hashes. `programFront` itself takes no hash, and neither argument stands for
BLAKE2b: the first is the format's hash of five arguments. What the two arguments are, and which
calls of the two hashes they do not reach, the head of that file says.

The theorems on the program are stated of `program` (OnBytes/Shell/Checks.lean), the same checks in
the text without such arguments; they reach `main` through one theorem alone,
`OnBytes.Shell.main_eq` (OnBytes/Shell/AtMain.lean), an equation between terms at these two hashes,
which says nothing of compiled code. `main` takes no hash: no theorem speaks of it at another hash
or at a hash drawn at random.

What is not claimed: no theorem is stated here.
-/
import OnBytes.Shell.Front

/-- The entry function. `args` is the command line (`usage`, OnBytes/Shell/Call.lean); the result is
the exit code (`Ending.status`, OnBytes/Shell/Ask.lean). -/
def main (args : List String) : IO UInt32 := OnBytes.Shell.programFront args

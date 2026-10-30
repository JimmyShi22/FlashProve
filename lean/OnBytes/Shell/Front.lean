-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Front.lean: the checks on a model's files with the format's hash as an argument, and
`mainIO` with them at the program's own two hashes.

Main definitions.
  `checksAt h k`: the record of checks (`Checks`, OnBytes/Shell/Whole.lean) whose whole call, call
    on a key file, call on an entry file and plan are the texts over a monad of
    OnBytes/ChecksWithHashAsArgument/M/Model/Verify.lean, at the identity monad and at a letter h for the format's
    hash; the whole call alone also takes a letter k for the second hash on the request file. The
    names, the places and the first tests (`entryNumber`) are those of `modelChecks`
    (OnBytes/Shell/Checks.lean): they take no letter.
  `frontChecks`: `checksAt` at the program's own two functions, `formatHashFastForm` and `secondHashFunctionTree`.
  `programFront`: `mainIO` with `frontChecks`. It takes no hash.

What the letters are. h stands for the format's hash of five arguments (three numbers and two byte
strings: `M.HashM Id`, OnBytes/ChecksWithHashAsArgument/M/Chain/EngineM.lean), a bare function with no law: not for
BLAKE2b and not for an oracle on strings. k is a second letter, tied to h by nothing. No function of
(files, hash) is defined here beyond the four fields of `checksAt h k`; for a whole call:
`(checksAt h k).wholeCall o f`.

What is not claimed: no theorem is stated here. This file does not say what the root's `main` calls:
OnBytes/Main.lean does. Where `main` is `program`, no definition of this file is called by the
program; where `main` is `programFront`, all three are, and the theorems on `program` reach `main`
through one theorem alone: that `programFront` and `program` are one term
(OnBytes/Shell/FrontSame.lean), which is not a definition. That the letter h reaches every call of
the format's hash in these texts is no theorem; the shell's `planLines` (OnBytes/Shell/Whole.lean)
calls `formatHashFastForm` by name, at any record. The second hash function is a letter at one call alone, the
request file's digest: the first tests, the planner and the request's item itself (`requestItemOf`,
OnBytes/ChecksWithHashAsArgument/M/Proof/RequestItem.lean: the scale file's digest, the lines' calls) call it by
name, whatever k is (the head of OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean lists the constants).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Shell.Checks
import OnBytes.ChecksWithHashAsArgument.M.Model.Verify

namespace OnBytes.Shell

open OnBytes.TwoPort

/-- The checks on a model's files at a hash h and an older hash k on the request file. -/
def checksAt (h : M.HashM Id) (k : ByteArray → Id (Option ByteArray)) : Checks :=
  { modelChecks with
    wholeCall := fun o f => M.Model.Verify.wholeCall (m := Id) h k o f
    keyCall := fun o f => M.Model.Verify.keyCall (m := Id) h o f
    leafCall := fun o f => M.Model.Verify.leafCall (m := Id) h o f
    plan := fun bits policy KL layout =>
      (M.Model.Verify.planBytes (m := Id) h bits policy KL layout).run }

/-- The checks at the program's own two hashes, `formatHashFastForm` and `secondHashFunctionTree`. -/
def frontChecks : Checks := checksAt formatHashFastForm (fun b => secondHashFunctionTree b)

/-- `mainIO` with `frontChecks`, as a function of the command line. -/
def programFront (args : List String) : IO UInt32 := mainIO frontChecks args

end OnBytes.Shell

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Checks.lean: the checks on a model's files at the program's own two hashes, in the
text without a letter for a hash, and `mainIO` with them.

Main definitions: `modelChecks`, `program`. What is not claimed: no theorem is stated here.
-/
import OnBytes.Shell.Ops
import OnBytes.Model.StagesNames
import OnBytes.Model.Tensors

namespace OnBytes.Shell

/-- The checks on a model's files: those of OnBytes/Model/Verify.lean, with the names that the
modules of OnBytes/Model/ list (`Stages.allNames`, OnBytes/Model/StagesNames.lean, and the list of
OnBytes/Model/Tensors.lean). No theorem shows that every name under which a module refuses is in its
list. A name that is in no list is printed as `unlisted-check`. -/
def modelChecks : Checks :=
  { names := Model.Stages.allNames ++ Model.tensorsNames
    places := Model.Verify.Account.places
    entryNumber := Model.Verify.entryNumber
    wholeCall := Model.Verify.wholeCall
    keyCall := Model.Verify.keyCall
    leafCall := Model.Verify.leafCall
    plan := Model.Verify.planBytes }

/-- `mainIO` with `modelChecks`, as a function of the command line: the function of which the
theorems on the program are stated. The root's `main` calls `programFront`
(OnBytes/Shell/Front.lean), which is this function by `programFront_eq`
(OnBytes/Shell/FrontSame.lean). -/
def program (args : List String) : IO UInt32 := mainIO modelChecks args

end OnBytes.Shell

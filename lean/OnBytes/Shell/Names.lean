-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Names.lean: the names that the program may print.

A call that is refused ends with the line `NO: ` and the name of the check that failed. The checks
hand that name to the program as a string. So that no name can carry bytes of a file to the
output, the program prints a name only if it is in a fixed list (`Line.text`,
OnBytes/Shell/Lines.lean). Any other name is printed as `unlisted-check`. Each module that can
refuse has a list of its names beside the code that uses them. The list by which the program prints
is made of those lists: `ownNames`, for the shell and the checks of the test protocols, and the
names that come with the checks on a model's files (`Checks.names`, OnBytes/Shell/Whole.lean).

Main definitions: `shellNames`, `ownNames`. What is not claimed: that every name under which a
module refuses is in its list.
-/
import OnBytes.Toy.Product
import OnBytes.Iop.Prox
import OnBytes.Chain.Why
import OnBytes.Key.File
import OnBytes.Entry.File
import OnBytes.Proof.ToyLinks
import OnBytes.Params.RefusalNames
import OnBytes.Plan.ToyRuns

namespace OnBytes.Shell

/-- The names that the shell itself writes, except `model-statement` and `policy` (`verdict`,
OnBytes/Shell/Lines.lean), which `Stages.endNames` (OnBytes/Model/Stages.lean) lists. The first
three are refusals. The next two say that nothing was checked. `internal-default-value` is in the
default `Verdict`, a refusal (OnBytes/Result.lean). `internal-no-line` fills a case of `verdict`
that `finish` never reaches. -/
def shellNames : List String :=
  ["file-too-long", "key-parameters", "entry-parameters", "internal-early-end",
   "internal-part-yes", "internal-default-value", "internal-no-line"]

/-- The names of the shell and of the modules that check the files of the test protocols. A name
that several modules use occurs several times. -/
def ownNames : List String :=
  shellNames ++ Toy.names ++ proxNames ++ ReaderCheck.names ++ Key.names ++ Entry.names ++
    Proof.toyNames ++ Params.names ++ Plan.names

end OnBytes.Shell

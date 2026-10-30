-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/StagesNames.lean: one list of the names with which the check of a model's proof can
refuse.

A refusal has a name. The rule of this library is that a name contains nothing that was read from a
file. Each module that can refuse lists its names in one constant beside the code that uses them.
This file gathers these lists, so that a program that prints a name in the last line of a call can
compare it with one list and print nothing else.

Main definition: `Stages.allNames`.
What is not claimed: no theorem is stated here. In particular, none shows that every string that a
module passes to a refusal is in that module's list. The list holds the names of the modules that
`allNames` spells out, and of no others. A name that is in no list is printed as unlisted-check
(OnBytes/Shell/Lines.lean).
-/
import OnBytes.Model.Verify
import OnBytes.Params.RefusalNames

namespace OnBytes.Model.Stages

/-- The names of modules under OnBytes/Model/, module by module, and after them those of the planner
under OnBytes/Params/, which the check calls. A name that several modules use occurs several times.
-/
def allNames : List String :=
  endNames ++ linksNames ++ Config.names ++ Rounds.names ++ lookNames ++ Forest.names ++
    Trees.names ++ Tail.names ++ Attention.configNames ++ Attention.names ++
    Head.names ++ Layer.names ++ Weights.names ++ Merge.names ++ Pending.names ++
    Verify.Cross.names ++ Verify.Account.names ++ Verify.Subproofs.names ++ Verify.names ++
    Params.names

end OnBytes.Model.Stages

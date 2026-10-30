-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Result.lean: a verdict on a file, and the name of the check at which a file was refused.

The checks of single files use these types (OnBytes/Key/, OnBytes/Entry/, OnBytes/Proof/,
OnBytes/Toy/). The result of a whole call has another type, `Model.Stages.CallEnd`
(OnBytes/Model/Stages.lean).

Main definitions: `Stage`, `Refusal`, `Verdict`.
-/

namespace OnBytes

/-- The part of a call in which a check failed. The program never prints the stage. The whole call
asks one thing of it: a refusal in the stage `configuration` counts as a fault of the program and
not of a file (`refusalName`, OnBytes/Model/VerifyStages.lean). -/
inductive Stage where
  /-- what a check is given as public input, such as the configuration files, a test protocol's
  public files, or parameter bytes -/
  | configuration
  /-- the request and its reply -/
  | request
  /-- the key file -/
  | key
  /-- the entry file that the proof names -/
  | entry
  /-- the proof file -/
  | proof
  deriving DecidableEq, Repr, Inhabited

/-- Why a call was refused: the stage, and the name of the first check that failed. By the rule of
this directory a name holds nothing that was read from a file, and each module lists its names
beside the code that refuses. The type does not enforce the rule. The program prints a name only if
it is in its list and holds no line feed (`shown`, OnBytes/Shell/Lines.lean). -/
structure Refusal where
  /-- the part of the call -/
  stage : Stage
  /-- the name of the check -/
  check : String
  deriving DecidableEq, Repr, Inhabited

/-- A verdict: accepted, or refused with the reason. -/
inductive Verdict where
  /-- every check passed -/
  | accepted
  /-- a check failed -/
  | refused (r : Refusal)
  deriving DecidableEq, Repr

/-- The default value is a refusal. Compiled code that reads beyond an array's end returns the
type's default value, and that must never be `accepted`. -/
instance : Inhabited Verdict := ⟨.refused ⟨.configuration, "internal-default-value"⟩⟩

end OnBytes

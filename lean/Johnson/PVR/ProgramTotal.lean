-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PVR/ProgramTotal.lean: the pure function `PV.Program.verdictOf` gives a verdict wherever the
claim reads, and it is `VerifierAndGoals.verify`'s. These are theorems on Lean terms, not on code that runs.

`verdictAt_eq`: `verdictAt g c (stepsOf g c) = some (verifyValue g c)`, at every `g` and `c`: the
left side joins the two calls that stand in `PV.Program.ending`'s text (Johnson/PVR/Program.lean).
`verdictOf_map`: `verdictOf g = (claimOf g).map (verifyValue g)`: one equation, without a premise.
`verdictOf_eq`: the same where `claimOf g = some c`.

They are the case O = `Fmt.oracle` of an equation that holds at every function O on bytes whose
answers have 32 bytes (`PV.Ride.verdictThe_eq`, Johnson/PVR/RideEveryHash.lean; at every hash
function of the goals' kind: `PV.Ride.verify_every_hash` there). Of BLAKE2b they use only that an
answer has 32 bytes (`Fmt.size_oracle`, Fmt/Rules23Laws.lean).

Limits: those of Johnson/PVR/Program.lean. No soundness is stated here.

Terms: lean/TERMS.md; lean/GLOSSARY.md.
-/
import Johnson.PVR.Program
import Johnson.PVR.RideEveryHash

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.Program

/-- **`verdictAt` at `stepsOf` is `VerifierAndGoals.verify`'s value.** It says nothing of code that runs. -/
theorem verdictAt_eq (g : Given) (c : Claim) :
    verdictAt g c (stepsOf g c) = some (verifyValue g c) :=
  PV.Ride.verdictThe_eq (pubOf g) _root_.Fmt.oracle _root_.Fmt.size_oracle (formOf g c)
    c.commitment c.prompt c.output

/-- **From bytes to verdict: `claimOf`, then `VerifierAndGoals.verify`'s value.** -/
theorem verdictOf_map (g : Given) : verdictOf g = (claimOf g).map (verifyValue g) := by
  cases h : claimOf g with
  | none => exact verdictOf_none g h
  | some c => exact (verdictOf_at g c h).trans (verdictAt_eq g c)

/-- Where the claim reads, the verdict is given, and it is `VerifierAndGoals.verify`'s. -/
theorem verdictOf_eq (g : Given) (c : Claim) (h : claimOf g = some c) :
    verdictOf g = some (verifyValue g c) :=
  (verdictOf_at g c h).trans (verdictAt_eq g c)

end PV.Program

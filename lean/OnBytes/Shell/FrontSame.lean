-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/FrontSame.lean: the checks with the hash as an argument, at the program's own hash,
are the checks of OnBytes/Shell/Checks.lean; so `programFront` is `program`.

Main theorems.
  `Checks.same`: two records of checks with the same seven fields are one.
  `frontChecks_eq`: `frontChecks = modelChecks`.
  `programFront_eq`: `programFront = program`: with it a theorem on `program` is one on
    `programFront`, by one rewriting.

Limits: equations between terms, at the one hash `formatHashFastForm` and the one tree hash `secondHashFunctionTree`: they say
nothing of compiled code, and nothing at another h. ALL THE WEIGHT IS IN FOUR EQUATIONS OF
OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean (`wholeCall_port`, `keyCall_port`, `leafCall_port`,
`planBytes_port`). One equation at one point does not show that the hash is a letter everywhere in
the texts over a monad (the head of that file). Theorems only; the program does not import this
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Shell.Front
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Spine

set_option autoImplicit false

namespace OnBytes.Shell

open OnBytes.TwoPort

/-- Two records of checks with the same fields are one. -/
theorem Checks.same : ∀ {A B : Checks}, A.names = B.names → A.places = B.places →
    A.entryNumber = B.entryNumber → A.wholeCall = B.wholeCall → A.keyCall = B.keyCall →
    A.leafCall = B.leafCall → A.plan = B.plan → A = B
  | ⟨_, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl => rfl

/-- A record of checks with its last four fields laid anew, each equal to the record's own, is the
record. -/
theorem Checks.with_four (C : Checks) {w k l : Model.Verify.Options → Model.Verify.Files → _}
    {p : Nat → Model.Verify.FileIn → Model.Verify.FileIn → Option Model.Verify.FileIn → _}
    (hw : w = C.wholeCall) (hk : k = C.keyCall) (hl : l = C.leafCall) (hp : p = C.plan) :
    { C with wholeCall := w, keyCall := k, leafCall := l, plan := p } = C := by
  subst hw hk hl hp
  rfl

/-- **The checks with the hash as an argument, at the program's own two hashes, are the checks of
OnBytes/Shell/Checks.lean (`modelChecks`)**: three fields by unfolding, four by a theorem each. -/
theorem frontChecks_eq : frontChecks = modelChecks :=
  Checks.with_four modelChecks
    (funext fun o => funext fun f => M.AtPort.wholeCall_port o f)
    (funext fun o => funext fun f => M.AtPort.keyCall_port o f)
    (funext fun o => funext fun f => M.AtPort.leafCall_port o f)
    (funext fun bits => funext fun policy => funext fun KL => funext fun layout =>
      M.AtPort.planBytes_port bits policy KL layout)

/-- **`programFront` is `program`.** -/
theorem programFront_eq : programFront = program := by
  funext args
  unfold programFront program
  rw [frontChecks_eq]

end OnBytes.Shell

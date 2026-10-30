-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/SelfRows.lean: the smallness test's three steps behind a sub-proof's last claim
(SelfTests.lean, Coefficients.lean), in a row, as one plain function, and as a step and a row of a chain's
decision (Johnson/Desc/Step.lean).

Main names:
  `testsP nU tl F`: the first test of the program on itself; the weights of the virtual rows; the test by a
    second computation: the state with the weights set, or the name of the guard that refused.
  `testsStep get set nU`: the same as a `Step S`, through a lens on the chain's state: it takes no round and no
    column and refuses a stretch that has a round. `testsRow`: the row, with its name.
nU: the plan's numbers of entries of the three tables. get: the smallness test's record, as the step that laid
its claims returned it, and the sub-proof's ledger.
Limits: definitions alone. The callers' own tests in front of the three are other files'.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Step
import Johnson.Desc.First.TailClaims.Coefficients
import Johnson.Desc.First.TailClaims.SelfTests

set_option autoImplicit false

namespace VerifiableInference.Desc.First.TailClaims
open OnBytes OnBytes.Model VerifiableInference.Desc

/-- The three in a row. -/
def testsP (nU : Array Nat) (tl : HTailF2) (F : Fork) : Except String Fork := do
  selfTestP tl nU F
  let F ← coefficientsP tl F
  rkSelfTestP tl F
  pure F

/-- The three in a row as a step. -/
def testsStep {S : Type} (get : S → HTailF2 × Fork) (set : S → Fork → S) (nU : Array Nat) : Step S :=
  fun s rounds _ =>
    if rounds.isEmpty then
      match testsP nU (get s).1 (get s).2 with
      | .ok F => some (set s F, 0)
      | .error _ => none
    else none

/-- The row. -/
def testsRow {S : Type} (get : S → HTailF2 × Fork) (set : S → Fork → S) (nU : Array Nat) : Row S :=
  ⟨"the smallness test's three tests of its own books", 0, testsStep get set nU⟩

end VerifiableInference.Desc.First.TailClaims

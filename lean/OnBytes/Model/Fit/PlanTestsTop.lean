-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/PlanTestsTop.lean: from the program's yes on the three configuration files alone:
the first chain of the key and of the proof has two rounds at least, and the last round of the first
and of the shared chain asks for no work.

OnBytes/Model/Fit/FitPlanned.lean (small_of_planned) says that every entry of the six made plans is
Small, from the program's yes alone. Small's first clause is what
OnBytes/Model/Fit/ReadNormMade.lean asks of the made plans (Spelt).

Main theorems: spelt_of_planned, planTests_planned_top.

What is not claimed: nothing where Verify.planned refuses; that it returns at any files. Nothing on
the dry runs. Nothing on soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Model.Fit.FitPlanned

set_option autoImplicit false

namespace OnBytes.Model.Verify

open OnBytes.Params

variable {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}

/-- The names of the six made plans' entries are in order. -/
theorem spelt_of_planned (h : planned pol KL layout = .ok p) :
    ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, Spelt P :=
  fun P hP => spelt_of_small (small_of_planned h P hP)

/-- **The tests on the first and the shared chain's plans, from the program's yes alone.** -/
theorem planTests_planned_top (h : planned pol KL layout = .ok p) :
    (2 ≤ p.chains.key.oneTime.given.rounds.length ∧
        EndsSeal p.chains.key.oneTime.given.rounds ∧
        EndsSeal p.chains.key.shared.given.rounds) ∧
      (2 ≤ p.chains.proof.first.given.rounds.length ∧
        EndsSeal p.chains.proof.first.given.rounds ∧
        EndsSeal p.chains.proof.shared.given.rounds) :=
  planTests_planned_norm h (spelt_of_planned h)

end OnBytes.Model.Verify

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/PlanTestsSmall.lean: the tests on the first and the shared chain's plans, of what
the program computes from the three configuration files, where every entry of the made plans is
Small.

OnBytes/Params/Fit/FitCalc.lean has the condition Small on an entry; its first clause says that the
entry's name fits and is not the name of the configuration's item. That clause is what
OnBytes/Model/Fit/ReadNormMade.lean asks of the made plans (Spelt).

Main theorems: spelt_of_small, planTests_planned_small.

What is not claimed: that the made plans' entries are Small: a premise. Of Small's seven clauses
the first alone is used here: whoever has the names alone calls planTests_planned_norm. Nothing
on soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Model.Fit.ReadNormMade
import OnBytes.Params.Fit.FitCalc

set_option autoImplicit false

namespace OnBytes.Params

/-- A made plan whose entries are Small is Spelt. -/
theorem spelt_of_small {P : Planned} (h : ∀ r ∈ P.rounds, Small r.entry) : Spelt P := by
  constructor
  · intro e he
    have he' : e ∈ P.rounds.map (·.entry) := he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he'
    exact (h r hr).1.1
  · intro e he
    have he' : e ∈ P.rounds.map (·.entry) := he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he'
    exact (h r hr).1.2

end OnBytes.Params

namespace OnBytes.Model.Verify

open OnBytes.Params

/-- From the program's yes on the three configuration files, where every entry of the made plans
is Small. -/
theorem planTests_planned_small {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p)
    (hs : ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, ∀ r ∈ P.rounds, Small r.entry) :
    (2 ≤ p.chains.key.oneTime.given.rounds.length ∧
        EndsSeal p.chains.key.oneTime.given.rounds ∧
        EndsSeal p.chains.key.shared.given.rounds) ∧
      (2 ≤ p.chains.proof.first.given.rounds.length ∧
        EndsSeal p.chains.proof.first.given.rounds ∧
        EndsSeal p.chains.proof.shared.given.rounds) :=
  planTests_planned_norm h fun P hP => spelt_of_small (hs P hP)

end OnBytes.Model.Verify

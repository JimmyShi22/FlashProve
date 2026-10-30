-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstAnyWitness.lean: at every place there is a job at that
place which says that the first fold's fresh table has come earlier, and a simulators' job with the
same two public letters. Both are made up and written out.

  `madeJob`, `madeSims`   the two jobs: no member; the table's sender is the place's own part number
                 0; the state on entry is `noState` (JobShared.lean); rows 0; no tree
  `job_there`, `sims_there`   they have the letters that Sim/FirstAnyAtPlace.lean asks

Why. The statements "at every job at the place" (Sim/FirstAnyAtPlace.lean and the files over it)
would say nothing if no such job were there.

Limits. Made-up jobs. They show only that "every job" is not empty by form: nothing on whether any
job at a place is the prover's. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Sims
import Johnson.Desc.ProofFile.Honest.K12.JobShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (P12)

/-- A made-up job at the place p. -/
def madeJob (W X : Type) (p : P12) : TestJob W X :=
  ⟨p, [], some (⟨p.place, 0⟩, 0), fun _ _ => noState, fun _ _ _ => zeroPS, fun _ _ _ _ => []⟩

/-- A made-up simulators' job at the place p. -/
def madeSims (Pb : Type) (p : P12) : SimJob Pb := ⟨p, false, fun _ _ => noState, []⟩

theorem job_there (W X : Type) (p : P12) :
    ∃ J : TestJob W X, J.p = p ∧ J.fresh.isNone = false := ⟨madeJob W X p, rfl, rfl⟩

theorem sims_there (Pb : Type) (p : P12) : ∃ Js : SimJob Pb, Js.p = p ∧ Js.own = false :=
  ⟨madeSims Pb p, rfl, rfl⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.madeJob
#print axioms ProofFile.Honest.K12.Light.madeSims
#print axioms ProofFile.Honest.K12.Light.job_there
#print axioms ProofFile.Honest.K12.Light.sims_there

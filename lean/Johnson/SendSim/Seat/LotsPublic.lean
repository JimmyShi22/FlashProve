-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotsPublic.lean: what the simulators of the two lots of the kind K1 are built
from (J.P, J.first and J.ride) does not depend on the data.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has.
  jobs_public   For all public parts Z, grounds G and numberings no, and any two data D and D': the
                list of the triples (J.P, J.first, J.ride), over the jobs J of lotJobs and wJobs in
                their order, is the same at D and at D'.

How it fits. The simulator in our row at a job J is sendSim J.P J.first J.ride (jobRow,
AtDescLots.lean). So by this lemma the list of simulators is a term of Z, G and no alone. That the
simulator is not built from wit either is by inspection, not proved: jobOver changes the field data
alone. What a simulator is given when it runs is another matter (Johnson/SendSim/At/Sim.lean, "What
the simulator is given"). A lemma on lists: no distribution is named. Not one of the release's goal
statements.

Limits. It says nothing on what sendSim does with the three. All limits of AtDescLots.lean.
-/
import Johnson.SendSim.Seat.LotW

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {X Xi : Type}

/-- **What the simulators are built from is the same at any two data.** -/
theorem jobs_public (no : Place → Nat) (D D' : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) :
    (lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G).map
        (fun J => (J.P, J.first, J.ride)) =
      (lotJobs (X := X) no D' Z G ++ wJobs (X := X) no D' Z G).map
        (fun J => (J.P, J.first, J.ride)) := by
  simp only [List.map_append]
  congr 1
  · unfold lotJobs
    simp only [List.map_cons, List.map_flatMap]
    refine congrArg₂ List.cons rfl ?_
    congr 1
    funext y
    obtain ⟨Y, l⟩ := y
    dsimp only
    cases K1.linkNumbers G Y with
    | none => rfl
    | some q => rfl
  · unfold wJobs
    cases linMessageW Z.first.lin <;> rfl

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.jobs_public

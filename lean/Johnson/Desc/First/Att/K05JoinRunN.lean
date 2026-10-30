-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05JoinRunN.lean: kind K5: the run "join" as the kind's list of runs typed at Claim holds it
(Johnson/Desc/First/Att/SeatN.lean: runsN maps runN over Johnson/Desc/First/Att/SeatO.lean's runsO) is the lookup's own run
at the calls' seat whose claims are made by K3Lot.ofForm (Johnson/Desc/ProofFile/Lot/K3.lean).

Main names:
  `join_runN_keys`: the equation at every function keys.
  `join_runN_eq`: at the kind's own keys (keysOfO A).
  `join_in_runsN`: ("join", that run) is a member of runsN A.
How made: Johnson/Desc/First/Batch/BlindClaims.lean's join_is and Johnson/Desc/First/Batch/BlindFl.lean's joinCalls_is, joined;
runN is runOfForms' second part, and claimOf, K9.ofForm and K3Lot.ofForm have one text ({ form := a }).
Is it empty here? No: an equation of two functions, under no premise.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.First.Batch.BlindClaims
import Johnson.Desc.ProofFile.Lot.K3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc

/-- "join", made of forms and then typed at Claim, is the lookup's run that makes claims itself. -/
theorem join_runN_keys (keys : First.S → Option (Array Aff)) :
    runN (K3.joinRun (K3.seatCalls (Cl := Aff) id) keys) = K3.joinRun (K3.seatCalls K3Lot.ofForm) keys :=
  (K9.join_is keys).trans (K9.joinCalls_is keys).symm

/-- **At the kind's own keys.** -/
theorem join_runN_eq (A : Attention.Plan) :
    runN (K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A)) = K3.joinRun (K3.seatCalls K3Lot.ofForm) (keysOfO A) :=
  join_runN_keys _

/-- The kind's list of runs holds it under the name "join". -/
theorem join_in_runsN (A : Attention.Plan) :
    ("join", K3.joinRun (K3.seatCalls K3Lot.ofForm) (keysOfO A)) ∈ runsN A := by
  rw [← join_runN_eq]
  exact List.mem_map.2 ⟨("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A)), by
    simp [runsO, runsK], rfl⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.join_runN_keys
#print axioms VerifiableInference.Desc.First.Att.P.join_runN_eq
#print axioms VerifiableInference.Desc.First.Att.P.join_in_runsN

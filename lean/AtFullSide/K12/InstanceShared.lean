-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/InstanceShared.lean: what the shared thread keeps at the tests on G_u and on G_omega,
members 9 and 10.

  keepsAtBase_U, keepsAtBase_O   keepsAtBase (LaterDefs.lean) at these places.

Limits. Nothing on completeness, on soundness or on what is hidden.
-/
import AtFullSide.K12.InstanceU
import AtFullSide.K12.LaterDefs
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FiveAtNine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open VerifiableInference.Desc (Place Grows)
open VerifiableInference.Desc.K1 (SmpStay)
open Desc.K14 (St)
open ProofFile.Honest.K12.AtFile (keepsU)
open ProofFile.Honest.K12.AtProof (fourOf placeU)

theorem keepsAtBase_U (Np : H2U.Places4) (Kp₁ : Place → St → St → Prop) (s s' : St) :
    keepsAtBase Np Kp₁ placeU s s' ↔ keepsU (fourOf Np).U s s' := by
  unfold keepsAtBase
  rw [if_pos rfl]

theorem keepsAtBase_O (Np : H2U.Places4) (Kp₁ : Place → St → St → Prop) (s s' : St) :
    keepsAtBase Np Kp₁ ⟨2, none, 10, .K12⟩ s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st := by
  unfold keepsAtBase
  rw [if_neg (by decide), if_pos rfl]

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.keepsAtBase_U
#print axioms ProofFile.Honest.Term.keepsAtBase_O

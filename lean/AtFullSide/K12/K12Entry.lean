-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/K12Entry.lean: what the kind K12 hands in for its lot (LotEntry, E2E/TheKOfRecord.lean) at
the base filling: the test at L, with its simulators.

  k12Entry         the entry: slot := simulatorLot matrixInput Sz.ref (K12/Sim2/SlotValueL.lean)
  k12Entry_slot    its lot, by name

By what. simulatorLot_toHLot: that lot without its simulators is proxLotAt, which the filling lays.
lotEntryOfMember, baseNamesApart: AtFullSide/K10/K10Entry.lean.

Limits. A definition and its proofs on names and sides. Nothing here says that the lot pays, that a
simulator is exact, or anything on completeness, soundness or zero knowledge.
-/
import AtFullSide.K10.K10Entry
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SlotValueL

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open AtPublicFiles.TheSides (LotEntry)
open ProofFile.Honest.Term (matrixInput baseFilling)
open ProofFile.Honest.K10 (lotEntryOfMember baseNamesApart)

/-- **What K12 hands in for its lot at the base filling.** -/
def k12Entry (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) : LotEntry (baseFilling files) Z Gr :=
  lotEntryOfMember Z Gr (simulatorLot matrixInput OnBytes.HonestTrace.Sz.ref)
    (by
      rw [simulatorLot_toHLot]
      show proxLotAt matrixInput OnBytes.HonestTrace.Sz.ref ∈
        (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
      rw [widerFillAtCPUOWM_lots]
      simp)
    (baseNamesApart files)

/-- Its lot, by name. -/
theorem k12Entry_slot (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) :
    (k12Entry files Z Gr).slot = simulatorLot matrixInput OnBytes.HonestTrace.Sz.ref := rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.k12Entry
#print axioms ProofFile.Honest.K12.Sim2.k12Entry_slot

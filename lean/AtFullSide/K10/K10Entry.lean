-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/K10Entry.lean: WHAT THE KIND K10 HANDS IN FOR ITS LOT (`LotEntry`, E2E/TheKOfRecord.lean) AT THE BASE FILLING: the closings' rows with their simulators.

  `lotEntryOfMember`   a helper for any kind: a lot with simulators whose list of sides is one of the filling's lots, in a filling whose lots' names are apart, is an entry
  `baseNamesApart`     the base filling's thirteen lots bear names that are apart: one closed test, by Lean's kernel
  **`k10Entry`**         the entry: slot := `closingsSLotAt matrixInput Sz.ref` (Johnson/Desc/ProofFile/Honest/AtPureWiderK10Rows.lean)
  `k10Entry_slot`       its lot, by name

By what. `closingsSLotAt_toHLot`: that lot without its simulators is `closeLotAt`, which the filling lays (`closeLotAt_mem_wider`, AtFullSide/Honest/K10AtTerm.lean).

Limits. A definition and its two proofs on names and sides. Nothing here says that the lot pays, that a simulator is exact, or anything on completeness, soundness or zero knowledge.
-/
import E2E.TheKOfRecord
import E2E.BaseMaker
import AtFullSide.Honest.K10AtTerm
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K10
open AtPublicFiles.TheSides (LotEntry)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.Term (matrixInput baseFilling closeLotAt_mem_wider)

/-- **A lot with simulators whose list of sides the filling lays is an entry**, where the filling's lots' names are apart. -/
def lotEntryOfMember {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} (Z : ProofFile.Pub) (Gr : ProofFile.Ground)
    (s : SLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst) (member : s.toHLot ∈ P.lots)
    (apart : (P.lots.map (·.name)).Nodup) : LotEntry P Z Gr where
  slot := s
  named := List.any_eq_true.2 ⟨s.toHLot, member, beq_self_eq_true _⟩
  fit := fun L hL e => by
    have eL : L = s.toHLot := List.inj_on_of_nodup_map apart hL member e
    rw [eL]
    rfl

set_option maxRecDepth 1000000 in
/-- The base filling's lots bear names that are apart. -/
theorem baseNamesApart (files : VerifierAndGoals.PublicFiles) : ((baseFilling files).lots.map (·.name)).Nodup := by
  show ((onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots.map (·.name)).Nodup
  decide +kernel

/-- **What K10 hands in for its lot at the base filling.** -/
def k10Entry (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) : LotEntry (baseFilling files) Z Gr :=
  lotEntryOfMember Z Gr (closingsSLotAt matrixInput OnBytes.HonestTrace.Sz.ref)
    (by
      rw [closingsSLotAt_toHLot]
      exact closeLotAt_mem_wider matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest)
    (baseNamesApart files)

/-- Its lot, by name. -/
theorem k10Entry_slot (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) :
    (k10Entry files Z Gr).slot = closingsSLotAt matrixInput OnBytes.HonestTrace.Sz.ref := rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.lotEntryOfMember
#print axioms ProofFile.Honest.K10.baseNamesApart
#print axioms ProofFile.Honest.K10.k10Entry
#print axioms ProofFile.Honest.K10.k10Entry_slot

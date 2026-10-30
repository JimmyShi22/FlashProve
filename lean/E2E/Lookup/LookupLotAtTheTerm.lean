-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupLotAtTheTerm.lean: AT THE TERM. The kind "lookup" (K3): the lot that the online
prover's filling (`onlineFilling`, E2E/TheHonestProver.lean) lays for the lookups is the lookups'
own lot, at the filling read through; and it is what the lookups' lot of rows with simulators gives
when the simulators are forgotten. Two definitions; equations between definitions. No premise.

  `lookupFillingAtTheTerm files`        the lookups' filling at the online prover
  `lookupLotIsLaidAtTheTerm`            rowLotAt of it is one of the lots of `onlineFilling files`
  `lookupLotAtTheTermIsReadThrough`     it is `theLotInst id`, as the wide fillings lay it, read
      through
  `lookupSimulatorLotAtTheTerm files`   the lookups' lot of rows with simulators at the online
      prover
  `lookupSimulatorLotAtTheTermForgets`  forgetting its simulators gives that lot
  `lookupSimulatorLotAtTheTermIsReadThrough`   THE EQUATION: its `toHLot` is `theLotInst id`, as the
                                        wide fillings lay it, read through
  `lookupSimulatorLotIsTheSixthLotAtTheTerm`   its `toHLot` is the sixth of the lots of
                                        `onlineFilling files`
  `lookupSimulatorLotIsLaidAtTheTerm`   so it is one of them

By what. `lookupLotIsAmongTheLotsReadThrough`, `lookupLotByPublicPartReadThrough`
(Johnson/Desc/ProofFile/Honest/K3/Term/LookupLotReadThrough.lean); `lookupSimulatorLotForgets`
(Johnson/Desc/ProofFile/Honest/K3/Term/LookupSimulatorLot.lean).

Limits. Equations between definitions. That no other lot of the filling lays a side at a lookup's
place is not shown here. Nothing on any property of the protocol.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupLotReadThrough
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSimulatorLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term ProofFile.Honest.Term AtPublicFiles.AtFiles AtPublicFiles.Cut

/-- **The lookups' filling at the online prover**: at the matrices' reader, the object's randomness
read as the stored tables'. -/
noncomputable def lookupFillingAtTheTerm (files : VerifierAndGoals.PublicFiles) :
    Pub → K3.Fill (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) :=
  lookupFillingThrough matrixInput.weights id (tableCoins files)

/-- **The lot that the online prover's filling lays for the lookups is the lookups' own.** -/
theorem lookupLotIsLaidAtTheTerm (files : VerifierAndGoals.PublicFiles) :
    rowLotAt (lookupFillingAtTheTerm files) ∈ (onlineFilling files).lots :=
  lookupLotIsAmongTheLotsReadThrough matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    openHonest id (tableCoins files) matrixInput.dummy

/-- **It is `theLotInst id`, as the wide fillings lay it, read through.** -/
theorem lookupLotAtTheTermIsReadThrough (files : VerifierAndGoals.PublicFiles) :
    (HLot.byPub matrixInput.weights fun wt => theLotInst id wt :
        HLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit).thru
        (Local.thru id (tableCoins files)) (Local.thru id (tableCoins files)) =
      rowLotAt (lookupFillingAtTheTerm files) :=
  lookupLotByPublicPartReadThrough matrixInput.weights id (tableCoins files)

/-- **THE LOOKUPS' LOT OF ROWS WITH SIMULATORS AT THE ONLINE PROVER.** -/
noncomputable def lookupSimulatorLotAtTheTerm (files : VerifierAndGoals.PublicFiles) :
    SLot (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) Unit Inst :=
  lookupSimulatorLot (lookupFillingAtTheTerm files)

/-- **Forgetting its simulators gives the lot that the online prover's filling lays.** -/
theorem lookupSimulatorLotAtTheTermForgets (files : VerifierAndGoals.PublicFiles) :
    (lookupSimulatorLotAtTheTerm files).toHLot = rowLotAt (lookupFillingAtTheTerm files) :=
  lookupSimulatorLotForgets (lookupFillingAtTheTerm files)

/-- **THE EQUATION AT THE TERM: forgetting the simulators gives `theLotInst id`, as the wide
fillings lay it, read through.** -/
theorem lookupSimulatorLotAtTheTermIsReadThrough (files : VerifierAndGoals.PublicFiles) :
    (lookupSimulatorLotAtTheTerm files).toHLot =
      (HLot.byPub matrixInput.weights fun wt => theLotInst id wt :
        HLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit).thru
        (Local.thru id (tableCoins files)) (Local.thru id (tableCoins files)) :=
  (lookupSimulatorLotAtTheTermForgets files).trans (lookupLotAtTheTermIsReadThrough files).symm

/-- **It is the sixth of the lots of the online prover's filling.** -/
theorem lookupSimulatorLotIsTheSixthLotAtTheTerm (files : VerifierAndGoals.PublicFiles) :
    (onlineFilling files).lots[5]? = some (lookupSimulatorLotAtTheTerm files).toHLot := by
  rw [lookupSimulatorLotAtTheTermForgets]
  exact lookupLotIsTheSixthLotReadThrough matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    openHonest id (tableCoins files) matrixInput.dummy

/-- **So its `toHLot` is one of the lots of the online prover's filling.** -/
theorem lookupSimulatorLotIsLaidAtTheTerm (files : VerifierAndGoals.PublicFiles) :
    (lookupSimulatorLotAtTheTerm files).toHLot ∈ (onlineFilling files).lots := by
  rw [lookupSimulatorLotAtTheTermForgets]
  exact lookupLotIsLaidAtTheTerm files

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.lookupFillingAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupLotIsLaidAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupLotAtTheTermIsReadThrough
#print axioms AtPublicFiles.Lookup.lookupSimulatorLotAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupSimulatorLotAtTheTermForgets
#print axioms AtPublicFiles.Lookup.lookupSimulatorLotAtTheTermIsReadThrough
#print axioms AtPublicFiles.Lookup.lookupSimulatorLotIsTheSixthLotAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupSimulatorLotIsLaidAtTheTerm

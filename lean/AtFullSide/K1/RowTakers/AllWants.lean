-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/RowTakers/AllWants.lean: THE FIRST OF THE WRITTEN BOOK's TEN PIECES (the 7,940
stretches' entries): AT EACH g = 1 … 11 THE WALK WITHOUT A TEST ON THE NUMBERS GIVES rowSpentAt g:
THE OWNER HAS NO OTHER ENTRY THERE; AND A TWIN THAT SAYS NO. EVALUATIONS IN LEAN's KERNEL (decide
+kernel; no compiled code). A sister of AllDefs.lean in this folder; the whole and its limits:
AtFullSide/K1/OwnerEntriesAtSwitches.lean's head. A TRIAL THAT COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.RowTakers.AllDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open VerifiableInference.Desc (Place KindName)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At each of the eleven groups the stretches' entries of that owner are the written rows.** -/
theorem ownedWantsB : ((List.range 11).all fun i =>
    decide (ownedIn (rawWantsW.map (·.entry)) (i + 1) = rowSpentAt (i + 1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A NEGATIVE TEST: with the first row struck the test says no. -/
theorem ownedWantsB_bent :
    decide (ownedIn (rawWantsW.map (·.entry)) 1 = (rowSpentAt 1).tail) = false := by
  decide +kernel

end AtFullSide.K1

#print axioms AtFullSide.K1.ownedWantsB
#print axioms AtFullSide.K1.ownedWantsB_bent

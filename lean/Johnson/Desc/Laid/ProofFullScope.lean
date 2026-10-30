-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Laid/ProofFullScope.lean: in scope, what Johnson/Desc/Laid/ProofFull.lean's value lays
as the proof
file's data is the written data, a closed term.

  laidPOf_written     **in scope, where the value is laid, its data are `writtenPFull`**
  laidPOf_depth32     in scope, where the value is laid, its data stand at the depth 32
  laidPOf_rounds      in scope, where the value is laid, the description's declared rounds, written,
                      are the written lists of the full size

How: the value's fourth refusal asks `seatPinnedProof` at the same parameter file of which the scope
is asked (`laidPOf_ok`); in scope that file's strict scan has the full size's key, and a yes of the
test gives the written lists, the depth and the data (`seat_in_scope`,
Johnson/Goal/Numbers/PlanWrittenDescScope.lean).

Limits: the pin holds at this value: whoever calls `ProofFile.onlineDescription` by another road does not get it.
Nothing is said where the value refuses, nor out of scope. Nothing on what a yes of the decision
gives.

-/
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Goal.Numbers.PlanWrittenDescScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Full
open OnBytes.Maker
open VerifiableInference.PlanWritten (seat_in_scope)
open Johnson.G (writtenPFull)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : RunPF}

/-- **In scope, where the value is laid, its data are the written data.** -/
theorem laidPOf_written (hZ : VerifierAndGoals.InScope Z = true)
    (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) : D = writtenPFull := by
  obtain ⟨F, -, -, hD, hs, -⟩ := laidPOf_ok h
  exact Except.ok.inj (hD.symm.trans (seat_in_scope _ F Z hZ (asks_written hs)).2.2)

/-- In scope, where the value is laid, the description's depth of the table, at which the data
stand, is 32. -/
theorem laidPOf_depth32 (hZ : VerifierAndGoals.InScope Z = true)
    (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) : D.a = 32 := by
  obtain ⟨F, -, -, hD, hs, -⟩ := laidPOf_ok h
  exact (data_depth F hD).trans (seat_in_scope _ F Z hZ (asks_written hs)).2.1

/-- In scope, where the value is laid, the description's declared rounds, written, are the written
lists of the full size. -/
theorem laidPOf_rounds (hZ : VerifierAndGoals.InScope Z = true)
    (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) :
    ∃ F, ProofFile.onlineDescription o Z.pol Z.lay Z.KL = .ok F ∧
      Johnson.G.OfPlan.writtenOf "proof file" F.roundsDeclaredByBlocks = .ok Johnson.G.dryProofFull := by
  obtain ⟨F, hd, -, -, hs, -⟩ := laidPOf_ok h
  exact ⟨F, hd, (seat_in_scope _ F Z hZ (asks_written hs)).1⟩

end LPFD.Full

#print axioms LPFD.Full.laidPOf_written
#print axioms LPFD.Full.laidPOf_depth32
#print axioms LPFD.Full.laidPOf_rounds

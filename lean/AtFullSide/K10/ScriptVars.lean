-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptVars.lean: the closing of a segment (K10): THE CODE SWITCH THAT LEADS INTO A SEGMENT COUNTS THE NEXT FOLD's ROW
VARIABLES AS THAT SEGMENT's CLOSING DOES: under the library's hypothesis, at a closing that `Tied` names
(Johnson/Desc/ProofFile/Honest/K10/SimLot.lean) and the written place of the code switch of the same segment: `p.foldVars = Qc.k`: the
field vars of `FreshBySwitch` (Honest/K10/Pay/XchFreshField.lean). And at the first segment, into which no switch leads, the closing's
two numbers are 8 and 0: those at which the first segment's sending lets its fresh mask's table ride
(`fresh_opening`, AtFullSide/K10/ScriptPublic.lean).

  `varsW`            a closed test, by Lean's kernel: at each written closing and each written place of the same segment the two counts
                     are one. `vars_not_idle`: 24 of the 25 written closings have such a place. `vars_can_fail`: with one count raised by
                     1 no pair passes
  `zeroW`            a closed test: the written closing of segment 0 is there, and has k = 8 and h = 0
  `par_of_tied`      under the hypothesis: the closing's numbers are a member of the written list, of the segment's number
  **`vars_of_tied`**   p.foldVars = Qc.k
  **`zero_of_tied`**   at segment 0: Qc.k = 8 ∧ Qc.h = 0

By: `pars_at_head` (AtFullSide/K10/PaysAtHead.lean); `k10Par_fields`, `k9Where_fields` (Johnson/IMR/LinkSeat.lean).

Limits. Public numbers alone. That a state's own height at the first closing is the plan's h is not said here. The hypothesis is a
premise. Closed facts by Lean's kernel. The full size and the older hash alone. No property is claimed.
-/
import AtFullSide.K10.PaysAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Close (Par)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K2.Law (placesW)

set_option maxRecDepth 1000000 in
/-- At each written closing and each written place of the same segment the two counts are one. -/
theorem varsW : (parsW.all fun P => placesW.all fun p => !(p.link == P.link) || p.foldVars == P.k) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test is not idle: 24 of the 25 written closings have a place of their segment. -/
theorem vars_not_idle : parsW.length = 25 ∧
    (parsW.filter fun P => placesW.any fun p => p.link == P.link).length = 24 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: with one count raised by 1 no pair passes. -/
theorem vars_can_fail :
    (parsW.any fun P => placesW.any fun p => p.link == P.link && p.foldVars == P.k + 1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written closing of segment 0. -/
theorem zeroW : (parsW.any fun P => P.link == 0) = true ∧
    (parsW.all fun P => P.link != 0 || (P.k == 8 && P.h == 0)) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The closing's numbers are a member of the written list, of the segment's number. -/
theorem par_of_tied (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : Nat}
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l pw Qc blk) :
    Qc ∈ parsW ∧ Qc.link = l := by
  refine ⟨?_, (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1⟩
  rw [← pars_at_head h]
  exact Td.2.2.2.2.1

/-- **THE SWITCH's COUNT OF THE NEXT FOLD's ROW VARIABLES IS THE CLOSING's.** -/
theorem vars_of_tied (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : Nat}
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l pw Qc blk)
    {p : SwitchPlace} (hpw : placesW.find? (·.link == l) = some p) : p.foldVars = Qc.k := by
  obtain ⟨hQ, hl⟩ := par_of_tied h Td
  have hp : p ∈ placesW := List.mem_of_find?_eq_some hpw
  have hpl : (p.link == l) = true := List.find?_some (p := fun y : SwitchPlace => y.link == l) hpw
  have t := List.all_eq_true.1 (List.all_eq_true.1 varsW Qc hQ) p hp
  rw [hl, hpl] at t
  exact beq_iff_eq.1 t

/-- **AT THE FIRST SEGMENT.** -/
theorem zero_of_tied (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp 0 pw Qc blk) :
    Qc.k = 8 ∧ Qc.h = 0 := by
  obtain ⟨hQ, hl⟩ := par_of_tied h Td
  have t := List.all_eq_true.1 zeroW.2 Qc hQ
  rw [hl] at t
  have t' : (Qc.k == 8 && Qc.h == 0) = true := t
  rw [Bool.and_eq_true] at t'
  exact ⟨beq_iff_eq.1 t'.1, beq_iff_eq.1 t'.2⟩

end AtFullSide.K10

#print axioms AtFullSide.K10.varsW
#print axioms AtFullSide.K10.vars_not_idle
#print axioms AtFullSide.K10.vars_can_fail
#print axioms AtFullSide.K10.zeroW
#print axioms AtFullSide.K10.par_of_tied
#print axioms AtFullSide.K10.vars_of_tied
#print axioms AtFullSide.K10.zero_of_tied

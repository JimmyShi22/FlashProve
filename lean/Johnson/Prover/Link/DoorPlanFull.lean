-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorPlanFull.lean: THE PLAN's SHARE OF THE DOOR's PREMISES (DoorPlan,
Johnson/Prover/Link/DoorPay.lean) HOLDS AT THE LINK's TYPED PARAMETERS OF THE FULL SIZE: frP
(Johnson/Desc/K15/TypedP.lean) and the place's numbers that the description itself makes of them
(p12Of frP, Johnson/Desc/K15/HsemSays.lean).

Main names (namespace Johnson.Prover.Link.Full).
  pF, curF, nxtF, iF, nF   the place's numbers; its first two stages; the numbers of their codes.
  full_ahead .. full_one   DoorPlan's twenty-one clauses, ONE LEMMA A CLAUSE.
  doorPlan_full   THE STATEMENT.

HOW EACH IS PROVED. full_early: fr_early (Johnson/Desc/K15/PubAtTyped.lean). THE OTHER
TWENTY: BY LEAN's KERNEL, "decide +kernel" ON THAT ONE CLAUSE ALONE, as the library does at frP
(PubAtTyped.lean; Johnson/Desc/Link/LinkDoorsFull.lean, LinkWrittenMade.lean). No decision runs over
the whole test.

Limits. That the parameters that run (p15Of c of three public files) are frP is a law in scope
elsewhere (Johnson/Goal/Conditions/LinkInScope.lean [not in this library]), not called here.
Nothing at the small
example's sizes. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorPay
import Johnson.Desc.K15.PubAtTyped

set_option autoImplicit false

namespace Johnson.Prover.Link.Full
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 Desc.K15

/-- the numbers of the test's place -/
def pF : P12 := p12Of frP
/-- its first and its second stage -/
def curF : Fmt.M1.Stage := pF.nums.stages.getD 0 default
def nxtF : Fmt.M1.Stage := pF.nums.stages.getD 1 default
/-- the numbers of their codes -/
def iF : Nat × Nat := pF.idx.getD 0 default
def nF : Nat × Nat := pF.idx.getD 1 default

theorem full_ahead : frP.S.masksAhead = true := by decide +kernel
theorem full_idx0 : pF.idx[0]? = some iF := by decide +kernel
theorem full_idx1 : pF.idx[1]? = some nF := by decide +kernel
theorem full_code : frP.S.code = iF.1 := by decide +kernel
theorem full_maskCode : frP.S.maskCode = iF.2 := by decide +kernel
theorem full_base : frP.codes.base[iF.1]? = some ⟨curF.C.a, curF.C.l, curF.C.r⟩ := by decide +kernel
theorem full_maskC : frP.codes.mask[iF.2]? = some ⟨curF.Z.a, curF.Z.l, curF.Z.r⟩ := by
  decide +kernel
theorem full_base1 : frP.codes.base[nF.1]? = some ⟨nxtF.C.a, nxtF.C.l, nxtF.C.r⟩ := by
  decide +kernel
theorem full_mask1 : frP.codes.mask[nF.2]? = some ⟨nxtF.Z.a, nxtF.Z.l, nxtF.Z.r⟩ := by
  decide +kernel
theorem full_layK : ceilLog2 frP.S.rows + 1 = curF.k := by decide +kernel
theorem full_layH : curF.h = 0 := by decide +kernel
theorem full_freshRows : (foldMaskNotice (linkFoldShape frP.S)).shape.maskRows = 2 ^ curF.h := by
  decide +kernel
theorem full_freshCode : (foldMaskNotice (linkFoldShape frP.S)).shape.maskCode = iF.2 := by
  decide +kernel
theorem full_stage : K12.stageOk false curF = true := by decide +kernel
theorem full_stage1 : nxtF.Z.a ≤ nxtF.C.a := by decide +kernel
theorem full_vars : curF.k + ceilLog2 curF.C.l ≤ 63 := by decide +kernel
theorem full_codes : codesFit pF { codes := frP.codes } = true := by decide +kernel
theorem full_pub : H2K.Pub.pubOk pF frP.codes = true := by decide +kernel
theorem full_free : pF.nums.free = 1 := by decide +kernel
theorem full_early : pF.early = true := fr_early

theorem full_one (l : TreeLay) (h : layTrees frP.codes (linkMessage frP.S 1) = some l) :
    l.shapes.size = 1 := by
  have a : (match layTrees frP.codes (linkMessage frP.S 1) with
    | some l => decide (l.shapes.size = 1)
    | none => true) = true := by decide +kernel
  rw [h] at a
  exact of_decide_eq_true a

/-- **DoorPlan AT THE FULL SIZE.** -/
theorem doorPlan_full : DoorPlan frP.S frP.codes pF curF nxtF iF nF where
  ahead := full_ahead
  idx0 := full_idx0
  idx1 := full_idx1
  code := full_code
  maskCode := full_maskCode
  base := full_base
  maskC := full_maskC
  base1 := full_base1
  mask1 := full_mask1
  layK := full_layK
  layH := full_layH
  freshRows := full_freshRows
  freshCode := full_freshCode
  stage := full_stage
  stage1 := full_stage1
  vars := full_vars
  early := full_early
  codes := full_codes
  pub := full_pub
  free := full_free
  one := full_one

end Johnson.Prover.Link.Full

#print axioms Johnson.Prover.Link.Full.full_ahead
#print axioms Johnson.Prover.Link.Full.full_idx0
#print axioms Johnson.Prover.Link.Full.full_idx1
#print axioms Johnson.Prover.Link.Full.full_code
#print axioms Johnson.Prover.Link.Full.full_maskCode
#print axioms Johnson.Prover.Link.Full.full_base
#print axioms Johnson.Prover.Link.Full.full_maskC
#print axioms Johnson.Prover.Link.Full.full_base1
#print axioms Johnson.Prover.Link.Full.full_mask1
#print axioms Johnson.Prover.Link.Full.full_layK
#print axioms Johnson.Prover.Link.Full.full_layH
#print axioms Johnson.Prover.Link.Full.full_freshRows
#print axioms Johnson.Prover.Link.Full.full_freshCode
#print axioms Johnson.Prover.Link.Full.full_stage
#print axioms Johnson.Prover.Link.Full.full_stage1
#print axioms Johnson.Prover.Link.Full.full_vars
#print axioms Johnson.Prover.Link.Full.full_codes
#print axioms Johnson.Prover.Link.Full.full_pub
#print axioms Johnson.Prover.Link.Full.full_free
#print axioms Johnson.Prover.Link.Full.full_early
#print axioms Johnson.Prover.Link.Full.full_one
#print axioms Johnson.Prover.Link.Full.doorPlan_full

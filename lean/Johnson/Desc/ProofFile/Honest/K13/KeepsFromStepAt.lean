-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/KeepsFromStepAt.lean: kind K13, the members' batching: THE KIND's
CLAUSE `K13KeepsAll` FROM THE ACCEPTING STEP OF NUMBER 355 OF THE LIBRARY's OWN LIST, under the
hypothesis h under which that list is laid: KeepsFromStep.lean of this folder at that list. Two
statements with their proofs: calls alone.
Main names:
  `k13_memberClean_at`: `MemberClean` there.
  `k13_keeps_at`: **the clause there**: no premise but h.

What is not claimed. That the member's step accepts anywhere. That h can be met. That h holds
together with a thread's sentence anywhere. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.KeepsFromStep
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K13.Honest (K13KeepsAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- At the library's own list, number 355. -/
theorem k13_memberClean_at : MemberClean cF.blocksInOrder 355 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact memberClean_open O fun _ hb => m3_member_place h hb

/-- **The clause from the accepting step of number 355 of the library's own list.** -/
theorem k13_keeps_at (ft : Nat) :
    ∀ blk, cF.blocksInOrder[355]? = some blk → ∀ s s', Johnson.Desc.First.Walk.Tied.StepYes ft blk s s' →
      K13KeepsAll h.𝔇.P13 s s' :=
  k13_keeps_stepYes (k13_memberIs_at h) (k13_memberClean_at h) ft

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_memberClean_at
#print axioms ProofFile.Honest.K13.k13_keeps_at

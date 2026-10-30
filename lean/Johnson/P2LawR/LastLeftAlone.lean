-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LastLeftAlone.lean: THE JOIN lastLeft_at_head WITH NO PREMISE BESIDE THE HEAD:
  `AtMgA.LastLeftAt` (what is left of the last chain's field at the value) FROM THE
  HEAD AT o := OnBytes.secondHashFunction. THE HEAD IS ITSELF MADE OF CLOSED TESTS AND FIELDS, AND THIS ROAD
  SPENDS THEM: the entry tests' two rows on written values (cutRow, madeRow) and the fields
  LaidAt.planOk, At.PlanOk.radii, At.PlanOk.shape. One theorem: calls.

AGAINST THE JOIN's FORM IN Johnson/P2LawR/LastLeftAtHead.lean (there:
  LastRest := core: fifteen tests as one) AND AGAINST radB_at_head (Johnson/IMR/RadAtHead.lean),
  whose premise radWB = true is one closed Bool, which Lean's kernel has not carried: here the
  premise C of planOk₃_at_join is had by core_of_two_radii
  (Johnson/P2LawR/CoreOfTwoRadii.lean), and its two tests on radii are theorems from the head:
  P5J.AtMg.two_radii (Johnson/P2LawR/TwoRadiiAtHead.lean, over the written
  radii in scope: rad_in_scope, Johnson/HB/LLHARD/RadiiInScope.lean).
WHICH DOOR: it reads rows 9 and 10 of the proof file's entry tests (the two pins): so it stands over
  their list of thirteen rows and over that of fourteen (one row appended).
Is it empty? Not at `VerifierAndGoals.storedPublicFiles` (`headMember_zFull`, AtFullSide/Top/, a side library); the
  theorem says nothing where there is no head. THE CONDITION "THE ROWS' MAKER RETURNS" IS NOT DONE
  AWAY WITH: IT STANDS IN THE HEAD: two_radii has it from the head's own field At.PlanOk.radii. The
  full size alone. At OnBytes.secondHashFunction alone. Nothing on what a radius means: numbers are compared.
  Nothing on soundness. A raised limit stands in this file (maxRecDepth 40000).
-/
import Johnson.P2LawR.LastLeftOfCoreJ
import Johnson.P2LawR.CoreOfTwoRadii
import Johnson.P2LawR.TwoRadiiAtHead
import Johnson.P2LawR.HSAtLeft
import Johnson.P2LawR.LdAtLeft
import Johnson.P2LawR.SitsAtLeft
import Johnson.P2LawR.RestOfDoor
import Johnson.Desc.K14.Law.SharedConstChainOkAtHead
import Johnson.ToldDescR.HRcAtLeftGen
import Johnson.Desc.Last.OwnAtHead
import Johnson.IMR.ToldPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers openSets sampledIn start)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT OF THE LAST CHAIN's FIELD, FROM THE HEAD ALONE.** -/
theorem AtMgA.lastLeft_at_head_alone (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) :
    h.LastLeftAt := by
  obtain ⟨h2, hE, hEnd, hIdx, hNum, hcut, hmade⟩ := h.rest_of_door
  have hy : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first
      Zp.made = true :=
    VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [hmade, Bool.or_true])
  have hII : ∀ a, (h.toAtMg.mq h.𝔇).pub .indexIs a = K13.indexIsC 4 a.2 := by
    intro a
    rw [VerifiableInference.Desc.Last.mq_indexIs h.toAtMg h.𝔇 a, hIdx]
  exact h.lastLeft_of_coreJ _root_.Meaning.Carry.k2Told_paid (Sh.tests_at_head h hy _) h2 hE hEnd
    (P2Law.Left.core_of_two_radii h (fun st rest e => (h.toAtMg.two_radii st rest e).1)
      (fun st rest e => (h.toAtMg.two_radii st rest e).2))
    (fun q y ho hr hm => ToldDesc.hRc_at_left_gen h.toAtMg (h.toAtMg.mq h.𝔇) hII
      (P2Law.Left.ld_at_head h.toAtMg hy) (fun q => h.toAtMg.typed q.1)
      ((ToldDesc.planSits_iff _ _ _ _ _).1 (P2Law.Left.sits_at_head h.toAtMg hy)) hNum hcut hmade
      q y ho hr hm)
    (P2Law.Left.hS_at_left h hy)

end P5J

#print axioms P5J.AtMgA.lastLeft_at_head_alone

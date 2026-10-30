-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/OwnRoundsStepClosedForm.lean: the step of the layers' own rounds
on shapes (k4G) in closed form, but for the parts left out of the own record: from the tests on the
plan and on the shape before, the host's count of the padding keys (hL) and 0 < V, it returns; the
ledger's shape, the tables' shapes and what stays of the own record are closed forms, and so is the
list of what the merge leaves of each weight claim (mergeRecordsShapes,
MergeRecordsClosedForm.lean). Also the letter k4own (a field of TabLetters) at the record LWn X.
General; nothing is evaluated.

Why. So a written value after this step can be compared with closed forms, without running the
hearing. A written value is a shape written out as a Lean term.

  mergeSlotsCount, mergeSlots_sizeIsCount   the number of the merge's slots, by the plan.
  **ownRoundsStep_closedForm**   these premises give that the step returns a shape with these closed
                          forms, for some own record, and that what stays of it is
                          ownRecordClosedForm.
  ownRoundsLetter_atNumerals   the letter k4own at a group that has a plan is ownOf at the
                          parameters that the cell sets (k4Par).

Limits. One way, from the premises. No test is shown to accept here. What the parts left out of the
own record hold is not said, and that no later member opens them is not shown here. What any of
this costs Lean's kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.OwnRecordClosedForm
import Johnson.AtFull.Shape.Lines.Layers.OwnRoundsTableShapes
import Johnson.AtFull.Shape.Lines.Layers.HearingAtBlankRun
import Johnson.AtFull.Shape.Lines.Layers.MergeRecordsClosedForm
import Johnson.AtFull.Shape.Lines.Layers.OwnRoundsGuardLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own TableAt)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K8.Honest (ledBlank)

/-- The number of the merge's slots, by the plan. -/
def mergeSlotsCount (hp : HPlan2) (g : Nat) : Nat :=
  hp.NCL - (if (g == 0) = true then 1 else 0) + (if (g == 0) = true then 1 else 0)

/-- The library's mergeSlots has that number of slots. -/
theorem mergeSlots_sizeIsCount (hp : HPlan2) (g : Nat) (o : Own) :
    (mergeSlots hp g o).size = mergeSlotsCount hp g := by
  unfold mergeSlots mergeSlotsCount
  rw [Array.size_append, Array.size_map, Array.size_range]
  by_cases hg : (g == 0) = true
  · rw [if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg]
    rfl

/-- **The step on shapes, in closed form but for the parts left out of the own record.** -/
theorem ownRoundsStep_closedForm (p : Par) {a : ChainSh} {h : HeardAll} {L : LedSh} (hlook : a.look
    = some h)
    (hled : a.led = some L) (hP : k4PlanB p = true)
    (hL : VerifiableInference.Desc.First.Look.laidLayers p.P = some p.P.y.fo.pub)
    (hF : k4FrontB p 0 a = true) (hV : 0 < p.P.V) :
    ∃ (iU3 : Nat) (tab : List TableAt) (laid : List (Layer.TableAsk × List (Nat × Nat))) (n : Nat)
      (ow : OwnSh) (recs : List RecSh),
      p.hp.tl.ix.U.getD 2 none = some iU3 ∧
      RtPub.tablesAt p.P p.g = some (tab, laid, n) ∧
      mergeRecordsShapes p.P p.hp p.g (mergeSlotsCount p.hp p.g) = some recs ∧
      k4G p a = some ((((a.setLed (hearLedU p.P p.hp p.g L)).layOwn (some ow)).layTables
        (some (tableShapesClosedForm p.P.y h laid))).setRowsOwed none) ∧
      ownRecordLessParts ow = ownRecordClosedForm p.P p.hp p.g iU3 tab h L.next (L.next + k4Takes
          p.P p.hp p.g) recs := by
  have hF0 := hF
  unfold k4FrontB at hF
  rw [Bool.and_eq_true, beq_iff_eq, hled, hlook] at hF
  obtain ⟨hh1, hF2⟩ := hF
  have hF3 : (roomB L (k4Takes p.P p.hp p.g + 0) && lookB p.P h L) = true := hF2
  rw [Bool.and_eq_true] at hF3
  obtain ⟨iU3, tab, o, G, e, -, -, a3, a4, hl⟩ := hearing_returnsAtBlankRun p 0 h L hP hL hF3.1
      hF3.2 hV
  obtain ⟨-, -, iU3', tab', laid, n, TS, claimsP, pts, hd2, hu, -, ht, -, hv, -, -, -, -, hfo⟩ :=
    hear_public e
  have et : tab' = tab := congrArg Layer.Env.tab (hv.symm.trans a4.v)
  have ei : iU3' = iU3 := congrArg Layer.Env.iU3 (hv.symm.trans a4.v)
  subst et ei
  have hf := funsOf_shapes hfo
  have hs := ownRecord_isClosedForm e a4
  have hlk : lookB p.P (heardAll h.blank) (ledSh (ledBlank L)) = true := by
    rw [heardAll_blank, ledSh_blank]
    exact hF3.2
  have hz : RtPub.zkFits p.P h.blank.zk = true := (look_of_B hlk).zk
  have hr := hearing_mergeRecordsShapes e a4 hz rfl
  rw [mergeSlots_sizeIsCount] at hr
  rw [heardAll_blank] at hs hf
  have hn : (ledBlank L).next = L.next := rfl
  rw [hn, a3] at hs
  have ht' : RtPub.tablesAt p.P p.g = some (tab', laid, n) := ht
  have hf' : o.funs.toList.map funSh = tableShapesClosedForm p.P.y h laid := hf
  have hs' : ownRecordLessParts (ownSh o) = ownRecordClosedForm p.P p.hp p.g iU3' tab' h L.next
      (L.next + k4Takes p.P p.hp p.g) (o.wo.recs.map recSh) := hs
  have hr' : mergeRecordsShapes p.P p.hp p.g (mergeSlotsCount p.hp p.g) =
      some (o.wo.recs.map recSh) := hr
  refine ⟨iU3', tab', laid, n, ownSh o, o.wo.recs.map recSh, hu, ht', hr', ?_, hs'⟩
  unfold k4G
  rw [if_neg (by rw [hh1]; decide), hlook, hled]
  show (ownOf p h L).map _ = _
  unfold ownOf
  rw [e]
  show some ((((a.setLed (ledSh G)).layOwn (some (ownSh o))).layTables
    (some (o.funs.toList.map funSh))).setRowsOwed none) = _
  rw [hl, hf']

end OnBytes.Desc.First.K4.Rt

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model

/-- The letter k4own at LWn X, where the group has a plan: the hearing on shapes at the parameters
that the cell sets. -/
theorem ownRoundsLetter_atNumerals (X : Verify.Public) (g : Nat) {hp : Layer.HPlan2} (hG : X.G[g]? =
    some hp) :
    (LWn X).k4own g = OnBytes.Desc.First.K4.Rt.ownOf (k4Par (LWn X).XG hp g) := by
  show k4ownX X g = _
  unfold k4ownX
  rw [hG]
  rfl

end Johnson.AtFull.Shape

#print axioms OnBytes.Desc.First.K4.Rt.mergeSlotsCount
#print axioms OnBytes.Desc.First.K4.Rt.mergeSlots_sizeIsCount
#print axioms OnBytes.Desc.First.K4.Rt.ownRoundsStep_closedForm
#print axioms Johnson.AtFull.Shape.ownRoundsLetter_atNumerals

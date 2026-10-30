-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/Kit.lean: THE HEAD's EXAMPLE: publicOfO AT THE STORED FULL-SIZE FILES:
THE TOOLS OF THE JOIN, AND THE SMALL FACTS ON THE LAYERS' LAYOUT yFull, EACH UNDER A NAME.
  onOk_ex'     a yes of the owners' file's onOk comes of a return
  at_yBase     a closed fact «Small.withY f = true» speaks of yBase
  open_pubC    a closed fact «withPubC f = true» speaks of yFull: the scales, the weights' layout,
  the
               table of rotations and the layers' public numbers return there, and f accepts them
  border_W     BY LEAN's KERNEL: the border that the model's head reads is the written one; a bent
  twin
               rejects (border_no)
  yFull_dq · yFull_NGr · yFull_lPd · yFull_border · yFull_tauFC · yFull_p3 · yFull_p4: dq and lPd
  are
               calls of Values.lean's dq_W | lPd_W
LIMITS. Tools, and closed facts on numbers. Nothing here says that publicOfO returns. No soundness
is
claimed.
-/
import Johnson.AtFull.Public.Values
import Johnson.AtFull.Public.Owners
import Johnson.AtFull.Public.Small
import Johnson.Desc.Kinds.Law.K06Condition
import Johnson.Unfolds.LedgerTables
import Johnson.Road.HeadTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtFull.Public
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Road.K4.Trial.Values (PW hW yBase foW kbmW yFull base_W polLayout_W noFill_W noAsk_W
  planeCols_W withY withY_eq dq_W lPd_W)
open OnBytes.Road.K4.Trial.AttK7Owners (withPubC onOk)
open OnBytes.Tie.Pv.Plan (scalesF)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.bFull)

/-! ## Tools -/

/-- A yes of the owners' file's onOk comes of a return. -/
theorem onOk_ex' {ε α : Type} {x : Except ε α} {f : α → Bool} (h : onOk x f = true) :
    ∃ a, x = .ok a ∧ f a = true := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => exact Bool.noConfusion (show false = true from h)

/-- A closed fact of Small.lean speaks of yBase. -/
theorem at_yBase {f : Layer.Lay → Bool} (h : OnBytes.Road.K4.Trial.Small.withY f = true) :
    f yBase = true := (withY_eq f).symm.trans (show withY f = true from h)

/-- **A closed fact «withPubC f = true» speaks of yFull.** -/
theorem open_pubC {f : Layer.Pub → Bool} (h : withPubC f = true) :
    ∃ (sc : Layer.Scales) (wsLay : WsLay) (rope : Array Nat) (L : Layer.Pub),
      Layer.scalesOf yFull.h scalesF.toArray = .ok sc ∧
      wsLayOf (weightShape PW yFull) yFull.h.p3 PW.lkW = .ok wsLay ∧
      Layer.ropeOf yFull.h = .ok rope ∧
      Layer.Pub.of yFull sc rope wsLay PW.h.V #[] PW.settings = .ok L ∧ f L = true := by
  unfold withPubC OnBytes.Road.K4.Trial.AttK7Owners.withLookC at h
  obtain ⟨y0, e0, h⟩ := onOk_ex' h
  obtain rfl : yBase = y0 := Except.ok.inj (noFill_W.symm.trans e0)
  obtain ⟨fo, e1, h⟩ := onOk_ex' h
  obtain rfl : foW = fo := Except.ok.inj (noAsk_W.symm.trans e1)
  obtain ⟨kbm, e2, h⟩ := onOk_ex' h
  obtain rfl : kbmW = kbm := Except.ok.inj (planeCols_W.symm.trans e2)
  obtain ⟨sc, e3, h⟩ := onOk_ex' h
  obtain ⟨wsLay, e4, h⟩ := onOk_ex' h
  obtain ⟨rope, e5, h⟩ := onOk_ex' h
  obtain ⟨L, e6, h⟩ := onOk_ex' h
  exact ⟨sc, wsLay, rope, L, e3, e4, e5, e6, h⟩

/-! ## The small facts on the layout -/

set_option maxRecDepth 1000000 in
/-- **By the kernel**: the border that the model's head reads of the layers' layout is the written
one. -/
theorem border_W : withY (fun y => decide (borderOf y = Cond.bFull)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A bent twin: the written border with one column more: rejected. -/
theorem border_no : withY (fun y => decide (borderOf y =
    { Cond.bFull with kxb := Cond.bFull.kxb + 1 })) = false := by
  decide +kernel

theorem yBase_NGr : yBase.NGr = 12 := by
  have hn := at_yBase OnBytes.Road.K4.Trial.Small.numbers
  simp only [Bool.and_eq_true, beq_iff_eq] at hn
  exact hn.1.2

theorem yBase_border : borderOf yBase = Cond.bFull :=
  of_decide_eq_true ((withY_eq _).symm.trans border_W)

theorem yFull_dq : yFull.dq = 5120 := dq_W
theorem yFull_NGr : yFull.NGr = 12 := yBase_NGr
theorem yFull_lPd : yFull.lPd = 13 := lPd_W
theorem yFull_border : borderOf yFull = Cond.bFull := yBase_border
theorem yBase_tauFC : yBase.tauFC = OnBytes.Road.Hd.tauFCw := OnBytes.Road.Hd.tauFC_of_base base_W
theorem yFull_tauFC : yFull.tauFC = OnBytes.Road.Hd.tauFCw := yBase_tauFC

theorem yFull_p3 : yFull.h.p3 = true := by
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  exact (Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hR polLayout_W).1

theorem yFull_p4 : yFull.h.p4 = true := by
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  exact Johnson.Unfolds.ledger_h4 VerifierAndGoals.inScope_full hR polLayout_W

end AtFull.Public

#print axioms AtFull.Public.onOk_ex'
#print axioms AtFull.Public.at_yBase
#print axioms AtFull.Public.open_pubC
#print axioms AtFull.Public.border_W
#print axioms AtFull.Public.border_no
#print axioms AtFull.Public.yBase_NGr
#print axioms AtFull.Public.yBase_border
#print axioms AtFull.Public.yFull_dq
#print axioms AtFull.Public.yFull_NGr
#print axioms AtFull.Public.yFull_lPd
#print axioms AtFull.Public.yFull_border
#print axioms AtFull.Public.yBase_tauFC
#print axioms AtFull.Public.yFull_tauFC
#print axioms AtFull.Public.yFull_p3
#print axioms AtFull.Public.yFull_p4

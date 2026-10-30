-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6CallsAtHead.lean: the condition `callsC` of `K6LeftSeven`
(Johnson/Desc/Kinds/Law/K6LeftSeven.lean), to the letter, at the head, under one named premise:
`callNamesB` at the built segment 24's list of arrays. One theorem: the test is its test at plain
values (`callsSeatedC_view`, Johnson/Desc/Kinds/Law/K6CallsView.lean), and that is `callsText`
(Johnson/HB/LLHARD/K6CallsText.lean) by definition.

Row or tool. A payer for a premise of another law.

Ground. It has not been through Lean.
(Where this and lean/THEOREM.md differ, the page holds.)

Limits. Those of K6CallsText.lean: the premise is not shown.

(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6CallsText
import Johnson.Desc.Kinds.Law.K6CallsView
import Johnson.Desc.Kinds.Law.DAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- **`K6LeftSeven.callsC`, at the head, from the eight names.** -/
theorem callsC_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hNm : P5J.callNamesB ((dAt h).sent.arrayOf.getD 24 #[]) = true) :
    AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true := by
  rw [AtFold.callsSeatedC_view]
  exact P5J.callsText_at_head h hNm

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.callsC_at_head

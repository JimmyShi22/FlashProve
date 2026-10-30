-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6MaskAtHead.lean: the condition `maskC` of `K6LeftSeven`
(Johnson/Desc/Kinds/Law/K6LeftSeven.lean), to the letter, at the head: no premise beside the head.
One theorem: the test is its test at plain values (`maskMeetsC_view`,
Johnson/Desc/Kinds/Law/K6CallsView.lean), and that is `maskText` (Johnson/HB/LLHARD/K6MaskText.lean)
by definition.

Row or tool. A payer for a premise of another law.

Ground. It has not been through Lean.
(Where this and lean/THEOREM.md differ, the page holds.)

Limits. Those of K6MaskText.lean. Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6MaskText
import Johnson.Desc.Kinds.Law.K6CallsView
import Johnson.Desc.Kinds.Law.DAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- **`K6LeftSeven.maskC`, at the head.** -/
theorem maskC_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    AtFold.maskMeetsC (dAt h).arr (dAt h).ms (dAt h).N (dAt h).sent (dAt h).l3.rad x.link
      ((dAt h).l3.seat x.link false) (P5J.At.num Zp 24 0) (P5J.At.X Zp).H.ns = true := by
  rw [AtFold.maskMeetsC_view]
  exact P5J.maskText_at_head h

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.maskC_at_head

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6NamedAtHead.lean: the condition `namedC` of `K6LeftSeven`
(Johnson/Desc/Kinds/Law/K6LeftSeven.lean), to the letter, at the head: from the head alone. One
theorem: a call of `namedText_at_head` (Johnson/HB/LLHARD/K6NamedText.lean); the test's text there
and the test here are one by definition.

Row or tool. A payer for a premise of another law.

Ground. It imports two files (PlanK6Planes.lean, DAtConst.lean).
(Where this and lean/THEOREM.md differ, the page holds.)


Limits. Those of K6NamedText.lean. Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6NamedText
import Johnson.Desc.Kinds.Law.PlanK6Planes
import Johnson.Desc.Kinds.Law.DAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- **`K6LeftSeven.namedC`, at the head.** -/
theorem namedC_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    OffPad.namedAtC (dAt h).arr (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      ((P5J.At.X Zp).hS.NHf + 2) = true :=
  P5J.namedText_at_head h

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.namedC_at_head

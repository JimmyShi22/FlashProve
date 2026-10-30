-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6CallsAtHeadAll.lean: the condition `callsC` of `K6LeftSeven`
(Johnson/Desc/Kinds/Law/K6LeftSeven.lean), to the letter, at the head: no premise beside the head.
Two theorems, each a call: the names' tie at the head's segment (`names_tie_head_all`,
Johnson/Desc/AtSeats/NamesTieHeadStream.lean) pays the one premise of `callsC_at_head`
(Johnson/HB/LLHARD/K6CallsAtHead.lean) through Johnson/HB/LLHARD/K6CallsOfTie.lean.

Row or tool. A payer for a premise of another law.

Ground. It has not been through Lean.
(Where this and lean/THEOREM.md differ, the page holds.)

Limits. Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6CallsAtHead
import Johnson.HB.LLHARD.K6CallsOfTie
import Johnson.Desc.AtSeats.NamesTieHeadStream

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- The names' tie at segment 24, at the head. -/
theorem namesTie24_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    P5J.NamesTie24 Zp :=
  P5J.namesTie24_of_head h fun _ hμ =>
    VerifiableInference.Desc.K1.HeadNames.names_tie_head_all h.scope h.reads h.laid.pub hμ

/-- **`K6LeftSeven.callsC`, at the head.** -/
theorem callsC_at_head_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true :=
  callsC_at_head h (P5J.callNames_of_tie h (namesTie24_at_head h))

end

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesTie24_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.callsC_at_head_all

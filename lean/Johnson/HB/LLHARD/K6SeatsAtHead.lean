-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6SeatsAtHead.lean: the condition `seatsC` of `K6LeftSeven`
(Johnson/Desc/Kinds/Law/K6LeftSeven.lean), to the letter, at the head, under two named premises. One
theorem: a call of `seatsK6C_in_scope` (Johnson/Goal/Meaning/K6SeatsScope.lean).

Row or tool. A payer for a premise of another law.

Who pays that law's premises. Scope, the files read, the public part, the public data: the head's
fields. That the test which holds the made plan to the written one has accepted: `pins_of_laid`
(Johnson/Goal/Skeleton/PinsOfLaid.lean). That the value is laid: `laidPOf_of`. The numbers' list of
what is sent at (24, 0): by definition. The two numbers 179 and 183, the listed seats' term and the
term of the data on what is sent: Johnson/HB/LLHARD/K6SeatsTies.lean.

The two premises that are left. `hLp`: `At.laid? Zp = some Lp`: the letter Lp is the listed seats;
the head with the facts on every reached state holds this as its field `listed`. `hA`: the first
entry of the built segment 24's list of arrays is (24, "U3"): the law's owners name a payer in scope
(`reads_room_in_scope`), which is not imported here.

Ground. It has not been through Lean.
(Where this and lean/THEOREM.md differ, the page holds.)

Limits. Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6SeatsTies
import Johnson.Goal.Meaning.K6SeatsScope
import Johnson.Desc.Kinds.Law.DAtConst
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- **`K6LeftSeven.seatsC`, at the head.** -/
theorem seatsC_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Lp : K12.Door.Laid)
    (hLp : P5J.At.laid? Zp = some Lp)
    (hA : ((dAt h).sent.arrayOf.getD 24 #[])[0]? = some (24, "U3")) :
    AtFold.seatsK6C (dAt h).arr (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.num Zp 24 0) 0 (dAt h).cs (dAt h).shape (dAt h).pubD.dS Lp
      (K12.Door.msgsOfChain Zp.made.proof.1) ((dAt h).sent.arrayOf.getD 24 #[])
      ((dAt h).N.msgsAt (First.flatPlacesOf Sound.linksFull true)[341]?) = true := by
  rw [P5J.dS_text h]
  exact AtFold.seatsK6C_in_scope h.scope h.reads h.laid.pub (P5J.pins_of_laid h.scope h.laid).1
    (LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks) h.pubOne
    (P5J.At.N Zp cF) rfl _ _ (P5J.base_24_at_name h.scope h.laid) _
    (P5J.msgs_341_at_name h.scope h.laid) Lp ((P5J.laid_text Zp).symm.trans hLp) _ hA

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.seatsC_at_head

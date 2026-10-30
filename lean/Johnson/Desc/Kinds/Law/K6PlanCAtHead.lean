-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PlanCAtHead.lean: ONE MORE FIELD OF K6LeftMg
(Johnson/Desc/Kinds/Law/K6DueSplit.lean): planC: THE TYPED TEST ON THE PLAN OffPad.planK6C ACCEPTS
AT THE COMPOSED MEANING's CLOSED TERMS, UNDER THE ONE HEAD OF A COUNTED STATEMENT (P5J.AtMg | AtMgA)
AND ONE TEST OF THE DOOR's (madePinnedAt). STATED AND PROVED: TWO CALLS: no new mathematics.
  planC_at_mg · **planC_at_head**: by OffPad.planK6C_atAll (Law/PlanK6AtAll.lean: the typed test at
    these terms is the cheap public test planK6AtZ Zp) and tests_of_pin (Law/HeadCutsOfPin.lean:
    under the head and the one test the cheap test accepts). General in the second hash function o.
Limits. hy stays a premise here: other files have it off the head's own field laid.asks; that
theorem is not called. The full size alone. A member of the head is proved at storedPublicFiles and zGap alone
(at secondHashFunction; side library AtFullSide/Top/). Nothing on soundness or on hiding.

-/
import Johnson.Desc.Kinds.Law.PlanK6AtAll
import Johnson.Desc.Kinds.Law.HeadCutsOfPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madePinnedAt)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The field planC, at AtMg. -/
theorem planC_at_mg (h : P5J.AtMg o Z D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    OffPad.planK6C (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
      (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0 = true :=
  OffPad.planK6C_atAll Zp cF Z.lay (tests_of_pin h hy).1

/-- **The field planC, at the head.** -/
theorem planC_at_head (h : P5J.AtMgA o Z D r Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    OffPad.planK6C (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
      (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0 = true :=
  planC_at_mg h.toAtMg hy

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.planC_at_mg
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planC_at_head

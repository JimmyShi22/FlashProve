-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/K11R/LeavesField.lean: THE TIE OF `P5J.leaves_field` (Johnson/K11R/LeavesPaid.lean) TO THE
FROZEN K11Cond's FIELD "leaves" (Johnson/K11R/LawAtMg.lean), MADE BY LEAN: the
theorem is laid INTO the structure's field: its type is the field's, or this file does not compile.

Statements and proofs.
Main names:
  **K11Cond.leaves_paid**: whatever fourteen conditions K gives at the first chain's frame and at
    Rch := h.toAtMg.rch: the same thirteen others with "leaves" laid anew from the head alone.
What it is for: whoever makes a K11Cond at that frame and that "reached" lays
`leaves := P5J.leaves_field h`.
Limits. LeavesPaid.lean's. It makes no K11Cond: thirteen fields stay. No soundness follows. It holds
no coding theory.

-/
import Johnson.K11R.LawAtMg
import Johnson.K11R.LeavesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K11

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **"leaves" LAID INTO THE FROZEN STRUCTURE FROM THE HEAD ALONE.** -/
theorem K11Cond.leaves_paid {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x} {Bs : ProofFile.PureBase}
    {xM xI : Mem} {posI : ℕ → Bool × ℕ × ℕ} {ni R : ℕ} {Wa : S → Prop}
    (K : K11Cond
      (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h Bs h.toAtMg.rch xM xI posI ni R Wa) :
    K11Cond
      (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h Bs h.toAtMg.rch xM xI posI ni R Wa :=
  { K with leaves := P5J.leaves_field h }

end K11

#print axioms K11.K11Cond.leaves_paid

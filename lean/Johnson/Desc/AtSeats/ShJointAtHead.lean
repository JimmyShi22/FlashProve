-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ShJointAtHead.lean: hJ : Sh.Joint A O
(Johnson/Desc/K14/Law/SharedConstJoint.lean) AT THE TWO TABLES' CLOSED LETTERS, FROM THE
ONE HEAD h : P5J.AtMgA … ALONE. Two theorems: calls.

  Sh.eCodes_at     At.cs Zp = A.Q.codes, off the head's fields laid.pub and laid.planOk: by
                   Sh.hcs_of_read (Johnson/Desc/AtSeats/ShCodesOfRead.lean:
                   three calls of Johnson/P2R0R/SizedIsRead.lean: no pin, no scope).
  Sh.joint_atHead  **Sh.Joint (planAt Zp Np (seatF …)) (Sh.openAll h (Sh.eCodes_at h))**:
                   Sh.joint_atAll (ShJointAtAll.lean) with e := eCodes_at h · hlin :=
                   Sh.hlin_of_read … · hW := Sh.hW_atAll
                   (Johnson/Desc/AtSeats/ShHWAtAll.lean). NO PREMISE BUT THE HEAD.
What is not claimed. That the head can be met at the release's own files (its own file's mark: not
shown in Lean). So: no member. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.ShHWAtAll
import Johnson.Desc.AtSeats.ShCodesOfRead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Desc.K14.Law.Sh
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain First.S)
open P5J (AtMgA)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The two tables' codes are one, off the head. -/
theorem eCodes_at (h : AtMgA o Z D r Zp Np cF x) :
    P5J.At.cs Zp = (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)).Q.codes :=
  hcs_of_read h.laid.pub Np (secondAt Zp Np) cF h.laid.planOk
    (seatF o Zp Np (secondAt Zp Np) cF)

/-- **Sh.Joint at the shared and the first table's closed letters, from the head alone.** -/
theorem joint_atHead (h : AtMgA o Z D r Zp Np cF x) :
    Joint (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h)) :=
  joint_atAll3 h (eCodes_at h)
    (hlin_of_read h.laid.pub Np (secondAt Zp Np) cF h.laid.planOk
      (seatF o Zp Np (secondAt Zp Np) cF))

end Desc.K14.Law.Sh

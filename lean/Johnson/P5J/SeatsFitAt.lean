-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/SeatsFitAt.lean: UNDER THE NAMED CONDITIONS (PlanOk) EVERY MEMBER OF THE CONSTANT's ms HAS A SEAT THAT FITS. Two theorems.
  At.PlanOk.seatsFit: ∀ y ∈ At.ms Zp lay, SeatFits (F0T o Zp Np cF) (At.cs Zp) y.1.l y.1.seat: from PlanOk's field "fit" (P5T.seatsFitP (F0T o Zp Np cF) cs pseats: over the plan's seats): seatsFitB_R carries it to the members' lists by the make; seatsFit_of_B gives SeatsFit at msOf of these; At.ms IS that (ms_is := rfl).
  At.seatsFit_of_P: the same from the bare condition, at any description F.
Limits. It shows the condition at no list of rounds (evaluated true at two named points of the scope: runs, no theorem). The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.PlanOk
import Johnson.Desc.Sound.PlanMemProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.Sound (SeatFits)

/-- From the bare condition, at any description. -/
theorem seatsFit_of_P {Xi : Type} (F : FileDescription Xi) (Zp : ProofFile.Pub) (lay : ByteArray)
    (h : P5T.seatsFitP F (cs Zp) (pseats Zp) = true) :
    ∀ y ∈ ms Zp lay, SeatFits F (cs Zp) y.1.l y.1.seat :=
  VerifiableInference.Desc.Sound.seatsFit_of_B F (cs Zp) (members Zp lay)
    ((P5T.seatsFitB_R _ _ _ _ _ (fun p hp _ => P5T.planSeats_send_lt Zp Zp.D.1 p hp)).trans h)

/-- **Every member's seat fits, under the named conditions.** -/
theorem PlanOk.seatsFit {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {lay : ByteArray} (ok : PlanOk o Zp Np cF lay) :
    ∀ y ∈ ms Zp lay, SeatFits (F0T o Zp Np cF) (cs Zp) y.1.l y.1.seat :=
  seatsFit_of_P _ Zp lay ok.fit

end P5J.At

#print axioms P5J.At.seatsFit_of_P
#print axioms P5J.At.PlanOk.seatsFit

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ShHWAtAll.lean: THE PREMISE hW OF Sh.joint_atAll
(ShJointAtAll.lean), PAID: at whatever the shared table's open letters' R holds of,
"K13.pileWithin"'s own test accepts. So Sh.Joint at the two tables' closed letters stands on three
premises: h, e, hlin.

  Sh.hW_atAll      from the one head h alone. R p has in it
                   EndAt₁ (seatF o Zp Np (secondAt Zp Np) cF) p: the wrapped sub-protocols' reach at
                   the first chain's length. within_paid_below
                   (Johnson/Desc/AtSeats/ReachBelow.lean) gives the test at every such state of SOME
                   Z A B c with F = fileDescBy … c, from onlineDescription's return and F.planOk = true: both
                   are fields of h.laid, at F0T o Zp Np cF, which is seatF … by unfolding
                   (Sh.f0T_is). THE ∃'s LETTERS ARE THE SEAT's: Z by the public part's one value
                   (h.laid.pub); c by Sh.first_inj
                   (Johnson/Desc/K14/Law/SharedConstReachAt.lean: two spellings of one IOP by
                   fileDescBy have one first chain). The fence "failed = none" and R's second
                   conjunct are not spent.
  Sh.joint_atAll3  Sh.joint_atAll at it.

What is not claimed. That AtMgA can be met at the release's own files. e, hlin. Nothing on
soundness.

-/
import Johnson.Desc.AtSeats.ShJointAtAll
import Johnson.Desc.K14.Law.SharedConstReachAt
import Johnson.Desc.AtSeats.ReachBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain First.S)
open P5J (AtMgA)

namespace Sh

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **hW, from the one head.** -/
theorem hW_atAll (h : AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF o Zp
    Np (secondAt Zp Np) cF)).Q.codes) :
    ∀ p, (openAll h e).R p → ((openAll h e).get p).2.failed = none →
      VerifiableInference.Desc.K13.pileWithinC ((openAll h e).get p).2 = true := by
  intro p hR _
  obtain ⟨Z', A, B, c, hZ, eF, K⟩ := Meaning.K2.within_paid_below h.laid.value h.laid.planOk
  obtain rfl : Z' = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  obtain rfl : cF = c := first_inj (show seatF o Z' Np (secondAt Z' Np) cF = _ from eF)
  exact (K _ p hR.1).1

/-- **Sh.Joint at the shared and the first table's closed letters, on three premises.** -/
theorem joint_atAll3 (h : AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF o Zp
    Np (secondAt Zp Np) cF)).Q.codes)
    (hlin : (VerifiableInference.Desc.K13.whereOf Zp).lin = (planAt Zp Np (seatF o Zp Np (secondAt
        Zp Np) cF)).Q.par.S) :
    Joint (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h e) :=
  joint_atAll h e hlin (hW_atAll h e)

end Sh

end Desc.K14.Law

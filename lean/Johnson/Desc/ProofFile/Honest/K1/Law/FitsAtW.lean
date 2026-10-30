-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FitsAtW.lean: THE SHARED "SENDING" (the kind K1): THREE PUBLIC
TESTS OF THE RECORD OF PREMISES K1Seated (Honest/K1/Seated.lean), fits, oneAns AND port, HOLD AT THE
PLAN OF W's SENDING, UNDER THE LIBRARY's HEAD. The like of Honest/K1/Law/FitsWritten.lean, whose 51
plans lack this one. Eight theorems; no definition.

The road. The first two are Bools on public numbers: they are evaluated IN THE KERNEL at the
library's written plan K1.parWF (Johnson/Desc/K1/Law/TiesWritten.lean), and the library's own ties
say that under its head the plan at the description's public part is the written one.

  - oneAns_w_written, fits_w_written: two closed sentences, by evaluation in the kernel: at
    K1.parWF; fits with the ride rideOf (wFold K1.qFull.lin) (Honest/K1/PlaceW.lean).
  - fits_w_wrong_fails: the same test at the same plan says NO where the same table rides at the
    wrong message, number 0, W itself: so it can fail, and the ride is read. (Where NO table rides
    the test asks less, not more: it does not ask that a fold's mask message have a ride: that is
    rideOwn's side, Honest/K1/PlaceJob.lean.)
  - msg_w_head: UNDER h, O: the message that the shape gives is the written one (W_hm_atAll,
    Johnson/Desc/K1/Law/TiesAtAll.lean).
  - parW_written: UNDER h, O: K1.parW Zp.first (wGp Zp) 4 wMsgFull = K1.parWF (eW_atAll, the same
    file).
  - oneAns_w_head, fits_w_head: UNDER h (the library's head: A HYPOTHESIS) and O (the description
    opened: out of h.laid.opened): the two tests at that plan, fits at the ride rideOf (wFold
    Zp.first.lin) (likeFull_in_scope's field lin).
  - port_w_head: UNDER h, O: the library's condition on the plan and the radii (condPort) at the
    radii radRec 81 of that plan: W_hCond_atAll (Johnson/Desc/K1/Law/TiesAtAll2.lean), restated at
    wGp.

Limits. THE FULL SIZE ALONE: the written plan stands at K1.qFull. "AT MOST one answer", at this
plan, under the head: no more is said. That a prover's job has this plan and ride is wJobAt's text
(Honest/K1/PlaceW.lean), not said here. Nothing on data. Nothing on soundness or on any other
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt
import Johnson.Desc.ProofFile.Honest.K1.PlaceW
import Johnson.Desc.K1.Law.TiesAtAll2
import Johnson.Desc.K1.Law.PinsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

/-- At most one answer at each message of W's sending's written plan. -/
theorem oneAns_w_written : answersAtMostOne K1.parWF = true := by decide +kernel

/-- W's sending's written plan fits, with the ride that the shape's own terms make. -/
theorem fits_w_written : sendFits K1.parWF (rideOf (wFold K1.qFull.lin)) = true := by
  decide +kernel

/-- Where the same table rides at message number 0, W itself, the test says no at that plan. -/
theorem fits_w_wrong_fails :
    sendFits K1.parWF (rideOf ((wFold K1.qFull.lin).map fun x => (0, x.2))) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- Under the head the message that the shape gives is the written one. -/
theorem msg_w_head : OnBytes.linMessageW Zp.first.lin = some wMsgFull :=
  K1.W_hm_atAll h O (K1.pin1_atAll h)

/-- Under the head the plan of W's sending is the written one. -/
theorem parW_written : K1.parW Zp.first (wGp Zp) 4 wMsgFull = K1.parWF :=
  K1.eW_atAll h O (K1.pin1_atAll h)

/-- **oneAns AT NUMBER 356's PLAN**, under the head. -/
theorem oneAns_w_head : answersAtMostOne (K1.parW Zp.first (wGp Zp) 4 wMsgFull) = true := by
  rw [parW_written h O]
  exact oneAns_w_written

/-- **fits AT NUMBER 356's PLAN AND RIDE**, under the head. -/
theorem fits_w_head :
    sendFits (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin)) = true := by
  rw [parW_written h O,
    (K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
  exact fits_w_written

/-- **port AT NUMBER 356's PLAN**, under the head, at the library's radii. -/
theorem port_w_head : K1.condPort (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
    (K1.radRec 81 (K1.parW Zp.first (wGp Zp) 4 wMsgFull)) = true :=
  K1.W_hCond_atAll h O (K1.pin1_atAll h)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.oneAns_w_written
#print axioms ProofFile.Honest.K1.fits_w_written
#print axioms ProofFile.Honest.K1.fits_w_wrong_fails
#print axioms ProofFile.Honest.K1.msg_w_head
#print axioms ProofFile.Honest.K1.parW_written
#print axioms ProofFile.Honest.K1.oneAns_w_head
#print axioms ProofFile.Honest.K1.fits_w_head
#print axioms ProofFile.Honest.K1.port_w_head

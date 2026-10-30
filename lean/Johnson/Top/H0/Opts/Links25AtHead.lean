-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/Links25AtHead.lean: UNDER THE ONE HEAD, WITHOUT A PIN: THE SHAPE THAT THE FIRST
STATE's FRAME HOLDS HAS 25 LINKS. Two statements with one proof. A law file; no running text imports
it.
  links25_at      h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF ⊢
                  Zp.s₀.check.frame.shape.link.length = 25
  links25_atAll   the same under P5J.AtMgA, which extends AtMg
BY CALLS ALONE. In scope a member of the code switching's lot stands at link 1 (IM.k2_link_sits,
IMR/FirstSeats.lean); the description's test on the list of rounds makes it live; a live member
is made of an answer Q of prepOf (P1K2.live_answers, Opts/SpotsAnswer.lean: its proof's own
first lines at m := 0 are repeated here to reach the member). Where prepOf answers, Q.z.request is
the first state's frame's shape (prepOf_request) and Q.z is the planner's own sizes (prepOf_z:
Tw/K2C/GroupAtNums.lean); and in scope, where ProofFile.pubPlain returns Zp, the planner's request has 25
links (pub_links, Opts/PlannerRequestHas25Links.lean: no pin is asked). OUT OF THE HEAD: scope · reads ·
laid.opened · laid.planOk · laid.pub.
WHOM IT PAYS (by report): the second premise of stands23 | stands24
(K2Caller/StandsLow.lean · Stands24.lean) and the field links25 of the frame's condition.
Limits. AtMg is shown at nothing here: NO MEMBER. At OnBytes.secondHashFunction alone. The full size alone.
Nothing on soundness.
-/
import Johnson.Top.H0.Opts.SpotsAnswer
import Johnson.Top.H0.Opts.PlannerRequestHas25Links
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2

open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2Caller (pub_links)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **25 links, under the head AtMg, without a pin.** -/
theorem links25_at (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    Zp.s₀.check.frame.shape.link.length = 25 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, hx, hl, hi⟩ :=
    IM.k2_link_sits h.scope h.reads O 1 (by omega) (by omega)
  have hb := flat_planOk O h.laid.planOk b (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
  have hxp : y.planOk = true := (IM.retype_planOk y (IM.laid_planOk hl.framed.laid hb)).1
  obtain ⟨Q, n, hQ, -, -⟩ := live_answers O.blank hx hxp
  rw [← (prepOf_request hQ).1, prepOf_z hQ]
  exact pub_links h.scope h.laid.pub

/-- **The same under AtMgA.** -/
theorem links25_atAll (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    Zp.s₀.check.frame.shape.link.length = 25 :=
  links25_at h.toAtMg

end P1K2

#print axioms P1K2.links25_at
#print axioms P1K2.links25_atAll

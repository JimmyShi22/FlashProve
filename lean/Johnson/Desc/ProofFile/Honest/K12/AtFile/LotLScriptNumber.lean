-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLScriptNumber.lean

It states no goal. No property of the protocol is claimed.

The number that the code switch's share
gives a place's message 0 (`switchNum`, K2/SwitchNums.lean) is the plan's numbering (`P5J.At.arr`) at
the seat that `switchSeatIn` finds for it. One statement with its proof: by unfolding.

Hypothesis. hq: the plan's list has a seat for the message. Limits. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.SwitchNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open ProofFile.Honest.K2 (SwitchPlace switchSeatIn switchNum switchNumIn)

/-- **The number of the switch's message 0 is the plan's numbering at its seat.** -/
theorem carrying_number_at_seat (Zp : ProofFile.Pub) (p : SwitchPlace) {q : P5T.PSeat}
    (hq : switchSeatIn (P5J.At.pseatsAll Zp) p.link 0 = some q) :
    switchNum Zp p 0 = P5J.At.arr Zp q.j q.t := by
  unfold switchNum switchNumIn
  rw [hq]
  rfl

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.carrying_number_at_seat

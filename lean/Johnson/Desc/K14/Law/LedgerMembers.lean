-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerMembers.lean: the proofs of the three statements of
Johnson/Desc/K14/Law/LedgerMembersOwed.lean on the letter mem of the shared chain's blocks' laws, as
it is filled there (`memK`). Three theorems.
  memAt     `MemAtOwed`: where o_u's sending has a message, memK gives the three members at the
            three numbers 0, sU, sU + 1: by the three tests of memK's text.
  memNo     `MemNoOwed`: oNoSh gives each of the three members its number: by unfolding.
  memSits   `MemSitsOwed`: who sits at a message's tenant has that message's number: it is that
            message's member (`uniq_sh`, Johnson/Desc/Sound/SeamNumbersSh.lean, CALLED), then memNo.
What is not claimed. That sU is the number of messages of o_u's sending at any plan. Nothing on
soundness.

-/
import Johnson.Desc.K14.Law.LedgerMembersOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence

/-- **At the three numbers.** -/
theorem memAt : MemAtOwed := by
  intro S rU rO rSp lo layU layO sU hs m
  cases m with
  | oU => exact if_pos rfl
  | oOmega => exact (if_neg (Nat.pos_iff_ne_zero.1 hs)).trans (if_pos rfl)
  | oSp =>
    exact (if_neg (Nat.succ_ne_zero sU)).trans
      ((if_neg (Nat.succ_ne_self sU)).trans (if_pos rfl))

/-- **Each of the three has its number.** -/
theorem memNo : MemNoOwed := by
  intro S rU rO rSp lo layU layO sU m
  cases m <;> rfl

/-- **Who sits at a message's tenant has that message's number.** -/
theorem memSits : MemSitsOwed := by
  intro S rU rO rSp lo layU layO codes sentU sentO hlU hlO hU hO sU m z hz hs
  rw [uniq_sh S rU rO rSp lo layU layO codes sentU sentO hlU hlO hU hO m z hz hs]
  exact memNo S rU rO rSp lo layU layO sU m

end Desc.K14.Law

#print axioms Desc.K14.Law.memAt
#print axioms Desc.K14.Law.memNo
#print axioms Desc.K14.Law.memSits

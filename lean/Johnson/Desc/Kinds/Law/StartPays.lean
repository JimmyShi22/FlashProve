-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/StartPays.lean: the test on the request that the law on the output head's
own rounds asks follows from the test on the request under which the first chain's first record is
made.

What the file holds.
  requestOf_req      what the head's seat reads of the request hangs on the record's field req
                     alone.
  okStart_of_reqOk   where S.reqOk (2 ^ h.lt) h.V says yes at a record, the kind's test on the
                     request (Par.okStart) says yes at the request that the seat reads off it.
  start_pays         the same at a later record s, if its field req is still that of the record s0
                     at which S.reqOk said yes.
Why. The law's premise on the record in front has a clause: the kind's test on the request passes at
the request that the seat reads. By a search of texts in another version, no block of the
description runs that test; this file does not lean on that. What runs is S.reqOk
(Johnson/Desc/First/State.lean), where the first record is made: T + 2 words; every token below V;
r < e ≤ T. The two tests say the same of the same words, once T is 2 ^ lt and V is the head's.

What it does not give. Nothing on soundness. That a given description makes its first record under
S.reqOk at these two numbers is to be seen at that description's text: here it is a premise. That
the blocks between the first record and the head's own rounds leave the field req is a premise too.

-/
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.StartPays

open VerifiableInference.Desc.First (S)
open OnBytes.Model.Head (Shape)

/-- What the seat reads of the request hangs on the field req alone. -/
theorem requestOf_req {s s0 : S} (h : s.req = s0.req) : requestOf s = requestOf s0 := by
  unfold requestOf S.tokv S.rowR S.rowE S.reqT
  rw [h]

/-- **The first record's test on the request gives the kind's.** -/
theorem okStart_of_reqOk (h : Shape) (w : Nat) (s : S) (hq : s.reqOk (2 ^ h.lt) h.V = true) :
    (parOf h w).okStart (requestOf s) = true := by
  unfold S.reqOk at hq
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not, Array.all_eq_true, decide_eq_true_eq, Nat.not_le, ge_iff_le] at hq
  obtain ⟨⟨hsz, htok⟩, hr, he⟩ := hq
  have hT : s.reqT = 2 ^ h.lt := by unfold S.reqT; omega
  have hts : s.tokv.size = 2 ^ h.lt := by
    unfold S.tokv
    rw [Array.size_map, Array.size_extract, hT]
    omega
  show (Decidable.decide (s.rowR < s.rowE) && Decidable.decide (s.rowE ≤ 2 ^ h.lt) &&
    (List.range (2 ^ h.lt)).all fun t => Decidable.decide (s.tokv.getD t 0 < h.V)) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨hr, Nat.le_of_not_lt he⟩, fun t ht => ?_⟩
  have ht' : t < s.tokv.size := by rw [hts]; exact ht
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht', Option.getD_some]
  exact htok t ht'

/-- **The same at a later record whose field req is as it was.** -/
theorem start_pays (h : Shape) (w iU3 : Nat) (s0 s : S) (hq : s0.reqOk (2 ^ h.lt) h.V = true)
    (hr : s.req = s0.req) : (parOf h w).okStart ((seatAt h iU3).request s) = true := by
  show (parOf h w).okStart (requestOf s) = true
  rw [requestOf_req hr]
  exact okStart_of_reqOk h w s0 hq

end VerifiableInference.Desc.Kinds.Head.Law.StartPays

#print axioms VerifiableInference.Desc.Kinds.Head.Law.StartPays.okStart_of_reqOk
#print axioms VerifiableInference.Desc.Kinds.Head.Law.StartPays.start_pays

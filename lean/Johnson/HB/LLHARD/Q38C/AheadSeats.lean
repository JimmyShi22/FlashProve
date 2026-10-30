-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38C/AheadSeats.lean: a test with code on public values: THE SEAT EQUATION FOR
EVERY ORACLE MESSAGE OF A SEGMENT THAT IS STILL AHEAD. A definition and two statements with their
proofs.

Why. Behind the approximate range proof's draw the digits' array is not yet sent. What the list of
rounds says of it (`K9.aheadIn`, Johnson/Desc/First/Batch/Ahead.lean) holds a seat, read off the
numbers' field "sent"; the law on the digits speaks of the seat that the lookups' letters give. That
the two are one is asked here of EVERY message that is ahead, not of the one in which the digits'
array lies: so the test does not read the built segments' lists of arrays, which no entry test
compares with a written value.

  `aheadSeatsB shape sent own seat l n₀`: the test. It follows `K9.aheadOf`'s rule for the seat
    clause by clause: the moment is not 0; the place among the messages of that moment; and
    `K9.aheadIn`'s "the seat may be read".
  `c_aheadSeats_at`: what a yes gives at one message from n₀ on.
  `aheadSeatsB_no_link`: a negative test, general: it rejects where the shape has no segment l. No
    theorem calls it.

Can it accept for want of members? Where n₀ is the segment's number of messages or more, it asks
nothing of any message: whoever spends a yes says how many messages are ahead (`aheadSeats_walks`,
Johnson/HB/LLHARD/Q38C/AheadSeatsWritten.lean).

WHICH ROWS OF THE HEAD IT SPENDS, BY THE CODE: none: it reads no field of the head.

Limits. Nothing on soundness.
-/
import Johnson.Desc.First.Batch.Ahead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes

/-- **The seat equation for every oracle message of segment l that is still ahead**, whichever array
lies in it. shape: a request's shape. sent: by moment, the seats of the segment's sendings. own:
the seats that may be read. seat: a message's seat, by its number in the segment. n₀: as many
messages of the segment are sent already.

It accepts where the shape has segment l and each message j from n₀ on is of a moment other than 0,
the seat that stands for it in its moment's sending (as many places in as messages of that moment
stand in front of it) is `seat j`, and that seat may be read. -/
def aheadSeatsB (shape : Params.ReqShape) (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))
    (seat : Nat → Nat × Nat) (l n₀ : Nat) : Bool :=
  (shape.link[l]?).any fun sh => (List.range sh.messages.length).all fun j =>
    decide (j < n₀) || (sh.messages[j]?).any fun M =>
      M.moment != 0 &&
        (sent M.moment)[((sh.messages.take j).filter (·.moment == M.moment)).length]? ==
          some (seat j) &&
        own.contains (seat j)

/-- What a yes gives at one message. -/
theorem c_aheadSeats_at {shape : Params.ReqShape} {sent : Nat → List (Nat × Nat)}
    {own : List (Nat × Nat)} {seat : Nat → Nat × Nat} {l n₀ : Nat}
    (h : aheadSeatsB shape sent own seat l n₀ = true)
    {sh : Params.ReqLink} (hs : shape.link[l]? = some sh) {j : Nat} {M : Params.ReqMessage}
    (hM : sh.messages[j]? = some M) (hj : n₀ ≤ j) :
    M.moment ≠ 0 ∧
      (sent M.moment)[((sh.messages.take j).filter (·.moment == M.moment)).length]? =
        some (seat j) ∧
      seat j ∈ own := by
  unfold aheadSeatsB at h
  rw [hs, Option.any_some, List.all_eq_true] at h
  have hlt : j < sh.messages.length := (List.getElem?_eq_some_iff.1 hM).1
  have h1 := h j (List.mem_range.2 hlt)
  rw [decide_eq_false (by omega), Bool.false_or, hM, Option.any_some] at h1
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h1
  exact ⟨h1.1.1, h1.1.2, List.contains_iff_mem.1 h1.2⟩

/-- The test rejects where the shape has no such segment. -/
theorem aheadSeatsB_no_link (shape : Params.ReqShape) (sent : Nat → List (Nat × Nat))
    (own : List (Nat × Nat)) (seat : Nat → Nat × Nat) (l n₀ : Nat) (h : shape.link[l]? = none) :
    aheadSeatsB shape sent own seat l n₀ = false := by
  unfold aheadSeatsB
  rw [h]
  rfl

end Q38

#print axioms Q38.c_aheadSeats_at
#print axioms Q38.aheadSeatsB_no_link

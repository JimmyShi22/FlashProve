-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/HandsOnBools.lean: **THE PROXIMITY TEST's ACCEPTING STEP HANDS FOUR FACTS ON
THE VERIFIER's STATE ON, AS BOOLS.** Statements and proofs.
What stands here is the kind's own step
for whoever walks the fold.
  `book_on` | `seats_on` | `shapes_on`: `hands_on`'s three clauses (HandsOnAtK12.lean) in the Bools'
    form: `atFirstBook ft` at ft := the place's own first tree's number; `atFirstSeats L` under the
    test with code `goesOnB` on the plan's lists at the state's two counts; `atFirstShapes M` where
    M goes on with the shapes of the notices of the test's sendings (by the rule `msgShapes_ride`,
    Johnson/Desc/K12/Door/MsgShapesRide.lean).
  `fits_on`: "K12.bookFits": `atFirstFits` goes on with no premise on the
    plan's lists: by the walk of the kind's block `k12_bookFits` (BookFitsThrough.lean).
Limits. First arm, but for `fits_on`, which has no premise on the own mask; its door is
`enterFinish`, so the last chain's own seat is not covered. The two "go on" are premises on the
plan. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.HandsOnAtK12
import Johnson.Desc.K12.Door.DoorIs
import Johnson.Desc.K12.Coin.BookFitsFields
import Johnson.Desc.Sound.BookTestsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open H2K.JointK

section
variable (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true) (ho : π.nums.ownMask = false)
  (he : π.early = true) (ha : π.answers = 1) (ft : ℕ)
  (leave : First.S → T12 → Except String First.S) (hl : LaysBack leave) (s s' : First.S)
  (hY : StepYes ft (proximityTestKind guardedProximityTestParts π : Blk') enterFinish leave s s')
include hp ho he ha hl hY

theorem book_on (h : Door.atFirstBook π.nums.firstTree s = true) :
    Door.atFirstBook π.nums.firstTree s' = true :=
  (bookStep_iff _ _ _).2
    ((hands_on π hp ho he ha ft leave hl s s' hY).1 ((bookStep_iff _ _ _).1 h))

theorem seats_on (L : Door.Laid) (h : Door.atFirstSeats L s = true)
    (hgo : ∀ first rest, π.nums.stages = first :: rest →
      goesOnB (Door.toTree L) s.st.codes s.book.place.size s.book.trees.size
        (sendsFrom π 0 rest) = true) :
    Door.atFirstSeats L s' = true :=
  (seatsPrefix_iff _ _).2
    ((hands_on π hp ho he ha ft leave hl s s' hY).2.1 (Door.toTree L) ((seatsPrefix_iff _ _).1 h)
      fun first rest A hs hA => goesOn_of_B (hgo first rest hs) A hA)

theorem shapes_on (M : List OracleShape) (h : Door.atFirstShapes M s = true)
    (hgo : ∀ first rest, π.nums.stages = first :: rest →
      (M.drop s.st.oracles.size).take (noticesOf (sendsFrom π 0 rest)).length =
        noticesOf (sendsFrom π 0 rest)) :
    Door.atFirstShapes M s' = true := by
  obtain ⟨first, rest, hs, e⟩ := (hands_on π hp ho he ha ft leave hl s s' hY).2.2
  exact Door.msgShapes_ride h e (hgo first rest hs)

omit hp ho in
/-- "K12.bookFits": by the kind's own walk (`k12_bookFits`, BookFitsThrough.lean). Both arms. -/
theorem fits_on (h : Door.atFirstFits s = true) : Door.atFirstFits s' = true := by
  obtain ⟨t, t', rs, cols, k, e1, e2, e3⟩ := hY
  obtain ⟨_, l2, _⟩ := hl s t' s' e3
  obtain ⟨o, _, _, _, rfl⟩ := Seat.enterFinish_ok s t e1
  obtain ⟨gs, hd⟩ := step_decide (proximityTestKind guardedProximityTestParts π : Blk') ft _ t' rs cols k e2
  refine (bookFitsB_iff _).2 ?_
  rw [l2]
  exact k12_bookFits π he ha _ t' _ gs hd ((bookFitsB_iff _).1 h)

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.book_on
#print axioms VerifiableInference.Desc.K12.Coin.seats_on
#print axioms VerifiableInference.Desc.K12.Coin.shapes_on
#print axioms VerifiableInference.Desc.K12.Coin.fits_on

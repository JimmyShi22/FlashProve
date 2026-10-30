-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/HandsOnAtK12.lean: **WHAT THE PROXIMITY TEST's YES HANDS ON OF THE PROMISE AT
THE FIRST CHAIN's FINISH**: the three items "K12.bookInOrder", "K12.seatsCarried", "K12.msgShapes",
from the state in front to the state behind, out of `StepYes` (SitsYes.lean) alone: so at the
file's own piece, behind whatever guards, wherever the way out lays the statement, the book and the
count of roots back. Statements and proofs.
  That a yes of the kind's decision keeps "the book is in order": `k12_bookStep`, BookThrough.lean.


  `LaysBack leave`: the way out lays the kind's state's statement, book and count of roots back.
  `hands_on`: **the three at once**: the plan's tests (the test on the plan; no mask of its own;
    early; one answer), `StepYes ft (proximityTestKind guardedProximityTestParts π) enterFinish leave s s'`, `LaysBack leave`: then
    (1) the book in order at s gives it at s'; (2) the seats carried at s give them at s', where the
    plan's lists go on with the test's sendings; (3) the shapes of s' are those of s and, behind
    them, the shapes of the notices of the test's sendings.
  `laysBack_finish`, `laysBack_bind`: the seat's own way out lays back; and so does it with a test
    bound behind that hands the state on as it is or refuses.
First arm. Limits. "The plan's lists go on" is a premise on the plan. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.SitsYes
import Johnson.Desc.K12.Coin.MaskOfYes
import Johnson.Desc.K12.Coin.BookThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.JointK H2K.Out
open VerifiableInference.Desc.K12.Door (shapesIn)

/-- The way out lays the kind's state's statement, book and count of roots back. -/
def LaysBack (leave : First.S → T12 → Except String First.S) : Prop :=
  ∀ s t' s', leave s t' = .ok s' → s'.st = t'.st ∧ s'.book = t'.book ∧ s'.roots = t'.roots

theorem laysBack_finish : LaysBack leaveFinish := by
  intro s t' s' h
  obtain rfl := (Seat.leaveFinish_ok s s' t').1 h
  exact ⟨rfl, rfl, rfl⟩

/-- With a test bound behind that hands the state on as it is, or refuses. -/
theorem laysBack_bind {leave : First.S → T12 → Except String First.S} (h : LaysBack leave)
    (g : First.S → First.S → Except String First.S) (hg : ∀ s m s', g s m = .ok s' → s' = m) :
    LaysBack fun s t => (leave s t).bind (g s) := by
  intro s t' s' hb
  obtain ⟨m, h1, h2⟩ := H2K.FoldLaw.bind_ok hb
  obtain rfl := hg s m s' h2
  exact h s t' _ h1

/-- **The three at once.** -/
theorem hands_on (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true)
    (ho : π.nums.ownMask = false) (he : π.early = true) (ha : π.answers = 1) (ft : ℕ)
    (leave : First.S → T12 → Except String First.S) (hl : LaysBack leave) (s s' : First.S)
    (hY : StepYes ft (proximityTestKind guardedProximityTestParts π : Blk') enterFinish leave s s') :
    (BookStep π.nums.firstTree s.book s.roots → BookStep π.nums.firstTree s'.book s'.roots) ∧
    (∀ L : Laid, SeatsPrefix L s.book →
      (∀ first rest A, π.nums.stages = first :: rest →
        laidFrom s.st.codes s.book.trees.size (sendsFrom π 0 rest) = some A →
        (L.places.drop s.book.place.size).take A.places.length = A.places ∧
        (L.shapes.drop s.book.trees.size).take A.shapes.length = A.shapes) →
      SeatsPrefix L s'.book) ∧
    ∃ first rest, π.nums.stages = first :: rest ∧
      shapesIn s'.st = shapesIn s.st ++ noticesOf (sendsFrom π 0 rest) := by
  obtain ⟨t, t', rs, cols, k, e1, e2, e3⟩ := hY
  obtain ⟨l1, l2, l3⟩ := hl s t' s' e3
  obtain ⟨o, _, _, _, rfl⟩ := Seat.enterFinish_ok s t e1
  have hm := mask_of_yes π hp ho _ t' ft k rs cols e2
  obtain ⟨gs, hd⟩ := step_decide (proximityTestKind guardedProximityTestParts π : Blk') ft _ t' rs cols k e2
  refine ⟨fun hb => ?_, fun L hS hgo => ?_, ?_⟩
  · rw [l2, l3]
    exact k12_bookStep π he ha _ t' _ gs hd hb
  · obtain ⟨first, rest, hs, hA⟩ := k12_appends π he ha _ t' _ gs hm hd
    rw [l2]
    exact seatsPrefix_appends L _ _ _ _ hS hA fun A hAA => hgo first rest A hs hAA
  · obtain ⟨first, rest, hs, hA⟩ := k12_shapes π he ha _ t' _ gs hm hd
    rw [l1]
    exact ⟨first, rest, hs, hA⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.laysBack_bind
#print axioms VerifiableInference.Desc.K12.Coin.hands_on
#print axioms VerifiableInference.Desc.K12.Coin.laysBack_finish

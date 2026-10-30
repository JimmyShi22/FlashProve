-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: A COUNT OF THE VERIFIER's CHALLENGES ALONE: no prover, no filling, no run and no coin is read.
E2E/Lookup/LookupMarksPassTheSharesTest.lean: the kind "lookup" (K3): THE LOOKUPS' HUNDRED MARKS PASS THE TEST THAT
E2E/TheFallsSum.lean ASKS OF EVERY RECORD (markSmall), and the price that E2E/TheFalls.lean writes for one event of a
lookup (lookupElement) is the number at which the marks pay (shareOfOneValue 36,
Honest/K3/Term/LookupMarksPayAtAWrittenNumber.lean).

  lookupNumeratorPassesTheTest   a numerator of at most 1591, over the field's size, passes shareSmall
  lookupMarksPassTheSharesTest   **every member of k3Marks passes markSmall**
  lookupElementIsTheShareOfOneValue   lookupElement = shareOfOneValue 36

The test is asked of each mark at the field's size, since each place of the list has the kind K3
(k3Marks_kind). Its numerator is one of the two numbers that lookupEventsAtSiteAtMost bounds by 1591. Neither needs the
library's head, so the theorem has no hypothesis. Under the head the list has 100 members (k3Marks_100), so there the
theorem speaks of all of them.

Limits. This is the lookups' part of sharesSmall alone: an inequality on public numbers. It does not say that a mark's
stated share bounds its event at any kit: the shares of k3Marks, read as chances, are not held at Run.ckP .two, and
the road there is the numerator times shareOfOneValue 36. The bound 1591 is at the largest sizes that the public test
on a shape allows.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import E2E.TheFallsSum
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupEventsInClosedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup
open ProofFile.Honest.K3.Good (k3Marks k3Marks_mem k3Marks_kind)
open ProofFile.Honest.K3.Term (lookupEventsAtSite lookupEventsAtSiteAtMost shareOfOneValue)
open AtPublicFiles.TheFalls (shareSmall markSmall lookupElement)

/-- **A numerator of at most 1591, over the field's size, passes the test on a share.** -/
theorem lookupNumeratorPassesTheTest {numerator : ℕ} (atMost : numerator ≤ 1591) :
    shareSmall ⟨numerator, AtPublicFiles.TheFalls.fieldSize⟩ = true := by
  have sizeOfTheField : AtPublicFiles.TheFalls.fieldSize = 18446744069414584321 ^ 3 := by
    unfold AtPublicFiles.TheFalls.fieldSize
    rw [OnBytes.Slice.two_p, Code.pGold_eq]
  unfold shareSmall
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  show 0 < AtPublicFiles.TheFalls.fieldSize ∧ numerator * 2 ^ 109 ≤ AtPublicFiles.TheFalls.fieldSize
  rw [sizeOfTheField]
  exact ⟨by norm_num, le_trans (Nat.mul_le_mul_right _ atMost) (by norm_num)⟩

/-- **EVERY MARK OF THE LOOKUPS PASSES THE TEST ON THE RECORDS.** No hypothesis. -/
theorem lookupMarksPassTheSharesTest (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    (k3Marks Zp G₀).all markSmall = true := by
  refine List.all_eq_true.2 fun mark isMember => ?_
  obtain ⟨site, isSite, isOneOfTheTwo⟩ := k3Marks_mem Zp G₀ mark isMember
  have bothMarks := lookupEventsAtSiteAtMost Zp site isSite
  unfold lookupEventsAtSite at bothMarks
  unfold markSmall
  rw [if_pos (Or.inl (k3Marks_kind Zp G₀ mark isMember))]
  refine lookupNumeratorPassesTheTest ?_
  rcases isOneOfTheTwo with rfl | rfl
  · exact le_trans (Nat.le_add_right _ _) bothMarks
  · exact le_trans (Nat.le_add_left _ _) bothMarks

/-- **The price of one event of a lookup is the number at which the marks pay.** -/
theorem lookupElementIsTheShareOfOneValue : lookupElement = shareOfOneValue 36 := rfl

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.lookupNumeratorPassesTheTest
#print axioms AtPublicFiles.Lookup.lookupMarksPassTheSharesTest
#print axioms AtPublicFiles.Lookup.lookupElementIsTheShareOfOneValue

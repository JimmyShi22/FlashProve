-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookFreeOf.lean: WHERE EVERY STRETCH OF A LIST LIES WITHIN ITS
MESSAGE's FREE ENTRIES, AND OF TWO STRETCHES OF ONE MESSAGE THE ONE THAT STANDS EARLIER IN THE LIST
ENDS WHERE THE LATER BEGINS OR BEFORE (or one of them has no entry), THE BOOK's MAKER's TEST OVER
ALL PAIRS, wantsFree (Honest/BookEntries.lean), ACCEPTS THE LIST. Written by the authors of the
honest side of the linear claim's shared rounds (K14), in the frame's folder, not by the frame's
authors; the makers are theirs. General in the list. One form; statements with their proofs.

  InFront₀ w w'   the form: where the two stretches name one message: one of them has the count 0,
                  or w ends at or before the number at which w' begins
  meets_false_of_front, meets_false_of_back   two runs of which one has no number, or one ends where
                  the other begins or before, do not meet (meets, Honest/Frame.lean)
  wantsFree_of_inFront₀   **the statement of the first sentence**

Why. wantsFree walks all pairs of places of the list. This statement puts a relation between a
stretch and the later ones in its place: a test of one pass, or a law on the makers of the list, can
end in it.
Kin. Honest/BookFree.lean has the other direction: what follows from a yes of wantsFree
(wantsFree_free, wantsFree_apart). meets_iff (Honest/BookGuard.lean) says what meets means; it does
not lie beneath this file. meets_of_le and meets_zero (Honest/BookLinear/Tool.lean) are two of the
three arms of meets_false_of_front, each as a lemma of its own; neither file lies beneath the other.
What is not claimed. The converse: wantsFree accepts lists whose stretches of one message stand in
another order. That any maker's list has the form. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **The earlier stretch stands in front of the later**: where they name one message: one of them
has no entry, or the first ends at or before the number at which the second begins. -/
def InFront₀ (w w' : Want) : Prop :=
  w.msg = w'.msg → w.count = 0 ∨ w'.count = 0 ∨ w.number + w.count ≤ w'.number

/-- Two runs do not meet where one has no number, or the first ends where the second begins or
before. -/
theorem meets_false_of_front {a n b m : Nat} (h : n = 0 ∨ m = 0 ∨ a + n ≤ b) :
    meets a n b m = false := by
  unfold meets
  rcases h with h | h | h
  · simp [h]
  · simp [h]
  · have h' : ¬ b < a + n := by omega
    simp [h']

/-- The like where the second ends where the first begins or before. -/
theorem meets_false_of_back {a n b m : Nat} (h : n = 0 ∨ m = 0 ∨ b + m ≤ a) :
    meets a n b m = false := by
  unfold meets
  rcases h with h | h | h
  · simp [h]
  · simp [h]
  · have h' : ¬ a < b + m := by omega
    simp [h']

/-- **FROM "WITHIN THE FREE ENTRIES" AND "IN FRONT", PAIR BY PAIR IN THE LIST's ORDER, TO THE TEST
OVER ALL PAIRS.** -/
theorem wantsFree_of_inFront₀ {ws : List Want}
    (hF : ∀ w ∈ ws, w.number + w.count ≤ w.msg.free) (hP : ws.Pairwise InFront₀) :
    wantsFree ws = true := by
  unfold wantsFree
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun w hw => decide_eq_true (hF w hw), ?_⟩
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨hi, ea⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 ha)
  obtain ⟨hj, eb⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hb)
  have hp := List.pairwise_iff_getElem.1 hP
  by_cases hij : a.2 = b.2
  · simp [hij]
  · by_cases hm : a.1.msg = b.1.msg
    · have hno : meets a.1.number a.1.count b.1.number b.1.count = false := by
        rcases Nat.lt_or_gt_of_ne hij with h | h
        · have q := hp a.2 b.2 hi hj h
          rw [ea, eb] at q
          exact meets_false_of_front (q hm)
        · have q := hp b.2 a.2 hj hi h
          rw [ea, eb] at q
          rcases q hm.symm with q | q | q
          · exact meets_false_of_back (Or.inr (Or.inl q))
          · exact meets_false_of_back (Or.inl q)
          · exact meets_false_of_back (Or.inr (Or.inr q))
      simp [hno]
    · simp [hm]

end ProofFile.Honest

#print axioms ProofFile.Honest.meets_false_of_front
#print axioms ProofFile.Honest.meets_false_of_back
#print axioms ProofFile.Honest.wantsFree_of_inFront₀

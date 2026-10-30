-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Inner/SaysOffPads.lean: WHAT A ROW THAT A CODE SWITCH MAKES SAYS OF WORDS
HANGS ON THE WORDS AT THE CARRYING MESSAGE AND THE COPIES, OFF THE NEW PADS' PLACES, AND ON NOTHING
ELSE. Two statements with their proofs; no definition. No coin, no round, no frame.

  `copies_covered` where there are no more numbers of copies than entries of the target's list kept:
                    each number is `anew.getD a noId` for an a at which that list has an entry
  `says_offPads` a row whose coefficients are `OnNew` (Inner/RowsOnNew.lean) and `Spares`
                    (Inner/PadsProof.lean) says of words m what it says of words m', where the two
                    are one at g at every part and index that is no place of the pad of the target's
                    shape, and at each copy likewise off the pad of its entry's shape

WHY. `says_onNew` (Inner/RowsOnNew.lean) asks the two words to be one at g and the copies AT EVERY
INDEX, the pads' places too. But no made row has a coefficient there (`padsUnread`,
Inner/PadsProof.lean). So whoever compares `newWords` with words read off a chain's witness need not
know what stands at a pad's place.

How. `says_onNew`'s own proof, term by term, with one more case at g and at a copy: at a pad's place
the coefficient is 0 by `Spares`; elsewhere the words are one.

Limits. "A pad's place" is meant as `padPlaces` (OnBytes/Iop/Cs.lean) lists it: a part and an index.
Nothing here ties that list to `padB` (Johnson/Desc/SeatAt.lean), the test by row and place that a
witness's accessor reads. WHAT THE LIBRARY HAS BETWEEN THE TWO, AS FAR AS WE LOOKED. For a pad in a
MAIN row, in Johnson/Goal/Meaning/LaidInside.lean: `pad_of_padB`: a place that `padB` takes, inside
the row, is one of the list's, at a shape with an answer or more · `padB_of_pad`: back, AT A SHAPE
WITH JUST ONE ANSWER: with more, the list has places for each answer and `padB` those of the last
alone (so the first law's own docstring). For a pad in a MASK row: `padB_inr`
(Johnson/Desc/Sound/MsgSig.lean) ties `padB` to the typed test `padP` (Johnson/Pack/PortZ.lean), not
to this list; A LAW FROM `padB` AT A MASK ROW TO `padPlaces` OR `Send.pad` WAS NOT FOUND: sought
among the theorem names that hold padB, offPad or off_pad, and among the files that name both
 `padB` and `padPlaces`: a
law of another name that speaks of `Send.pad` alone would escape both nets. `OnNew` and `Spares` are
premises here: `rowsOnNew` and `padsUnread` give them of every made row. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Inner.RowsOnNew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE coefAt)
open OnBytes.Means (Words Says value onTable)

/-- Each number of a copy stands at an a at which the target's list has an entry. -/
theorem copies_covered (T : SwitchTarget) (an : Array Nat) (h : an.size ≤ T.kept.size) :
    ∀ o ∈ an.toList, ∃ (a : Nat) (k : KeptTarget), T.kept[a]? = some k ∧ an.getD a noId = o := by
  intro o ho
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem ho
  have ha' : a < an.size := by simpa using ha
  have hk : a < T.kept.size := lt_of_lt_of_le ha' h
  refine ⟨a, T.kept[a], Array.getElem?_eq_getElem hk, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ha']
  simp

/-- **What such a row says hangs on the words at g and the copies, off the new pads' places.** -/
theorem says_offPads (St S : Statement) (T : SwitchTarget) (r : OnBytes.Row) (g : Nat)
    (an : Array Nat) (m m' : Words GE) (hOn : OnNew g an (coefAt r))
    (hSp : Spares S T g an (coefAt r))
    (hcov : ∀ o ∈ an.toList, ∃ (a : Nat) (k : KeptTarget),
      T.kept[a]? = some k ∧ an.getD a noId = o)
    (hG : ∀ part i, (∀ p ∈ padPlaces S.codes T.shape, p.part = part → p.index ≠ i) →
      m g part i = m' g part i)
    (hA : ∀ (a : Nat) (k : KeptTarget), T.kept[a]? = some k → ∀ part i,
      (∀ p ∈ padPlaces S.codes k.shape, p.part = part → p.index ≠ i) →
      m (an.getD a noId) part i = m' (an.getD a noId) part i) :
    Says rdE St r m ↔ Says rdE St r m' := by
  have key : ∀ o part, onTable rdE St r m o part = onTable rdE St r m' o part := by
    intro o part
    unfold onTable
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases e : o = g
    · rw [e]
      by_cases hp : ∀ p ∈ padPlaces S.codes T.shape, p.part = part → p.index ≠ i
      · rw [hG part i hp]
      · push Not at hp
        obtain ⟨p, hpm, h1, h2⟩ := hp
        have z : rdE.val (r.coefficient g part i) = 0 := by
          have h0 := hSp.1 p hpm
          rw [h1, h2] at h0
          exact h0
        rw [z, zero_mul, zero_mul]
    · by_cases e' : o ∈ an.toList
      · obtain ⟨a, k, hk, rfl⟩ := hcov o e'
        by_cases hp : ∀ p ∈ padPlaces S.codes k.shape, p.part = part → p.index ≠ i
        · rw [hA a k hk part i hp]
        · push Not at hp
          obtain ⟨p, hpm, h1, h2⟩ := hp
          have z : rdE.val (r.coefficient (an.getD a noId) part i) = 0 := by
            have h0 := hSp.2 a k hk p hpm
            rw [h1, h2] at h0
            exact h0
          rw [z, zero_mul, zero_mul]
      · have z : rdE.val (r.coefficient o part i) = 0 := hOn o e e' part i
        rw [z, zero_mul, zero_mul]
  unfold Says value
  simp only [key]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.copies_covered
#print axioms VerifiableInference.Desc.K2.Honest.says_offPads

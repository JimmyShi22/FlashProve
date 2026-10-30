-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BorderW.lean: CLOSED FACTS ON THE WRITTEN LIST OF PLACES placesW (Johnson/IMR/WrittenList.lean), BY THE KERNEL: NO PLACE STANDS TWICE; SO THE BORDER's NUMBER, AS First.borderOf COUNTS IT (Johnson/Desc/First/BookNumbers.lean: the index of the place's first occurrence; at «none» the list's length), IS THE NUMBER ITSELF.
Compiled with the whole library.
WANTED BY: bookAt_whole (Johnson/IMR/BookAtWhole.lean; its premise hb : borderOf ps ps[k]? = k) · told_succ (Johnson/Desc/First/ToldSucc.lean; its premise hn : (blockPlaces bs).Nodup, «a closed test on the written list»).
  places_nodup      placesW.Nodup.
  border_W          ∀ k ≤ 358, borderOf placesW placesW[k]? = k.
No state, no sub-protocol is spoken of. No soundness.
-/
import Johnson.IMR.WrittenList
import Johnson.Desc.First.BookNumbers

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (borderOf)

/-- No place twice, as a Bool: each number is the index of its place's first occurrence. -/
def firstAtB : Bool := (List.range 358).all fun k => (placesW[k]?).map placesW.idxOf == some k

set_option maxRecDepth 1000000 in
theorem first_at : firstAtB = true := by decide +kernel

theorem border_W : ∀ k ≤ 358, borderOf placesW placesW[k]? = k := by
  intro k hk
  rcases Nat.lt_or_ge k 358 with h | h
  · have h1 := first_at
    unfold firstAtB at h1
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h1
    obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 (h1 k h)
    rw [hp]
    exact e
  · obtain rfl : k = 358 := by omega
    rw [List.getElem?_eq_none (Nat.le_of_eq places_len)]
    exact places_len

theorem places_nodup : placesW.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij e
  have hi' : i < 358 := by rwa [places_len] at hi
  have hj' : j < 358 := by rwa [places_len] at hj
  have e1 := border_W i (by omega)
  have e2 := border_W j (by omega)
  rw [List.getElem?_eq_getElem hi, e] at e1
  rw [List.getElem?_eq_getElem hj] at e2
  omega

end IM

#print axioms IM.first_at
#print axioms IM.border_W
#print axioms IM.places_nodup

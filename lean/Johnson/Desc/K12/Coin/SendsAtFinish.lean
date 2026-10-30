-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/SendsAtFinish.lean: **WHAT AN ACCEPTING STEP OF THE PROXIMITY TEST AT THE
FIRST CHAIN's FINISH SENDS**, in the three clauses in which a walk along the run asks it of each
sub-protocol. Statement and proof.
  `sends_atFinish`: at EVERY state s in front, for the sub-protocol `(atFinish π).retype`: where its
    step accepts from s to s' and s's codes are `codes`: (1) s' has these codes; (2) the book of
    commitment trees grows by just what the test's sendings `sendsFrom π 0 π.nums.stages.tail` lay
    (`Appends`, BookAppends.lean); (3) if the statement had as many oracle messages as the book has
    places, it has so behind.
PREMISES, both on the sub-protocol's own public numbers: its test `planOk`; `ownMask = false` (the
arm in which the test sends its own mask is not covered by `k12_appends`).
The three clauses are meant as `IM.SendsAt ft codes (sendsFrom π 0 π.nums.stages.tail) _`, unfolded
(Johnson/IMR/SendsFold.lean); that file is not imported here: that they are is BY READING.
A sub-protocol that rejects everything has it for nothing. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.K12Grows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.JointK H2K.Out

/-- **The proximity test's sendings, at the first chain's finish.** -/
theorem sends_atFinish {Cl : Type} (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true)
    (ho : π.nums.ownMask = false) (ft : ℕ) (codes : Codes) (s s' : First.S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : ℕ)
    (hY : ((atFinish π).retype : Block First.S Cl).step ft s rs cols = .ok (s', n))
    (hc : s.st.codes = codes) :
    s'.st.codes = codes ∧ Appends codes (sendsFrom π 0 π.nums.stages.tail) s.book s'.book ∧
      (s.st.oracles.size = s.book.place.size → s'.st.oracles.size = s'.book.place.size) := by
  have hS : Sits ((atFinish π).retype : Block First.S Cl) (proximityTestKind guardedProximityTestParts π : Blk') enterFinish
      leaveFinish := (sits_inside enterFinish (proximityTestKind guardedProximityTestParts π : Blk') leaveFinish).retype
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols n hY
  obtain ⟨o, _, _, _, ht⟩ := Seat.enterFinish_ok s t e1
  obtain ⟨gs, hd⟩ := step_decide (proximityTestKind guardedProximityTestParts π : Blk') ft _ t' rs cols n e2
  have he := early_of_planOk π hp
  have ha := answers_of_planOk π hp
  have hm : t.mask.isSome = true := mask_of_yes π hp ho t t' ft n rs cols e2
  have hl := laysOnly_finish s t' s' e3
  have h1 : s'.st = t'.st := by rw [hl]
  have h2 : s'.book = t'.book := by rw [hl]
  have h3 : t.st = s.st := by rw [ht]
  have h4 : t.book = s.book := by rw [ht]
  obtain ⟨first, rest, hs, hA⟩ := k12_appends π he ha t t' _ gs hm hd
  obtain ⟨first', rest', hs', hSh⟩ := k12_shapes π he ha t t' _ gs hm hd
  obtain rfl : rest = rest' := by
    rw [hs] at hs'
    exact (List.cons.inj hs').2
  have htail : π.nums.stages.tail = rest := by rw [hs]; rfl
  rw [h3, hc, h4] at hA
  refine ⟨?_, ?_, fun hin => ?_⟩
  · rw [h1, ← hc, ← h3]
    exact (k12_out π he ha _ t' _ gs hd).codes
  · rw [htail, h2]
    exact hA
  · obtain ⟨A, a1, a2, _⟩ := hA
    have l1 := laidFrom_places_len codes _ _ A a1
    have l2 := congrArg List.length a2
    have l3 := congrArg List.length hSh
    unfold Door.shapesIn at l3
    rw [List.length_append, Array.length_toList, Array.length_toList] at l2
    rw [List.length_append, List.length_map, List.length_map, Array.length_toList,
      Array.length_toList, h3] at l3
    rw [h1, h2]
    omega

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.sends_atFinish

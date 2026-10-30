-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/RangesFirstTree.lean: THE KEY FILE: «hft»: THE FIRST TREE's NUMBER AT THE RANGES' TEST's PLACE IS 0 WHEREVER THE PLACE's NUMBERS ARE THE MAKER's: A LIGHT FILE: over the maker's own text (Johnson/Desc/Key/Ranges.lean) and bind_ok (Johnson/Desc/ChainEndFold.lean) alone.
WHY: hft : N.nums.firstTree = 0 is the one premise of the step at block 15 (g15, Johnson/RunOne/Law/StepSide15At.lean | gaps_of, Johnson/RunOne/Law/StepSideGaps.lean) and so of aSide_of_hist (Johnson/Top/Fire/Code/KeyASideAtFk.lean) THAT NO TEST OF THE KEY FILE's IOP AS WRITTEN IN LEAN ASKS (by report, not shown here: it closes for every k ≤ 19 «modulo hft … payable in scope from rangesNumbers m = .ok N at the seat»).
  firstTree_of_rangesNumbers   rangesNumbers m = .ok N → N.nums.firstTree = 0: the maker is a do-block that can only refuse until its last step, which returns a structure with «firstTree := 0»
AT THE SEAT: seat_facts (Johnson/Goal/Conditions/KeyMemberAtTheSeat.lean: not in this library) hands «rangesNumbers m = .ok N» among its five equations: so hft at the seat's N is one call.
KIN, SAID: the same fact is the second conjunct of numbers_parts (Johnson/RunOne/Law/K12Facts15A.lean), in a file that stands in row 1.15's cone (it imports the coin's and the seats' files); it is stated again here so that a light file has it. later_firstTree | places_firstTree (Johnson/Desc/K12/Law/FirstTreeOfMade.lean) say the like of the other makers: their proofs are this one's pattern.
OBJECT: Key.rangesNumbers · USER: aSide_at_all (KeyASideAll.lean) · LETTERS: m N. Nothing on soundness.
-/
import Johnson.Desc.Key.Ranges
import Johnson.Desc.ChainEndFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open Johnson.G.OfPlan
open VerifiableInference.Desc.ChainEnd (bind_ok)

/-- **hft, where the place's numbers are the maker's.** -/
theorem firstTree_of_rangesNumbers {m : Made} {N : H2U.PlaceNums} (h : rangesNumbers m = .ok N) :
    N.nums.firstTree = 0 := by
  unfold rangesNumbers at h
  dsimp only at h
  obtain ⟨ts, _, h⟩ := bind_ok h
  obtain ⟨first, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨start, _, h⟩ := bind_ok h
    split at h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain rfl := Except.ok.inj h
      rfl
    · obtain ⟨_, h', _⟩ := bind_ok h
      cases h'
  · obtain ⟨_, h', _⟩ := bind_ok h
    cases h'

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.firstTree_of_rangesNumbers

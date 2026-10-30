-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/GroupsSeatedB.lean: "EVERY TENANT OF EVERY SEGMENT's GROUP IS THE SEAT OF A
MEMBER", FROM TWO TESTS WITH CODE AND ONE PREMISE. Theorems, proved.

`GroupsSeated ms N` (Johnson/Desc/Sound/ReadAt.lean): for every k, every tenant of N.group k is the
seat of a member of ms. It is a premise wherever a witness's table is read by seat through `seatTab`
(which is the zero table, in silence, at a seat of no member).
  `mem_of_seat` (proved): the converse of `seat_mem` (PlanMemProofs.lean): where
    `seatsFitB` says yes (each entry of L has as many seats as shapes): every seat of `allSeats L`
    is the seat of a member of `msOf L`.
  `groupsSeated_of_B` (proved): `seatsFitB G cs L = true` · `groupsAreMembers N n L = true`
    (Johnson/Desc/First/BordersPlan.lean: every seat of the groups 0 … n, the index masks' and W's
    stands among L's seats) · beyond n the groups are empty ⟹ `GroupsSeated (msOf L) N`.
  `index_w_seated` (proved): under the same two tests N.index and N.w are seats of members too.
Limits. "Beyond n the groups are empty" is a premise on N (at a filling off a plan: no tenant is
booked at a segment beyond the last). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ReadAt
import Johnson.Desc.Sound.PlanMemProofs
import Johnson.Desc.First.BordersPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers groupsAreMembers)

theorem mem_of_seat {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (L : MemberLists)
    (h : seatsFitB G cs L = true) (x : ℕ × ℕ) (hx : x ∈ allSeats L) :
    ∃ y ∈ msOf L, seatOf y = x := by
  obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.1 hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxp
  have h1 := List.all_eq_true.1 h p hp
  rw [Bool.and_eq_true, beq_iff_eq] at h1
  have hi' : i < p.1.length := h1.1 ▸ hi
  refine ⟨⟨Sending.ofLists p.1 p.2, ⟨i, hi'⟩⟩, ?_, ?_⟩
  · exact List.mem_flatMap.2 ⟨Sending.ofLists p.1 p.2, List.mem_map.2 ⟨p, hp, rfl⟩,
      List.mem_map.2 ⟨⟨i, hi'⟩, List.mem_finRange _, rfl⟩⟩
  · show p.2.getD i (0, 0) = p.2[i]
    exact List.getD_eq_getElem _ _ hi

theorem groupsSeated_of_B {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (L : MemberLists)
    (h : seatsFitB G cs L = true) (N : Numbers) (n : ℕ) (hG : groupsAreMembers N n L = true)
    (hEnd : ∀ k, n < k → N.group k = []) : GroupsSeated (msOf L) N := by
  intro k x hx
  by_cases hk : n < k
  · rw [hEnd k hk] at hx
    cases hx
  · refine mem_of_seat G cs L h x ?_
    have h1 := List.all_eq_true.1 hG x (List.mem_append_left _
      (List.mem_flatMap.2 ⟨k, List.mem_range.2 (by omega), hx⟩))
    exact List.contains_iff_mem.1 h1

theorem index_w_seated {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (L : MemberLists)
    (h : seatsFitB G cs L = true) (N : Numbers) (n : ℕ) (hG : groupsAreMembers N n L = true) :
    (∃ y ∈ msOf L, seatOf y = N.index) ∧ ∃ y ∈ msOf L, seatOf y = N.w := by
  have a := List.all_eq_true.1 hG N.index (List.mem_append_right _ (by simp))
  have b := List.all_eq_true.1 hG N.w (List.mem_append_right _ (by simp))
  exact ⟨mem_of_seat G cs L h _ (List.contains_iff_mem.1 a),
    mem_of_seat G cs L h _ (List.contains_iff_mem.1 b)⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mem_of_seat
#print axioms VerifiableInference.Desc.Sound.groupsSeated_of_B
#print axioms VerifiableInference.Desc.Sound.index_w_seated

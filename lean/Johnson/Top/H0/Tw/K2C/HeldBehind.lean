-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeldBehind.lean: code switching (the kind K2): TWO MORE OF THE TABLE OF
JOINTS' FIXED TESTS ACCEPT BEHIND A SWITCH: membersHeld (the group's members, read through the
state's book, are just the tenants whose pins are open) and bookAt (the book holds as many trees,
places and messages as the list of rounds says). Rules over letters: nothing of the switch's text
is read here. NO BLOCK IMPORTS THIS FILE.
  membersHeld_behind   an open set whose classes of rows are the switch's three and whose open
                       pins of segment m are «pin m 0» alone · the group number N.groupAt m has
                       the members n0, n0 + 1, … (n of them) · the book seats message n0 + i at
                       seat i · these seats are, as a set, N.sent m 0: membersHeld N O' s = true
  bookAt_behind        bookAt in front · a trees, b places and b messages more behind · N.treesAt
                       | N.msgsAt grow by a | b between the two places: bookAt behind
LIMITS. Every premise on N is a premise on the list of rounds; those on O' are closed facts on the
written list of places. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.RowsHeldAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes
open VerifiableInference.Desc (Place)

theorem membersHeld_behind (N : Numbers) (m : Nat) (s : S) (O' : List Item)
    (hO : O'.filter Item.isRow = switchRowsOpen m) (hP0 : O'.contains (.pin m 0) = true)
    (hP1 : O'.contains (.pin m 1) = false) (hP2 : O'.contains (.pin m 2) = false) {G' : Group}
    (hG : s.st.groups[N.groupAt m]? = some G') {n n0 : Nat} {seat : Nat → Nat × Nat}
    (hM : G'.members.toList = (List.range n).map (· + n0))
    (hB : ∀ i, i < n → s.book.place[n0 + i]? = some (seat i))
    (hS : sameMembers ((List.range n).map seat) (N.sent m 0) = true) :
    membersHeld N O' s = true := by
  have hseg : rowSegs O' = [m] := by
    rw [rowSegs_of_filter (switchRowsOpen m) O' (by rw [hO]; rfl)]
    simp [rowSegs, switchRowsOpen, List.eraseDups_cons]
  have h1 : (G'.members.toList.all fun o => (s.book.place[o]?).isSome) = true := by
    rw [hM, List.all_eq_true]
    intro o ho
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
    rw [Nat.add_comm, hB i (List.mem_range.1 hi)]
    rfl
  have h2 : (G'.members.toList.filterMap fun o => s.book.place[o]?) = (List.range n).map seat := by
    rw [hM, List.filterMap_map]
    rw [List.filterMap_congr (g := fun i => some (seat i)) fun i hi => by
      show s.book.place[i + n0]? = _
      rw [Nat.add_comm, hB i (List.mem_range.1 hi)]]
    show List.filterMap (some ∘ seat) _ = _
    rw [List.filterMap_eq_map]
  have h3 : ((List.range 3).flatMap fun t => if O'.contains (.pin m t) then N.sent m t else []) =
      N.sent m 0 := by
    have q0 : Item.pin m 0 ∈ O' := by simpa using hP0
    have q1 : Item.pin m 1 ∉ O' := by simpa using hP1
    have q2 : Item.pin m 2 ∉ O' := by simpa using hP2
    simp [List.range_succ, q0, q1, q2]
  unfold membersHeld
  rw [hseg]
  simp only [List.all_cons, List.all_nil, hG, h1, h2, h3, hS, Bool.and_self]

theorem bookAt_behind (N : Numbers) (p p' : Option Place) (s s' : S) (a b : Nat)
    (h : bookAt N p s = true) (hT : s'.book.trees.size = s.book.trees.size + a)
    (hPl : s'.book.place.size = s.book.place.size + b)
    (hOr : s'.st.oracles.size = s.st.oracles.size + b) (nT : N.treesAt p' = N.treesAt p + a)
    (nM : N.msgsAt p' = N.msgsAt p + b) : bookAt N p' s' = true := by
  unfold bookAt at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.membersHeld_behind
#print axioms VerifiableInference.Desc.First.K2.bookAt_behind

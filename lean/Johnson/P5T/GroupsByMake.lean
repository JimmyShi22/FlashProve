-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/GroupsByMake.lean: AT THE TABLE's NUMBERS OFF THE ENTRIES (`numbersOf`,
Johnson/P5T/NumbersOf.lean) THE TEST `groupsP` (Johnson/P5T/MembersPlain.lean) IS TWO MEMBERSHIPS:
THE REST OF IT HOLDS BY THE MAKE. Three theorems.

Why. `groupsP N n ps` asks that every (tree, tenant) of every group, the index masks' and W's be an
entry's with a sample. At N := numbersOf ps a group's (tree, tenant)s ARE such entries', by that
definition's own text: so an acceptance there says nothing of the groups: IT IS NO EXAMPLE OF
ANYTHING ON THEM. What is left is said here.
  `sent_mem`, `group_mem`: a (tree, tenant) of numbersOf's sent | group is an entry's with a sample.
  `groupsP_numbersOf`: groupsP N n ps, at any N whose sent is numbersOf ps's, is: N.index is such an
    entry's (tree, tenant), and N.w is.
WHAT THE TWO STILL TEST: `numbersOf` answers (0, 0) in silence where the entries hold no index
masks' message, or no W.

Limits. Nothing on whether the two memberships hold. Nothing on soundness.

-/
import Johnson.P5T.MembersPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc.First (Numbers)

theorem sent_mem (ps : List PSeat) (m t : Nat) (s : Nat × Nat)
    (h : s ∈ (numbersOf ps).sent m t) : s ∈ (ps.filter (·.smpd)).map (·.seat) := by
  have h' : s ∈ (ps.filter fun p => p.seg == some (m, t) && p.smpd && !p.isStart).map (·.seat) := h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h'
  have hp' := List.mem_filter.1 hp
  have h1 := (Bool.and_eq_true_iff.1 hp'.2).1
  exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp'.1, (Bool.and_eq_true_iff.1 h1).2⟩, rfl⟩

theorem group_mem (N : Numbers) (ps : List PSeat) (hS : N.sent = (numbersOf ps).sent) (m : Nat)
    (s : Nat × Nat) (h : s ∈ N.group m) : s ∈ (ps.filter (·.smpd)).map (·.seat) := by
  unfold Numbers.group at h
  rw [hS] at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · exact sent_mem ps m 0 s h
    · exact sent_mem ps m 1 s h
  · exact sent_mem ps m 2 s h

/-- **The test is two memberships.** -/
theorem groupsP_numbersOf (N : Numbers) (n : Nat) (ps : List PSeat)
    (hS : N.sent = (numbersOf ps).sent) :
    groupsP N n ps = (((ps.filter (·.smpd)).map (·.seat)).contains N.index &&
      ((ps.filter (·.smpd)).map (·.seat)).contains N.w) := by
  unfold groupsP
  rw [List.all_append]
  have e : ((List.range (n + 1)).flatMap N.group).all
      ((ps.filter (·.smpd)).map (·.seat)).contains = true := by
    refine List.all_eq_true.2 fun s hs => ?_
    obtain ⟨m, _, hm⟩ := List.mem_flatMap.1 hs
    exact List.contains_iff_mem.2 (group_mem N ps hS m s hm)
  rw [e]
  simp

end P5T

#print axioms P5T.sent_mem
#print axioms P5T.group_mem
#print axioms P5T.groupsP_numbersOf

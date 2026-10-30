-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/GroupsEnd.lean: "THE GROUPS BEYOND THE LAST SEGMENT ARE EMPTY", AT THE NUMBERS THAT
ARE MADE OFF THE PUBLIC PARAMETERS. `GroupsSeated` (Johnson/Desc/Sound/ReadAt.lean) runs over all
numbers k; every theorem that gives it from a test takes, beside the test, the premise hEnd : ∀ k, n
< k → N.group k = []: a sentence over all numbers, which no test can say. Here it is a theorem at N
:= numbersOf (planSeats Z dl) (Johnson/P5T/NumbersOf.lean, PlanSeats.lean), and at what
`Numbers.atBlocks` makes of it. Five theorems. No draw, no count.

  `segOf_lt`: a label that reads back as "link l, moment m" has l below the bound that was asked.
  `seg_planSeats`: a seat of the plan that is a link's has l at most the number of the request's
    groups.
  `group_nil_of_segs`: where every seat's link is at most n, the groups beyond n are empty.
  `groups_end`: hEnd at N := numbersOf (planSeats Z dl), n := the number of the request's groups.
  `groups_end_atBlocks`: the same at (numbersOf (planSeats Z dl)).atBlocks s links bs: that maker
    leaves the field `sent`.

Limits. K04_law IS NOT PROVED BY THIS. n is the number of groups of the request's shape, (reqGroups
Z.first.shape).toList.length: that it is the number of segments that a caller's test runs to is the
caller's. Nothing on what the seats are.
-/
import Johnson.P5T.NumbersOf
import Johnson.Desc.First.NumbersAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.Desc VerifiableInference.Desc.First
open P5T (PSeat segOf planSeats numbersOf)

/-- A label that reads back as "link l, moment m" has l below the bound. -/
theorem segOf_lt {groups moments : ℕ} {label : String} {l m : ℕ}
    (h : segOf groups moments label = some (l, m)) : l < groups := by
  unfold segOf at h
  obtain ⟨a, ha, h1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨b, -, h2⟩ := List.exists_of_findSome?_eq_some h1
  split at h2
  · obtain rfl : a = l := congrArg Prod.fst (Option.some.inj h2)
    exact List.mem_range.1 ha
  · cases h2

/-- A seat of the plan that is a link's: the link is at most the number of the request's groups. -/
theorem seg_planSeats {Z : ProofFile.Pub} {dl : List Fmt.DeclaredRound} {p : PSeat}
    (hp : p ∈ planSeats Z dl) {l t : ℕ} (h : p.seg = some (l, t)) :
    l ≤ (OnBytes.reqGroups Z.first.shape).toList.length := by
  unfold planSeats at hp
  obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 hp
  split at hs
  · cases hs
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
    exact Nat.lt_succ_iff.1 (segOf_lt h)

/-- Where every seat's link is at most n, the groups beyond n are empty. -/
theorem group_nil_of_segs {ps : List PSeat} {n : ℕ}
    (h : ∀ p ∈ ps, ∀ l t, p.seg = some (l, t) → l ≤ n) {k : ℕ} (hk : n < k) :
    (numbersOf ps).group k = [] := by
  have key : ∀ t, (numbersOf ps).sent k t = [] := by
    intro t
    show (ps.filter fun p => p.seg == some (k, t) && p.smpd && !p.isStart).map (·.seat) = []
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p hp hq
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hq
    exact absurd (h p hp k t hq.1.1) (by omega)
  unfold Numbers.group
  rw [key 0, key 1, key 2]
  rfl

/-- **The groups beyond the last segment are empty**, at the numbers off the plan's seats. -/
theorem groups_end (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (k : ℕ)
    (hk : (OnBytes.reqGroups Z.first.shape).toList.length < k) :
    (numbersOf (planSeats Z dl)).group k = [] :=
  group_nil_of_segs (fun _ hp _ _ h => seg_planSeats hp h) hk

/-- The same at what `Numbers.atBlocks` makes of these numbers. -/
theorem groups_end_atBlocks {St Cl : Type} (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound)
    (s : OnBytes.Params.ReqShape) (links : List ModelPart) (bs : List (Block St Cl)) (k : ℕ)
    (hk : (OnBytes.reqGroups Z.first.shape).toList.length < k) :
    ((numbersOf (planSeats Z dl)).atBlocks s links bs).group k = [] :=
  groups_end Z dl k hk

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.segOf_lt
#print axioms OnBytes.Road.K4.seg_planSeats
#print axioms OnBytes.Road.K4.group_nil_of_segs
#print axioms OnBytes.Road.K4.groups_end
#print axioms OnBytes.Road.K4.groups_end_atBlocks

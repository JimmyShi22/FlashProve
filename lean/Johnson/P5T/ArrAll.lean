-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/ArrAll.lean: THE WITNESS's NUMBERING OVER ALL THREE CHAINS' SEATS AGREES WITH THE
NUMBERING OVER THE FIRST CHAIN's SEATS, AT EVERY SEAT OF THE FIRST CHAIN. Five theorems. It names no
Mathlib.

Why. `arrOf ps` (Johnson/P5T/PlanSeats.lean) gives every seat outside ps one number (the number of
keys). One arr for the tables of all three chains must tell every chain's tenants apart: it is read
at `planSeatsAll`. What was evaluated or proved at the first chain's list carries over by these.
  `idxOf_eraseDups_append`: a member of the front keeps its place among the members, each once, of a
    longer list.
  `arrOf_append`: where the seat (j, t) has a holder in ps, `arrOf (ps ++ qs) j t = arrOf ps j t`.
  `numOfPlan_append`: where the key (0, l, k) is a key of ps, the like for `numOfPlan`.
  `arrOf_all`, `numOfPlan_all`: both at `planSeatsAll Z D`, whose first part is `planSeats Z D.1`.

Limits. Nothing on a seat of the two later chains. Nothing on soundness.

-/
import Johnson.P5T.NumOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T

/-- A key of the front keeps its place among the keys, each once, of a longer list. -/
theorem idxOf_eraseDups_append {α : Type} [BEq α] [LawfulBEq α] (A B : List α) (x : α)
    (h : x ∈ A) : ((A ++ B).eraseDups).idxOf x = (A.eraseDups).idxOf x := by
  rw [List.eraseDups_append]
  exact List.idxOf_append_of_mem (List.mem_eraseDups.2 h)

theorem arrOf_append (ps qs : List PSeat) (j t : Nat) (p : PSeat)
    (h : (ps.find? fun p => p.j == j && p.t == t) = some p) :
    arrOf (ps ++ qs) j t = arrOf ps j t := by
  have h' : ((ps ++ qs).find? fun p => p.j == j && p.t == t) = some p := by
    rw [List.find?_append, h]
    rfl
  rw [arrOf_of_find ps j t p h, arrOf_of_find (ps ++ qs) j t p h', List.map_append]
  exact idxOf_eraseDups_append _ _ _ (List.mem_map_of_mem (List.mem_of_find?_eq_some h))

theorem numOfPlan_append (ps qs : List PSeat) (l k : Nat) (h : (0, l, k) ∈ ps.map keyOf) :
    numOfPlan (ps ++ qs) l k = numOfPlan ps l k := by
  unfold numOfPlan
  rw [List.map_append]
  exact idxOf_eraseDups_append _ _ _ h

/-- **At every seat of the first chain the numbering over all three chains is the first chain's.**
-/
theorem arrOf_all (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (j t : Nat) (p : PSeat)
    (h : ((planSeats Z D.1).find? fun p => p.j == j && p.t == t) = some p) :
    arrOf (planSeatsAll Z D) j t = arrOf (planSeats Z D.1) j t := by
  unfold planSeatsAll
  simp only [List.append_assoc]
  exact arrOf_append _ _ j t p h

theorem numOfPlan_all (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (l k : Nat)
    (h : (0, l, k) ∈ (planSeats Z D.1).map keyOf) :
    numOfPlan (planSeatsAll Z D) l k = numOfPlan (planSeats Z D.1) l k := by
  unfold planSeatsAll
  simp only [List.append_assoc]
  exact numOfPlan_append _ _ l k h

end P5T

#print axioms P5T.idxOf_eraseDups_append
#print axioms P5T.arrOf_append
#print axioms P5T.numOfPlan_append
#print axioms P5T.arrOf_all
#print axioms P5T.numOfPlan_all

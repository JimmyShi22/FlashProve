-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/E3OrdKey.lean.
The order of the last key level in the key file's lookup, as a permutation.

The Lean verifier's lookup for a key file (OnBytes/Iop/Lkp.lean, `orderBeginning`) binds the
variables that the public inputs name first, and then the others from the highest down.
Main names:
  `beginList`: that list; `beginList_eq_key`: it is `OnBytes.Lkp.orderBeginning`, by rfl.
  `beginList_perm`: it is a permutation of 0, …, k - 1 if the named variables are below k and
    pairwise distinct.
  `ordBegin`: the permutation; `ordBegin_val`: round j binds the list's entry j.
Examples by evaluation stand at the end.
Limits: the program tests a like condition on its public inputs (`Public.orderOK`); no statement
here compares the two, or says at which level the program uses the list.

-/
import Cb.Pv.Lookup.Order.E3Ord
import OnBytes.Iop.Lkp

set_option autoImplicit false

namespace E3

/-- The list of `OnBytes.Lkp.orderBeginning`, letter by letter. -/
def beginList (first : List ℕ) (k : ℕ) : List ℕ :=
  first ++ ((List.range k).reverse).filter fun j => !first.contains j

theorem beginList_eq_key (first : List ℕ) (k : ℕ) :
    beginList first k = OnBytes.Lkp.orderBeginning first k := rfl

theorem beginList_perm (first : List ℕ) (k : ℕ) (h1 : ∀ j ∈ first, j < k) (h2 : first.Nodup) :
    (beginList first k).Perm (List.range k) := by
  unfold beginList
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun x => ?_
  · refine List.Nodup.append h2 ((List.nodup_reverse.2 List.nodup_range).filter _) ?_
    intro x hx hy
    simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hy
    exact hy.2 hx
  · simp only [List.mem_append, List.mem_filter, List.mem_reverse, List.mem_range,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    constructor
    · rintro (h | h)
      · exact h1 x h
      · exact h.1
    · intro h
      by_cases hx : x ∈ first
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩

/-- The order that beginList says, as a permutation. -/
def ordBegin (first : List ℕ) (k : ℕ) (h1 : ∀ j ∈ first, j < k) (h2 : first.Nodup) :
    Equiv.Perm (Fin k) :=
  permOfList k (beginList first k) (beginList_perm first k h1 h2)

theorem ordBegin_val (first : List ℕ) (k : ℕ) (h1 : ∀ j ∈ first, j < k) (h2 : first.Nodup)
    (j : Fin k) :
    ((ordBegin first k h1 h2 j : Fin k) : ℕ) = (beginList first k).getD j.1 0 :=
  permOfList_val k _ _ j

/-! ### Examples by evaluation -/
example : beginList [1] 3 = [1, 2, 0] := by decide
example : beginList [] 2 = [1, 0] := by decide
example : beginList [] 2 = defaultList 2 := by decide
example : ((ordBegin [1] 3 (by decide) (by decide) 0 : Fin 3) : ℕ) = 1 := by decide
example : ((ordBegin [1] 3 (by decide) (by decide) 1 : Fin 3) : ℕ) = 2 := by decide
example : ((ordBegin [1] 3 (by decide) (by decide) 2 : Fin 3) : ℕ) = 0 := by decide
example : (((ordBegin [1] 3 (by decide) (by decide)).symm 0 : Fin 3) : ℕ) = 2 := by decide
example : lastList 12 3 = beginList ([2, 1, 0, 5, 4, 3, 8, 7, 6].map (3 + ·)) 12 := by decide
example : lastList 23 4 = beginList ([2, 1, 0, 5, 4, 3, 8, 7, 6].map (4 + ·)) 23 := by decide
example : lastList 9 0 = beginList [2, 1, 0, 5, 4, 3, 8, 7, 6] 9 := by decide

end E3

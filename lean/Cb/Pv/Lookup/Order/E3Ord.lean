-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Order/E3Ord.lean.
Orders in which a sumcheck binds its variables, as permutations that can be computed.

A list that names each of the numbers 0, …, k − 1 once gives a permutation of Fin k (permOfList):
round j binds the variable that the list names at place j, and the inverse is the place of a
variable in the list.
The file has the two lists of the lookup in the sub-proofs of the Lean verifier (OnBytes/Model/):
from the highest variable down (defaultList), and the list of the last key level of a forest
(lastList: nine variables above the tree's number in three groups of three, then the others from the
top down, then the tree's number). It proves that both are permutations (the second if at least nine
variables stand above the tree's number), names the orders ordDefault, ordLast and ordKeys, and
proves that lastList is `PL.rangeBits` (Blocks/Ext.lean; rangeBits_eq).
Limits: a list names a variable by its bit of the index, as OnBytes/Model/Forest.lean does; in
Blocks/Ext.lean that is a bit position, and the variable is counted from the other end (rangeOrd).
lastList is a permutation only if at least nine variables stand above the tree's number;
`Forest.shape` (OnBytes/Model/Forest.lean) tests this as a tree's depth of at least 10, and ordKeys
takes that bound as an argument.
That the two lists are that program's own terms is not stated here but in
OnBytes/Tie/Pv/Lookup/Port/E3OrdPort.lean. That ordKeys is its choice between the two
(OnBytes/Model/Look.lean) is stated in no file of this library.

-/
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Equiv.Defs
import Blocks.Ext

set_option autoImplicit false

namespace E3

/-- The order that a list says. -/
def permOfList (k : ℕ) (l : List ℕ) (h : l.Perm (List.range k)) : Equiv.Perm (Fin k) where
  toFun j := ⟨l[j.1]'(by rw [h.length_eq, List.length_range]; exact j.2),
    List.mem_range.mp (h.subset (List.getElem_mem _))⟩
  invFun i := ⟨l.idxOf i.1, by
    have h1 : i.1 ∈ l := h.symm.subset (List.mem_range.mpr i.2)
    have h2 := List.idxOf_lt_length_of_mem h1
    rwa [h.length_eq, List.length_range] at h2⟩
  left_inv j := Fin.ext ((h.symm.nodup List.nodup_range).idxOf_getElem _ _)
  right_inv i := Fin.ext (List.getElem_idxOf _)

/-- what it says: round j binds the list's entry j -/
theorem permOfList_val (k : ℕ) (l : List ℕ) (h : l.Perm (List.range k)) (j : Fin k) :
    ((permOfList k l h j : Fin k) : ℕ) = l.getD j.1 0 := by
  have hj : j.1 < l.length := by rw [h.length_eq, List.length_range]; exact j.2
  show l[j.1] = _
  rw [List.getD_eq_getElem _ _ hj]

/-- The Lean verifier's list for the last key level, letter for letter
(`OnBytes.Model.Forest.orderForestRange`, OnBytes/Model/Forest.lean). That it is that term:
`lastList_eq_port`, OnBytes/Tie/Pv/Lookup/Port/E3OrdPort.lean, by rfl. -/
def lastList (mu rK : ℕ) : List ℕ :=
  [2, 1, 0, 5, 4, 3, 8, 7, 6].map (rK + ·) ++
    ((List.range (mu - (rK + 9))).map (rK + 9 + ·)).reverse ++ (List.range rK).reverse

/-- The Lean verifier's default list (`OnBytes.Model.orderDefault`, OnBytes/Model/Frame.lean). That
it is that term: `defaultList_eq_port`, OnBytes/Tie/Pv/Lookup/Port/E3OrdPort.lean, by rfl. -/
def defaultList (mu : ℕ) : List ℕ := (List.range mu).reverse

theorem nine_perm : [2, 1, 0, 5, 4, 3, 8, 7, 6].Perm (List.range 9) := by decide

/-- The list for the last key level names each of the mu variables once, if at least nine bits stand
above the tree's number. -/
theorem lastList_perm {mu rK : ℕ} (h : rK + 9 ≤ mu) : (lastList mu rK).Perm (List.range mu) := by
  obtain ⟨m, rfl⟩ : ∃ m, mu = rK + 9 + m := ⟨mu - (rK + 9), by omega⟩
  unfold lastList
  rw [Nat.add_sub_cancel_left, List.range_add, List.range_add]
  rw [List.append_assoc (List.range rK)]
  exact List.perm_append_comm.trans
    ((List.reverse_perm _).append ((nine_perm.map _).append (List.reverse_perm _)))

/-- The default order: from the top variable down. -/
def ordDefault (k : ℕ) : Equiv.Perm (Fin k) := Fin.revPerm

theorem defaultList_perm (k : ℕ) : (defaultList k).Perm (List.range k) := List.reverse_perm _

/-- The default order is the order that defaultList says. -/
theorem ordDefault_eq (k : ℕ) : ordDefault k = permOfList k (defaultList k) (defaultList_perm k) :=
    by
  refine Equiv.ext fun j => Fin.ext ?_
  show k - (j.1 + 1) = (List.range k).reverse[j.1]'_
  rw [List.getElem_reverse, List.getElem_range, List.length_range]
  omega

/-- The last key level's order. -/
def ordLast (mu rK : ℕ) (h : rK + 9 ≤ mu) : Equiv.Perm (Fin mu) :=
  permOfList mu (lastList mu rK) (lastList_perm h)

/-- The order at the key level with k variables, in a forest of 2^rK trees of 2^dT keys: ordLast at
the last level (k + 1 = dT + rK), ordDefault at the others. No statement compares it with the Lean
verifier's choice (OnBytes/Model/Look.lean). -/
def ordKeys (dT rK : ℕ) (h : 10 ≤ dT) (k : ℕ) : Equiv.Perm (Fin k) :=
  if e : k + 1 = dT + rK then ordLast k rK (by omega) else ordDefault k

theorem ordKeys_last (dT rK : ℕ) (h : 10 ≤ dT) (k : ℕ) (e : k + 1 = dT + rK) :
    ordKeys dT rK h k = ordLast k rK (by omega) := dif_pos e
theorem ordKeys_other (dT rK : ℕ) (h : 10 ≤ dT) (k : ℕ) (e : k + 1 ≠ dT + rK) :
    ordKeys dT rK h k = ordDefault k := dif_neg e

/-- round j binds the list's entry j -/
theorem ordLast_val (mu rK : ℕ) (h : rK + 9 ≤ mu) (j : Fin mu) :
    ((ordLast mu rK h j : Fin mu) : ℕ) = (lastList mu rK).getD j.1 0 := permOfList_val _ _ _ j

/-- The library's other lookup (Blocks/Ext.lean `PL.rangeBits`: bit positions) has the same list. -/
theorem rangeBits_eq (mu rK : ℕ) : Blocks.PL.rangeBits mu rK = lastList mu rK := by
  unfold Blocks.PL.rangeBits lastList
  congr 1
  · congr 1
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    omega
  · refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]

/-! ### Guards by evaluation -/
example : lastList 12 3 = [5, 4, 3, 8, 7, 6, 11, 10, 9, 2, 1, 0] := by decide
example : lastList 12 2 = [4, 3, 2, 7, 6, 5, 10, 9, 8, 11, 1, 0] := by decide
example : lastList 23 4 =
    [6, 5, 4, 9, 8, 7, 12, 11, 10, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 3, 2, 1, 0] := by decide
/-- the order is neither the identity nor the reversal -/
example : (ordLast 12 3 (by omega) 0 : Fin 12) = 5 := by decide
example : ((ordLast 12 3 (by omega)).symm 5 : Fin 12) = 0 := by decide

end E3

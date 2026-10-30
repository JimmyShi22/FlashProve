-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevOrd.lean: orders in which a level of a product tree binds its variables, as
computable terms without a hypothesis in their types.

An order of k variables is an `Equiv.Perm (Fin k)`: σ j is the variable that round j binds.
  `beginList first k`  the named variables first, the others from the highest down, as a list.
  `BeginOK first k`    every named variable is below k and none is named twice; decidable.
  `ordOf first k`      the order that `beginList first k` says if `BeginOK first k`; else from the
                       highest variable down.
  `ordOf_val`          under `BeginOK`: round j binds the list's entry j.
  `ordOf_nil`          with no variable named it is the reversal.
  `rev_val`            the reversal, read off the list `(List.range k).reverse`.
  `ordKey first v l`   key level l of a part of 2^v keys: `ordOf first` at the last level
                       (l + 1 = v), the reversal elsewhere.
  `ordTab mu l`        level l of the table's tree: the reversal.
Conditions: none.
Not claimed: that these lists are the terms of the verifier in OnBytes/Iop/Lkp.lean. Where `BeginOK`
fails, `ordOf` falls back to the reversal, while that verifier refuses.
`beginList`, `beginList_perm`, `ordBegin`, `ordBegin_val`: after E3OrdKey.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Order.E3Ord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open E3

/-- the named variables first, the others from the highest down -/
def beginList (first : List ℕ) (k : ℕ) : List ℕ :=
  first ++ ((List.range k).reverse).filter fun j => !first.contains j

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
      Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not]
    constructor
    · rintro (h | h)
      · exact h1 x h
      · exact h.1
    · intro h
      by_cases hx : x ∈ first
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩

def ordBegin (first : List ℕ) (k : ℕ) (h1 : ∀ j ∈ first, j < k) (h2 : first.Nodup) : Equiv.Perm (Fin
    k) :=
  permOfList k (beginList first k) (beginList_perm first k h1 h2)

theorem ordBegin_val (first : List ℕ) (k : ℕ) (h1 : ∀ j ∈ first, j < k) (h2 : first.Nodup) (j : Fin
    k) :
    ((ordBegin first k h1 h2 j : Fin k) : ℕ) = (beginList first k).getD j.1 0 :=
  permOfList_val k _ _ j

/-- the list may begin an order of k variables -/
def BeginOK (first : List ℕ) (k : ℕ) : Prop := (∀ j ∈ first, j < k) ∧ first.Nodup

instance (first : List ℕ) (k : ℕ) : Decidable (BeginOK first k) :=
  inferInstanceAs (Decidable ((∀ j ∈ first, j < k) ∧ first.Nodup))

/-- The order of k variables that begins with `first`. No hypothesis: where `first` is no beginning,
from the highest down. -/
def ordOf (first : List ℕ) (k : ℕ) : Equiv.Perm (Fin k) :=
  if h : BeginOK first k then ordBegin first k h.1 h.2 else Fin.revPerm

theorem ordOf_ok {first : List ℕ} {k : ℕ} (h : BeginOK first k) : ordOf first k = ordBegin first k
    h.1 h.2 :=
  dif_pos h

/-- round j binds the list's entry j -/
theorem ordOf_val {first : List ℕ} {k : ℕ} (h : BeginOK first k) (j : Fin k) :
    ((ordOf first k j : Fin k) : ℕ) = (beginList first k).getD j.1 0 := by
  rw [ordOf_ok h]
  exact ordBegin_val first k h.1 h.2 j

/-- the reversal, read off the list -/
theorem rev_val (k : ℕ) (j : Fin k) :
    ((Fin.revPerm j : Fin k) : ℕ) = ((List.range k).reverse).getD j.1 0 := by
  have h := congrArg (fun σ : Equiv.Perm (Fin k) => ((σ j : Fin k) : ℕ)) (ordDefault_eq k)
  exact h.trans (permOfList_val k _ _ j)

theorem beginList_nil (k : ℕ) : beginList [] k = (List.range k).reverse := by
  unfold beginList
  simp

theorem beginOK_nil (k : ℕ) : BeginOK [] k := ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩

/-- with no variable named: from the highest down -/
theorem ordOf_nil (k : ℕ) : ordOf [] k = Fin.revPerm := by
  refine Equiv.ext fun j => Fin.ext ?_
  rw [ordOf_val (beginOK_nil k) j, beginList_nil, rev_val]

/-- Key level l (it has l variables) of a part of 2^v keys. -/
def ordKey (first : List ℕ) (v l : ℕ) : Equiv.Perm (Fin (0 + l)) :=
  if l + 1 = v then ordOf first (0 + l) else Fin.revPerm

theorem ordKey_last (first : List ℕ) {v l : ℕ} (h : l + 1 = v) : ordKey first v l = ordOf first (0 +
    l) := if_pos h
theorem ordKey_other (first : List ℕ) {v l : ℕ} (h : l + 1 ≠ v) : ordKey first v l = Fin.revPerm :=
    if_neg h

/-- Level l of the table's tree (mu + l variables). -/
def ordTab (mu l : ℕ) : Equiv.Perm (Fin (mu + l)) := Fin.revPerm

/-! ### Guards by evaluation (kernel) -/
example : beginList [1] 3 = [1, 2, 0] := by decide
example : beginList [] 2 = [1, 0] := by decide
example : (List.ofFn fun j : Fin (0 + 3) => ((ordKey [1] 4 3 j : Fin (0 + 3)) : ℕ)) = [1, 2, 0] :=
    by decide
example : (List.ofFn fun j : Fin (0 + 2) => ((ordKey [1] 4 2 j : Fin (0 + 2)) : ℕ)) = [1, 0] := by
    decide
example : (List.ofFn fun j : Fin (0 + 3) => (((ordKey [1] 4 3).symm j : Fin (0 + 3)) : ℕ)) = [2, 0,
    1] := by decide

end Lk6

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/KeyLookup/ClosePort.lean: the order of the rounds of the closing and of the test of
the bits is the program's `Lkp.defaultOrder`, and the program's `Lkp.byVariable` at that order
reverses a list, as the end points of the two sumchecks do.

It imports ClosePoint.lean (under it Close.lean, Bits.lean) and OnBytes/Iop/Lkp.lean.
Main names:
  `ordC_default`  the order `ordC k`, as a list of variables' numbers in the order of the rounds, is
                  `Lkp.defaultOrder k`.
  `en_vars_port`  the list of the closing's variables `(A.En P).par.vars x` is
                  `Lkp.defaultOrder (mu + d)`, mapped: round i binds the variable that stands at
                  place i, with the equality weight at that coordinate of x.pt. The degrees in that
                  statement (1 at t < mu, else 2) are held against no term of the program here.
  `bt_vars_port`  the same for the test of the bits, at the zero point; degree 2.
  `byVariable_default`   `Lkp.byVariable` at the default order reverses the list of challenges.
  `ofFn_rev`, `ptE_list`, `ptB_list`   the end points, listed by variable, are the places of the
                  sumcheck's point, listed by round, reversed.
Limits: not shown here that the values of `Lkp.run` are those of the description.

-/
import Cb.Pv.KeyLookup.ClosePoint
import OnBytes.Iop.Lkp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp

theorem ordC_default (k : ℕ) :
    (List.ofFn fun i : Fin k => ((ordC k i : Fin k) : ℕ)) = OnBytes.Lkp.defaultOrder k := by
  unfold OnBytes.Lkp.defaultOrder
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < k := by simpa using h1
    rw [List.getElem_ofFn, List.getElem_reverse, List.getElem_range]
    show ((Fin.revPerm (⟨i, hi⟩ : Fin k) : Fin k) : ℕ) = _
    rw [Fin.revPerm_apply, Fin.val_rev]
    simp
    omega

/-- In a list of pairs whose first members are all different, the i-th first member finds the i-th
    second member. -/
private theorem lookup_zip {α : Type} : ∀ (l : List ℕ) (g : List α) (i : ℕ) (hi : i < l.length)
    (hg : i < g.length), l.Nodup → (l.zip g).lookup l[i] = some g[i]
  | [], _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, hg, _ => absurd hg (Nat.not_lt_zero _)
  | a :: l, b :: g, 0, _, _, _ => by simp
  | a :: l, b :: g, i + 1, hi, hg, hn => by
    have hi' : i < l.length := Nat.lt_of_succ_lt_succ hi
    have hg' : i < g.length := Nat.lt_of_succ_lt_succ hg
    have hne : l[i] ≠ a := fun h => (List.nodup_cons.1 hn).1 (h ▸ List.getElem_mem hi')
    show List.lookup l[i] ((a, b) :: l.zip g) = some g[i]
    rw [List.lookup_cons, beq_false_of_ne hne]
    exact lookup_zip l g i hi' hg' (List.nodup_cons.1 hn).2

theorem byVariable_default (g : List OnBytes.E) :
    OnBytes.Lkp.byVariable g (OnBytes.Lkp.defaultOrder g.length) = g.reverse := by
  unfold OnBytes.Lkp.byVariable OnBytes.Lkp.defaultOrder
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    have ht : t < g.length := by simpa using h1
    rw [List.getElem_map, List.getElem_range, List.getElem_reverse]
    have hl : g.length - 1 - t < (List.range g.length).reverse.length := by simp; omega
    have he : (List.range g.length).reverse[g.length - 1 - t]'hl = t := by
      rw [List.getElem_reverse, List.getElem_range]
      simp
      omega
    have h := lookup_zip (List.range g.length).reverse g (g.length - 1 - t) hl (by omega)
      (List.nodup_reverse.2 List.nodup_range)
    rw [he] at h
    rw [h]
    rfl

theorem ofFn_rev {α : Type} (k : ℕ) (γ : Fin k → α) :
    (List.ofFn fun t : Fin k => γ t.rev) = (List.ofFn γ).reverse := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < k := by simpa using h1
    rw [List.getElem_ofFn, List.getElem_reverse, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    rw [Fin.val_rev]
    simp
    omega

/-! ### the list of a sumcheck's variables is the program's order, mapped; the end point by variable
is the reversal -/
section
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A)

/-- The closing: round i binds the variable that `Lkp.defaultOrder (mu + d)` names at place i, with
    the equality weight at that coordinate of x.pt, in a
polynomial of degree 1 (a plane's variable) or 2 (a row's). -/
theorem en_vars_port (x : A.XS) :
    (A.En P).par.vars x =
      (OnBytes.Lkp.defaultOrder (A.mu + A.d)).map fun t =>
        (pfCube E (if t < A.mu then 1 else 2)).var
          (pdEq E (if t < A.mu then 1 else 2) (x.pt t)) := by
  rw [A.en_vars_at P x, ← ordC_default, List.map_ofFn]
  rfl

/-- The test of the bits: the same order, at the zero point, degree 2. -/
theorem bt_vars_port (x : A.XS) :
    (A.BT P).vars (A.bitsIn P x).2 =
      (OnBytes.Lkp.defaultOrder (A.mu + A.d)).map fun t =>
        (pfCube E 2).var (pdEq E 2 (x.zt t)) := by
  rw [A.bt_vars_at P x, ← ordC_default, List.map_ofFn]
  rfl

/-- The end points, listed by variable, are the challenges, listed by round, reversed: as
    `byVariable` at the default order (`byVariable_default`). -/
theorem ptE_list (zz : (A.En P).par.Mid) :
    List.ofFn (A.ptE P zz) = (List.ofFn (A.gamE P zz)).reverse := ofFn_rev _ _
theorem ptB_list (o : (A.BT P).par.Out) :
    List.ofFn (A.ptB P o) = (List.ofFn fun i : Fin (A.mu + A.d) => A.gamB P o i).reverse :=
  ofFn_rev _ fun i : Fin (A.mu + A.d) => A.gamB P o i

end

end Lk6

#print axioms Lk6.ordC_default
#print axioms Lk6.byVariable_default
#print axioms Lk6.ofFn_rev
#print axioms Lk6.en_vars_port
#print axioms Lk6.bt_vars_port
#print axioms Lk6.ptE_list

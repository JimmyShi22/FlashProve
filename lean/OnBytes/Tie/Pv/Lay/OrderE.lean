-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/OrderE.lean: the order in which the programs bind a product layer's variables, as
the permutation that the product layer of Cb/Pv/Lay/Prod.lean takes.

The programs give the order as a list of variables (Model.orderDefault, Model.orderRange); variable
v stands at coordinate mu - 1 - v of the point. The product layer takes e : Fin k ≃ Fin k: round j
binds coordinate e j.

Main names:
  `ordE mu order h`: the permutation of a list that is a permutation of the mu variables.
  `ordE_val`: round j binds coordinate mu - 1 - order[j].
  `ordE_coords`: the coordinates in the rounds' order are `coords mu order`
    (OnBytes/Tie/Pv/Lay/Order.lean).
  `eDefault`, `eRange`: the two orders of the programs; `eRange` from 9 variables on.
  `eDefault_val`: the default order binds coordinate j in round j.
  `eRange_coords`: the range order's coordinates, written out.
  `prod_point`: in a product layer at e := ordE mu order h the equality weight of round j is at the
    point's coordinate mu - 1 - order[j].

Limits: below 9 variables the programs' orderRange is no permutation of the variables, and nothing
is said of it. That the programs' routines bind in these orders is by reading them.
-/
import OnBytes.Tie.Pv.Lay.Order
import Cb.Pv.Lay.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model Cb.Pv.Lay

theorem perm_lt {mu : ℕ} {order : List ℕ} (h : order.Perm (List.range mu)) (j : Fin mu) :
    order[j.val]'(by rw [h.length_eq, List.length_range]; exact j.2) < mu :=
  List.mem_range.1 (h.subset (List.getElem_mem _))

/-- round j ↦ the coordinate of the j-th variable of the list -/
def ordF (mu : ℕ) (order : List ℕ) (h : order.Perm (List.range mu)) (j : Fin mu) : Fin mu :=
  ⟨mu - 1 - order[j.val]'(by rw [h.length_eq, List.length_range]; exact j.2), by
    have := j.2
    omega⟩

theorem ordF_inj (mu : ℕ) (order : List ℕ) (h : order.Perm (List.range mu)) :
    Function.Injective (ordF mu order h) := fun i j hij => by
  have h1 : mu - 1 - order[i.val]'(by rw [h.length_eq, List.length_range]; exact i.2) =
      mu - 1 - order[j.val]'(by rw [h.length_eq, List.length_range]; exact j.2) :=
    congrArg Fin.val hij
  have hi := perm_lt h i
  have hj := perm_lt h j
  have h2 : order[i.val]'(by rw [h.length_eq, List.length_range]; exact i.2) =
      order[j.val]'(by rw [h.length_eq, List.length_range]; exact j.2) := by omega
  have hnd : order.Nodup := h.nodup_iff.2 List.nodup_range
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h2)

/-- The permutation. -/
noncomputable def ordE (mu : ℕ) (order : List ℕ) (h : order.Perm (List.range mu)) : Fin mu ≃ Fin mu
    :=
  Equiv.ofBijective (ordF mu order h) (Finite.injective_iff_bijective.1 (ordF_inj mu order h))

theorem ordE_val (mu : ℕ) (order : List ℕ) (h : order.Perm (List.range mu)) (j : Fin mu) :
    (ordE mu order h j).val =
      mu - 1 - order[j.val]'(by rw [h.length_eq, List.length_range]; exact j.2) := rfl

theorem ordE_coords (mu : ℕ) (order : List ℕ) (h : order.Perm (List.range mu)) :
    List.ofFn (fun j => (ordE mu order h j).val) = coords mu order := by
  have hl : order.length = mu := by rw [h.length_eq, List.length_range]
  refine List.ext_getElem (by simp [coords, hl]) fun i h1 h2 => ?_
  simp [coords, ordE_val]

/-- the programs' two orders -/
noncomputable def eDefault (mu : ℕ) : Fin mu ≃ Fin mu := ordE mu (orderDefault mu) (default_perm mu)
noncomputable def eRange (mu : ℕ) (h : 9 ≤ mu) : Fin mu ≃ Fin mu :=
  ordE mu (orderRange mu) (range_perm mu h)

theorem eDefault_coords (mu : ℕ) :
    List.ofFn (fun j => (eDefault mu j).val) = List.range mu :=
  (ordE_coords mu _ _).trans (default_coords mu)

theorem eDefault_val (mu : ℕ) (j : Fin mu) : (eDefault mu j).val = j.val := by
  have h := congrArg (fun l => l[j.val]?) (eDefault_coords mu)
  simpa [j.2] using h

theorem eRange_coords (mu : ℕ) (h : 9 ≤ mu) :
    List.ofFn (fun j => (eRange mu h j).val) = coords mu (orderRange mu) :=
  ordE_coords mu _ _

/-- The equality weight of round j. -/
theorem prod_point {E : Type} [Field E] [Fintype E] (L : ProdL E) (order : List ℕ)
    (h : order.Perm (List.range L.k)) (he : L.e = ordE L.k order h) (st : L.St) (j : Fin L.k) :
    L.Sm.w st j = some (L.pnt st (ordE L.k order h j)) := by
  show some (L.pnt st (L.e j)) = _
  rw [he]

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.ordE_coords
#print axioms OnBytes.Tie.Pv.Lay.eDefault_val
#print axioms OnBytes.Tie.Pv.Lay.eRange_coords
#print axioms OnBytes.Tie.Pv.Lay.prod_point

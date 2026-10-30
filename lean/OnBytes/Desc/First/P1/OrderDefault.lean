-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/OrderDefault.lean: at the order in which most layers of a product tree are
summed (`orderDefault`, OnBytes/Model/Frame.lean), round number j of a layer has coordinate number
j of the point. Statements and proofs.

  `levelWs_default`: if the point rho has mu coordinates, the weights of the layer's rounds are the
    equality weights at rho's coordinates, in their order.
  `getD_append_left`, `getD_append_right`: a member of two lists laid together.


-/
import OnBytes.Desc.First.P1.FlSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc

theorem rev_range_getD (l : List E) :
    ((List.range l.length).reverse.map fun v => l.getD (l.length - 1 - v) zeroE) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have e : l.length - 1 - (l.length - 1 - i) = i := by omega
    simp [e, h2]

theorem array_getD_toList (a : Array E) (j : Nat) : a.getD j zeroE = a.toList.getD j zeroE := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- At the default order the rounds' weights are the equality weights at the point's coordinates, in
their order. -/
theorem levelWs_default (mu : Nat) (rho : Array E) (h : rho.size = mu) :
    levelWs mu rho (orderDefault mu) =
      rho.toList.map fun z => OnBytes.Psc.Weight.equality z 3 := by
  have hl : rho.toList.length = mu := h
  have e := rev_range_getD rho.toList
  rw [hl] at e
  unfold levelWs orderDefault
  conv_rhs => rw [← e]
  rw [List.map_map]
  refine List.map_congr_left fun v _ => ?_
  show OnBytes.Psc.Weight.equality (rho.getD (mu - 1 - v) zeroE) 3 =
    OnBytes.Psc.Weight.equality (rho.toList.getD (mu - 1 - v) zeroE) 3
  rw [array_getD_toList]

theorem getD_append_left {α : Type} (a b : List α) (d : α) (i : Nat) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {α : Type} (a b : List α) (d : α) (i : Nat) :
    (a ++ b).getD (a.length + i) d = b.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_replicate' {α : Type} (x d : α) (n i : Nat) (h : i < n) :
    (List.replicate n x).getD i d = x := by
  simp [List.getD_eq_getElem?_getD, h]

end OnBytes.Desc.First.P1

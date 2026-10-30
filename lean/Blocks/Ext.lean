-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Ext.lean: the multilinear extension of a vector, and of a vector of forms.

Vectors and points are functions on ℕ (`ext`, `extF`). A form is an affine function of entries
(`Form`, Blocks/Form.lean).

Also: the orders in which the rounds of a sumcheck over the variables 0, .., g - 1 may bind them
(`PL.vars`, `PL.rangeOrd`). Variable t belongs to coordinate t of a point, and coordinate 0 belongs
to the top bit of an index.

Notation: `PL`: a namespace; `structure PL` (Blocks/ProductBlock.lean): the parameters of a product
layer; `mu`, `rK`: natural numbers: in `rangeBits mu rK`, an index of mu bits whose lowest rK bits
are the number of a tree; `g`: a natural number: there are g variables (`PL.vars g`).
-/
import Blocks.EqN
import Blocks.Form

set_option autoImplicit false

namespace Blocks

open Finset Prob

section Ext

variable {E : Type} [Field E]

/-- The multilinear extension of the vector v of length 2^g at the point pt (its first g
coordinates). -/
def ext (g : ℕ) (v : ℕ → E) (pt : ℕ → E) : E := ∑ X ∈ range (2 ^ g), eqN g 0 pt X * v X

theorem ext_congr {g : ℕ} {v w : ℕ → E} (h : ∀ X < 2 ^ g, v X = w X) (pt : ℕ → E) :
    ext g v pt = ext g w pt :=
  sum_congr rfl fun X hX => by rw [h X (mem_range.mp hX)]

theorem ext_add (g : ℕ) (v w : ℕ → E) (pt : ℕ → E) :
    ext g (fun X => v X + w X) pt = ext g v pt + ext g w pt := by
  unfold ext
  rw [← sum_add_distrib]
  exact sum_congr rfl fun X _ => by ring

theorem ext_sub (g : ℕ) (v w : ℕ → E) (pt : ℕ → E) :
    ext g (fun X => v X - w X) pt = ext g v pt - ext g w pt := by
  unfold ext
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun X _ => by ring

theorem ext_smul (g : ℕ) (c : E) (v : ℕ → E) (pt : ℕ → E) :
    ext g (fun X => c * v X) pt = c * ext g v pt := by
  unfold ext
  rw [mul_sum]
  exact sum_congr rfl fun X _ => by ring

theorem ext_sum {J : Type} (s : Finset J) (g : ℕ) (v : J → ℕ → E) (pt : ℕ → E) :
    ext g (fun X => ∑ j ∈ s, v j X) pt = ∑ j ∈ s, ext g (v j) pt := by
  unfold ext
  rw [sum_comm]
  exact sum_congr rfl fun X _ => mul_sum _ _ _

theorem ext_const (g : ℕ) (c : E) (pt : ℕ → E) : ext g (fun _ => c) pt = c := by
  unfold ext
  rw [← sum_mul]
  have h : ∑ X ∈ range (2 ^ g), eqN g 0 pt X = 1 := by
    simp only [eqN_eq]
    exact Alg.sum_eqN _
  rw [h, one_mul]

theorem ext_zero_of_forall {g : ℕ} {v : ℕ → E} (h : ∀ X < 2 ^ g, v X = 0) (pt : ℕ → E) :
    ext g v pt = 0 :=
  sum_eq_zero fun X hX => by rw [h X (mem_range.mp hX), mul_zero]

/-- Multilinear identity: the extension of a vector that is not zero vanishes at no more than g
|E|^(g - 1) points. -/
theorem cnt_ext_zero_le [Fintype E] (g : ℕ) (d : ℕ → E) (hd : ∃ X < 2 ^ g, d X ≠ 0) :
    cnt (fun p : Fin g → E => ext g d (nat p) = 0) ≤ g * Fintype.card E ^ (g - 1) :=
  cnt_eqN_zero_le g (2 ^ g) le_rfl d hd

/-- The extension of a vector of forms, as a form. -/
def extF {N : Type} (g : ℕ) (F : ℕ → Form N E) (pt : ℕ → E) : Form N E :=
  ∑ X ∈ range (2 ^ g), eqN g 0 pt X • F X

theorem val_extF {N : Type} [Fintype N] (y : N → E) (g : ℕ) (F : ℕ → Form N E) (pt : ℕ → E) :
    Form.val y (extF g F pt) = ext g (fun X => Form.val y (F X)) pt := by
  unfold extF ext
  simp only [map_sum, map_smul, smul_eq_mul]

end Ext

/-! ## Orders of the variables -/

namespace PL

/-- The variables 0, .., g - 1, in this order: the top bit of the index first. -/
def vars (g : ℕ) : List ℕ := (List.finRange g).map fun t : Fin g => (t : ℕ)

/-- The variables are the numbers below g. -/
theorem mem_vars {g v : ℕ} : v ∈ vars g ↔ v < g := by
  unfold vars
  rw [List.mem_map]
  exact ⟨fun ⟨t, _, ht⟩ => ht ▸ t.2, fun h => ⟨⟨v, h⟩, List.mem_finRange _, rfl⟩⟩

/-- No variable occurs twice. -/
theorem nodup_vars (g : ℕ) : (vars g).Nodup := (List.nodup_finRange g).map Fin.val_injective

/-- There are g variables. -/
theorem length_vars (g : ℕ) : (vars g).length = g := by
  unfold vars
  rw [List.length_map, List.length_finRange]

/-- The forest range order (forest, tree: Blocks/LookupRel.lean), as a list of bit positions of an
index of mu bits whose lowest rK bits are the number of a tree: rK + 2, rK + 1, rK, then rK + 5, rK
+ 4, rK + 3, then rK + 8, rK + 7, rK + 6, then mu - 1 down to rK + 9, then rK - 1 down to 0. For rK
= 0 it is the range order 2, 1, 0, 5, 4, 3, 8, 7, 6, mu - 1, .., 9. -/
def rangeBits (mu rK : ℕ) : List ℕ :=
  [rK + 2, rK + 1, rK, rK + 5, rK + 4, rK + 3, rK + 8, rK + 7, rK + 6] ++
    ((List.range (mu - (rK + 9))).map fun j => mu - 1 - j) ++
    ((List.range rK).map fun j => rK - 1 - j)

/-- The forest range order, as a list of variables: the bit position v is the variable (the
coordinate) mu - 1 - v. -/
def rangeOrd (mu rK : ℕ) : List ℕ := (rangeBits mu rK).map fun v => mu - 1 - v

/-- `rangeOrd` names every variable once, if there are at least nine bits above the number of the
tree. -/
theorem rangeOrd_perm {mu rK : ℕ} (h : rK + 9 ≤ mu) : (rangeOrd mu rK).Perm (vars mu) := by
  have hlen : (rangeOrd mu rK).length = mu := by
    simp only [rangeOrd, rangeBits, List.length_map, List.length_append, List.length_range,
      List.length_cons, List.length_nil]
    omega
  have hsub : vars mu ⊆ rangeOrd mu rK := fun t ht => by
    have ht' : t < mu := mem_vars.mp ht
    refine List.mem_map.mpr ⟨mu - 1 - t, ?_, by omega⟩
    unfold rangeBits
    by_cases h1 : mu - 1 - t < rK
    · exact List.mem_append_right
        _ (List.mem_map.mpr ⟨rK - 1 - (mu - 1 - t), List.mem_range.mpr (by omega), by omega⟩)
    · refine List.mem_append_left _ ?_
      by_cases h2 : mu - 1 - t < rK + 9
      · refine List.mem_append_left _ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega
      · exact List.mem_append_right
          _ (List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), by omega⟩)
  exact ((List.subperm_of_subset (nodup_vars mu) hsub).perm_of_length_le
    (by rw [hlen, length_vars])).symm

end PL

end Blocks

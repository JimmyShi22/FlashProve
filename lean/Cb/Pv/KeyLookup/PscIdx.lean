-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/PscIdx.lean: a numbering of the names of a hiding polynomial's coefficients in which
the constant stands first in the last variable's group; and how a sum over names picks one name.

It imports PscCf.lean and the library alone.

The library's names `PIdx l` have the constant's name last. The program orders the coefficients by
variable, then by degree upwards; the last variable also has a constant, which stands first in that
variable's group (OnBytes/Iop/Psc.lean: `hidingEntries`, `hidingWalk`).
Main names:
  `Cf.portIdx l i`   the number of the name i in that order, counted from 0.
  `portIdx_lt`       it is below 1 + Σ (degrees), the number of names.
  `portIdx_inj`      different names have different numbers.
  `Cf.nSum_zero`, `Cf.nSum_pick`   if the places w of the names are apart, the sum of h i' over the
                     names i' with w i' = w i is h i.
Limits: no term of the program is called here: that this is the program's order is not shown in this
file.

-/
import Cb.Pv.KeyLookup.PscCf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Cf
open Iop Hiop Prob Cb Finset

section
variable {E : Type}

/-- The number of a name: by variable, degrees upwards; the constant first in the last group. -/
def portIdx : (l : List (PFmt E)) → PIdx l → ℕ
  | [], _ => 0
  | [_], .inl t => 1 + (t : ℕ)
  | [_], .inr _ => 0
  | _ :: _ :: _, .inl t => (t : ℕ)
  | f :: g :: l, .inr i => f.n + portIdx (g :: l) i

theorem portIdx_lt : ∀ (l : List (PFmt E)) (i : PIdx l),
    portIdx l i < 1 + (l.map fun f => f.n).sum
  | [], _ => by simp [portIdx]
  | [f], .inl t => by
    have := t.2
    show 1 + (t : ℕ) < 1 + ([f].map fun f => f.n).sum
    simp
  | [f], .inr _ => by simp [portIdx]
  | f :: g :: l, .inl t => by
    have := t.2
    simp [portIdx]
    omega
  | f :: g :: l, .inr i => by
    have := portIdx_lt (g :: l) i
    simp [portIdx] at *
    omega

theorem portIdx_inj : ∀ (l : List (PFmt E)) (i j : PIdx l), portIdx l i = portIdx l j → i = j
  | [], _, _, _ => rfl
  | [f], .inl t, .inl t', h => by
    simp [portIdx] at h
    exact congrArg Sum.inl (Fin.ext h)
  | [f], .inl t, .inr _, h => by
    have h' : 1 + (t : ℕ) = 0 := h
    omega
  | [f], .inr _, .inl t, h => by
    have h' : 0 = 1 + (t : ℕ) := h
    omega
  | [f], .inr _, .inr _, _ => rfl
  | f :: g :: l, .inl t, .inl t', h => by
    simp [portIdx] at h
    exact congrArg Sum.inl (Fin.ext h)
  | f :: g :: l, .inl t, .inr i, h => by
    have := t.2
    simp [portIdx] at h
    omega
  | f :: g :: l, .inr i, .inl t, h => by
    have := t.2
    simp [portIdx] at h
    omega
  | f :: g :: l, .inr i, .inr j, h => by
    simp [portIdx] at h
    exact congrArg Sum.inr (portIdx_inj (g :: l) i j h)

end

section
variable {E : Type} [Field E]

theorem nSum_zero : ∀ (l : List (PFmt E)) (f : PIdx l → E), (∀ i, f i = 0) → nSum l f = 0
  | [], f, h => h ()
  | g :: l, f, h => by
    show (∑ t : Fin g.n, f (.inl t)) + nSum l (fun i => f (.inr i)) = 0
    rw [Finset.sum_eq_zero fun t _ => h (.inl t), nSum_zero l _ fun i => h (.inr i), add_zero]

theorem nSum_pick {J : Type} [DecidableEq J] : ∀ (l : List (PFmt E)) (w : PIdx l → J),
    Function.Injective w → ∀ (h : PIdx l → E) (i : PIdx l),
    nSum l (fun i' => if w i' = w i then h i' else 0) = h i
  | [], _, _, _, _ => if_pos rfl
  | g :: l, w, hw, h, .inl t => by
    show (∑ t' : Fin g.n, if w (.inl t') = w (.inl t) then h (.inl t') else 0) +
      nSum l (fun i' => if w (.inr i') = w (.inl t) then h (.inr i') else 0) = h (.inl t)
    rw [nSum_zero l _ fun i' => if_neg fun e => Sum.inr_ne_inl (hw e), add_zero,
      Finset.sum_eq_single t]
    · exact if_pos rfl
    · intro t' _ hne
      exact if_neg fun e => hne (Sum.inl.inj (hw e))
    · intro hn
      exact absurd (Finset.mem_univ t) hn
  | g :: l, w, hw, h, .inr i => by
    show (∑ t' : Fin g.n, if w (.inl t') = w (.inr i) then h (.inl t') else 0) +
      nSum l (fun i' => if w (.inr i') = w (.inr i) then h (.inr i') else 0) = h (.inr i)
    rw [Finset.sum_eq_zero fun t' _ => if_neg fun e => Sum.inl_ne_inr (hw e), zero_add]
    exact nSum_pick l (fun i' => w (.inr i')) (fun a b e => Sum.inr.inj (hw e))
      (fun i' => h (.inr i')) i

end
end Lk6.Cf

#print axioms Lk6.Cf.portIdx_lt
#print axioms Lk6.Cf.portIdx_inj
#print axioms Lk6.Cf.nSum_pick

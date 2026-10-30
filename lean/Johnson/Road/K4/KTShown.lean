-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/KTShown.lean: WHAT THE SECOND TOKEN SUMCHECK LEAVES (THE FORM KT OF A LAYERS'
SUB-PROOF), VALUED AT WHAT WAS SHOWN, IS THE TYPED `overTg`: THE LAST CLAIM OVER eps. Five theorems.
An identity between values: no draw, no count.

  `sumFrom_zero_in`: a sum along a list from a first number on is 0 if each member is 0 at the
    numbers that the list takes.
  `rowForm_shown`: in a world in which the slots of a sumcheck's hiding coefficients read 0 and the
    record's target is the start form's value: the form that the sumcheck leaves, asked for without
    the summand and without kept maps, is worth minus the record's last claim (from
    `Psc.rowForm_value`, OnBytes/Model/HideLaws.lean).
  `KT_shown`: so that form times k, where k times eps reads -1, is worth claim / eps.
  `overTg_eq`: where the typed summand's part in shown maps alone is 0, the typed public part
    `overTg` (Cb/Pv/Lay/At/Start.lean) of an output is its last claim over its eps.
  `over_KT`: the two joined: if the typed output's last claim and eps read the record's:
    `overTg Y o = KT.value ρ W`.

Limits. That the hiding slots read 0 at what was shown, that the target is the start's value there,
that the typed output's fields read the record's, and that the typed part in shown maps alone is 0
ARE PREMISES.
-/
import OnBytes.Model.HideLaws
import Cb.Pv.Lay.At.Start

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes.Model (Reading World Aff Psc sumFrom)
open Cb Cb.Pv.Lay.At

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

omit [Field K] in
/-- A sum along a list is 0 if each member is 0 at the numbers that the list takes. -/
theorem sumFrom_zero_in [CommRing K] {α : Type} (g : ℕ → α → K) : ∀ (l : List α) (s : ℕ),
    (∀ i x, s ≤ i → i < s + l.length → g i x = 0) → sumFrom g s l = 0
  | [], _, _ => rfl
  | x :: l, s, H => by
    simp only [sumFrom]
    rw [H s x (le_refl _) (by simp),
      sumFrom_zero_in g l (s + 1) (fun i y h1 h2 =>
        H i y (by omega) (by simp only [List.length_cons]; omega)), add_zero]

/-- The form that a sumcheck leaves, at what was shown. -/
theorem rowForm_shown (p : Psc)
    (h0 : ∀ j, p.first ≤ j → j < p.first + p.walk.1.length → W.slot j = 0)
    (ht : ρ.val p.target = p.start.value ρ W) :
    (p.rowForm zeroE {}).value ρ W = -ρ.val p.claim := by
  rw [Psc.rowForm_value, sumFrom_zero_in _ _ _ (fun i x h1 h2 => by rw [h0 i h1 h2, mul_zero]),
    ht, Aff.value_empty, ρ.zero]
  ring

/-- **KT at what was shown.** -/
theorem KT_shown (p : Psc) (k : E) (hk : ρ.val k * ρ.val p.eps = -1)
    (h0 : ∀ j, p.first ≤ j → j < p.first + p.walk.1.length → W.slot j = 0)
    (ht : ρ.val p.target = p.start.value ρ W) :
    ((p.rowForm zeroE {}).scale k).value ρ W = ρ.val p.claim / ρ.val p.eps := by
  have he : ρ.val p.eps ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    exact one_ne_zero (neg_eq_zero.mp hk.symm)
  rw [Aff.value_scale, rowForm_shown ρ W p h0 ht, eq_div_iff he]
  linear_combination (-(ρ.val p.claim)) * hk

/-- The typed public part, where the part in shown maps alone is 0. -/
theorem overTg_eq (Y : PscPar K) (o : Y.Out)
    (hS : Y.S0 o.st (Y.hp o.st o.pt) o.vals = 0) : overTg Y o = o.fin / o.eps := by
  unfold overTg
  rw [hS, sub_zero]

/-- **The typed public part of what the terms' sumcheck leaves is KT's value at what was shown.** -/
theorem over_KT (Y : PscPar K) (o : Y.Out) (p : Psc) (k : E) (KT : Aff)
    (hKT : KT = (p.rowForm zeroE {}).scale k) (hk : ρ.val k * ρ.val p.eps = -1)
    (h0 : ∀ j, p.first ≤ j → j < p.first + p.walk.1.length → W.slot j = 0)
    (ht : ρ.val p.target = p.start.value ρ W)
    (hS : Y.S0 o.st (Y.hp o.st o.pt) o.vals = 0) (hf : o.fin = ρ.val p.claim)
    (he : o.eps = ρ.val p.eps) : overTg Y o = KT.value ρ W := by
  rw [overTg_eq Y o hS, hKT, KT_shown ρ W p k hk h0 ht, hf, he]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.KT_shown
#print axioms OnBytes.Road.K4.over_KT

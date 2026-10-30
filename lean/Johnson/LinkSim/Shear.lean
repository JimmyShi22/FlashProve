-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/Shear.lean: a map that adds to each coordinate a value computed from earlier
coordinates alone is injective, and bijective when the families are finite. Statement and proof.
Pure algebra and order.
Terms of this folder: Johnson/LinkSim/Spec.lean.

The setting. The coordinates of a family c : Idx → G, with G an additive group, each have a rank, a
natural number. The shift s c i added at coordinate i may depend on c only at coordinates of lower
rank (Earlier). A translation is the case in which s does not depend on c.

What this file has.
  shear_injective   if s satisfies Earlier, then c ↦ c + s c is injective.
  shear_bijective   if moreover there are finitely many families, it is a bijection of the
                    families with themselves. shearEquiv is the same map as an equivalence.

How it fits. Under Johnson/LinkSim/ no file uses it.

Other names (namespace OnBytes.LinkSim).
  Earlier rk s         two families that agree at all coordinates of lower rank than i get the
                       same value of s at i.
  earlier_const        an example: a translation satisfies Earlier.
  not_injective_self   a negative test: where s may read the coordinate itself, the map need not be
                       injective. c ↦ c + (- c) sends every family to 0.

Note on sources. The library has a lemma of the same name and wider reach (Prob/Linear.lean: any
well-founded relation on the places, a family of commutative groups), of which shear_injective here
is a case where the group is commutative. This file does not import it.

Limits. Nothing on the inverse's form.
Terms: lean/GLOSSARY.md.

-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

namespace OnBytes.LinkSim

variable {Idx G : Type} [AddGroup G]

/-- The shift at coordinate i depends only on coordinates of lower rank. -/
def Earlier (rk : Idx → ℕ) (s : (Idx → G) → Idx → G) : Prop :=
  ∀ (c c' : Idx → G) (i : Idx), (∀ j, rk j < rk i → c j = c' j) → s c i = s c' i

/-- A shear c ↦ c + s c, with s satisfying Earlier, is injective. -/
theorem shear_injective (rk : Idx → ℕ) (s : (Idx → G) → Idx → G) (hs : Earlier rk s) :
    Function.Injective fun c : Idx → G => c + s c := by
  intro c c' h
  have key : ∀ (n : ℕ) (i : Idx), rk i = n → c i = c' i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have e : s c i = s c' i := hs c c' i fun j hj => ih (rk j) (hi ▸ hj) j rfl
      have hh : c i + s c i = c' i + s c' i := congrFun h i
      rw [e] at hh
      exact add_right_cancel hh
  exact funext fun i => key (rk i) i rfl

/-- With finitely many families, the shear is bijective. -/
theorem shear_bijective [Finite (Idx → G)] (rk : Idx → ℕ) (s : (Idx → G) → Idx → G)
    (hs : Earlier rk s) : Function.Bijective fun c : Idx → G => c + s c :=
  Finite.injective_iff_bijective.mp (shear_injective rk s hs)

/-- The shear as an equivalence. -/
noncomputable def shearEquiv [Finite (Idx → G)] (rk : Idx → ℕ) (s : (Idx → G) → Idx → G)
    (hs : Earlier rk s) : (Idx → G) ≃ (Idx → G) :=
  Equiv.ofBijective _ (shear_bijective rk s hs)

/-- shearEquiv maps c to c + s c. -/
theorem shearEquiv_apply [Finite (Idx → G)] (rk : Idx → ℕ) (s : (Idx → G) → Idx → G)
    (hs : Earlier rk s) (c : Idx → G) : shearEquiv rk s hs c = c + s c := rfl

/-- An example: a translation satisfies Earlier. -/
theorem earlier_const (rk : Idx → ℕ) (t : Idx → G) : Earlier rk fun _ => t := fun _ _ _ _ => rfl

/-- A negative test: what is added reads the coordinate itself. -/
theorem not_injective_self (i : Idx) {a b : G} (h : a ≠ b) :
    ¬ Function.Injective fun c : Idx → G => c + (fun c => -c) c := by
  intro hi
  have e : (fun _ : Idx => a) = fun _ => b :=
    hi (by
      show (fun _ : Idx => a) + -(fun _ : Idx => a) = (fun _ : Idx => b) + -(fun _ : Idx => b)
      rw [add_neg_cancel, add_neg_cancel])
  exact h (congrFun e i)

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.shear_injective
#print axioms OnBytes.LinkSim.shear_bijective
#print axioms OnBytes.LinkSim.not_injective_self

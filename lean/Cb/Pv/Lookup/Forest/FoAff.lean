-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Forest/FoAff.lean.
Affine forms on named places, as plain data.

The end claims of a sub-proof's lookup are affine in named values: cells of committed rows and
entries of the mask row. Some of these forms are made by the lookup itself, some are handed in by
its caller: for each call the form of the call's key vector at a point, and the forms on the planes
of counts. This file gives the one type in which such a form is written by the lookup and by its
caller.

Defines:
  AffK P K: a form: a list of (place, coefficient), and a constant. A place may stand twice.
  AffK.val f μ: its value under a reading μ of the places: the sum of coefficient times μ (place),
    plus the constant.
  AffK.ofConst, add, smul, sub, addMul: the operations that the Lean verifier under OnBytes/ has on
    its own forms (OnBytes.Model's Aff), on this type. That they agree with Aff's is not stated.
  extL f z: the multilinear extension of the vector f of 2^(length of z) entries at the point z, the
    top bit's coordinate first.
States: what val gives at each operation (val_ofConst, val_add, val_smul, val_sub, val_addMul).
Everything here is computable. K is any commutative ring.

-/
import Cb.Pv.Lookup.Out.TwV
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Fo
open TwV

/-- An affine form: (place, coefficient) pairs, and a constant. -/
abbrev AffK (P K : Type) : Type := List (P × K) × K

section
variable {P K : Type} [CommRing K]

namespace AffK

/-- The value of a form under a reading of the places. -/
def val (f : AffK P K) (μ : P → K) : K := (f.1.map fun pc => pc.2 * μ pc.1).sum + f.2

/-- The constant form. -/
def ofConst (c : K) : AffK P K := ([], c)

/-- The sum of two forms. -/
def add (f g : AffK P K) : AffK P K := (f.1 ++ g.1, f.2 + g.2)

/-- A form times a scalar. -/
def smul (a : K) (f : AffK P K) : AffK P K := (scale a f.1, a * f.2)

/-- The difference of two forms. -/
def sub (f g : AffK P K) : AffK P K := add f (smul (-1) g)

/-- f + a g. -/
def addMul (f g : AffK P K) (a : K) : AffK P K := add f (smul a g)

theorem val_ofConst (c : K) (μ : P → K) : val (ofConst c : AffK P K) μ = c := by
  simp [val, ofConst]

theorem val_add (f g : AffK P K) (μ : P → K) : val (add f g) μ = val f μ + val g μ := by
  simp only [val, add, List.map_append, List.sum_append]
  ring

theorem val_smul (a : K) (f : AffK P K) (μ : P → K) : val (smul a f) μ = a * val f μ := by
  have h : ∀ l : List (P × K), ((scale a l).map fun pc => pc.2 * μ pc.1).sum = a *
      (l.map fun pc => pc.2 * μ pc.1).sum := by
    intro l
    induction l with
    | nil => simp [scale]
    | cons x l ih =>
      have e : scale a (x :: l) = (x.1, a * x.2) :: scale a l := rfl
      rw [e, List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
      ring
  simp only [val, smul, h]
  ring

theorem val_sub (f g : AffK P K) (μ : P → K) : val (sub f g) μ = val f μ - val g μ := by
  rw [sub, val_add, val_smul]
  ring

theorem val_addMul (f g : AffK P K) (a : K) (μ : P → K) : val (addMul f g a) μ = val f μ + a *
    val g μ := by
  rw [addMul, val_add, val_smul]

end AffK

/-- The multilinear extension of f at z, the top bit's coordinate first. (TwV.eqN takes the lowest
bit's coordinate first: hence the reverse.) -/
def extL (f : ℕ → K) (z : List K) : K := ((List.range (2 ^ z.length)).map fun i => eqN z.reverse i *
    f i).sum

end
end Fo

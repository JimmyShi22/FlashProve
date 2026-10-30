-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RelForm.lean: affine forms, as far as the blocks need them.

A form is an affine function of values of masked scalars and of entries of vectors, with
coefficients that the verifier computes; the value of a masked scalar is the scalar minus its pad.
(The entry that holds a pad is itself a form. So the value of a masked scalar is the value of a
form, `Forms.scalar`, if the constant form 1 has the value 1 (`Forms.OK`; `Forms.val_scalar`).)

A block (a single sub-protocol, Blocks/Block.lean) that works with forms needs little of them: they
can be added and multiplied by scalars, each has a value on every implicit part y of a statement,
the value is linear in the form, there is the constant form 1, and there is a form for each pad.
This file fixes just that (`Forms`); the forms of Blocks/Form.lean are the instance `Forms.ofForm`.
The verifier holds a form (an element of Fm: data); the value of the form depends on the implicit
part, which holds the pad vectors that were sent.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Pi
import Blocks.Form

set_option autoImplicit false

namespace Blocks

/-- A system of forms: the data. E is the field, Y the type of implicit parts, P the index set of
the pads. -/
structure Forms (E Y P : Type) [Field E] where
  Fm : Type
  [acg : AddCommGroup Fm]
  [mod : Module E Fm]
  /-- the value of a form on an implicit part -/
  val : Y → Fm →ₗ[E] E
  /-- the constant form 1 -/
  one : Fm
  /-- the entry of a pad vector that holds the pad p, as a form -/
  pad : P → Fm

attribute [instance] Forms.acg Forms.mod

namespace Forms

variable {E Y P : Type} [Field E] (𝔉 : Forms E Y P)

/-- The constant form 1 has the value 1. -/
def OK : Prop := ∀ y, 𝔉.val y 𝔉.one = 1

/-- The form of a masked scalar s with the pad p: the scalar minus the pad. -/
def scalar (s : E) (p : P) : 𝔉.Fm := s • 𝔉.one - 𝔉.pad p

theorem val_scalar (h : 𝔉.OK) (y : Y) (s : E) (p : P) :
    𝔉.val y (𝔉.scalar s p) = s - 𝔉.val y (𝔉.pad p) := by
  unfold scalar
  rw [map_sub, map_smul, h y, smul_eq_mul, mul_one]


/-- The forms that the protocols use (Blocks/Form.lean): a form is given by a constant term and a
coefficient for each entry n : N of the vectors and pad vectors that were sent. proj gives the
entries of the implicit part, and place says which entry holds a pad. -/
def ofForm {N : Type} [Fintype N] [DecidableEq N] (proj : Y → N → E) (place : P → N) :
    Forms E Y P where
  Fm := Form N E
  val := fun y => Form.val (proj y)
  one := Form.const 1
  pad := fun p => Form.ent (place p)

theorem ofForm_ok {N : Type} [Fintype N] [DecidableEq N] (proj : Y → N → E) (place : P → N) :
    (ofForm proj place).OK :=
  fun y => Form.val_const (proj y) 1

/-- The form of a masked scalar is that of Blocks/Form.lean. -/
theorem ofForm_scalar {N : Type} [Fintype N] [DecidableEq N] (proj : Y → N → E)
    (place : P → N) (s : E) (p : P) :
    (ofForm proj place).scalar s p = Form.masked s (place p) := by
  show s • Form.const (1 : E) - Form.ent (place p) = Form.const s - Form.ent (place p)
  congr 1
  funext o
  cases o <;> simp [Form.const]

end Forms

end Blocks

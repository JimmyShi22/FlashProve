-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Course/LocRel.lean: relations on what the verifier program holds at a link of a proof
file's first chain, for any type A of the link's local values. Definitions and one rule.

No soundness: a test. This module serves a tool that runs, step by step, the verifier program of
OnBytes/Iop, OnBytes/Model and OnBytes/Proof (written by hand after the C++ source); it states
nothing on soundness.

Johnson/Top/H/Course/LayPlaces.lean has these definitions at the local values of a layers' link
(LayRel, LayRel.comp, LayRel.still, relRow). The links of the other kinds hold other local values.
Here the type of the local values is a letter A; at A := LayLoc the four definitions unfold to those
of LayPlaces.lean.

Main names:
  LocRel A: a relation between two states: local values and the context of the blocks.
  LocRel.comp: two relations behind each other. LocRel.still: nothing happens.
  LocRel.comp_of: two relations behind each other, from the two.
  locRow Rh R n: a first relation Rh and then the relations R 0 to R n behind each other.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course
open OnBytes

/-- A relation between two states of a link: local values and the context of the blocks. -/
abbrev LocRel (A : Type) : Type := A → Ctx → A → Ctx → Prop

/-- Two relations behind each other. -/
def LocRel.comp {A : Type} (R Q : LocRel A) : LocRel A :=
  fun a x a'' x'' => ∃ a' x', R a x a' x' ∧ Q a' x' a'' x''

/-- Two relations behind each other, from the two. -/
theorem LocRel.comp_of {A : Type} {R Q : LocRel A} {a a' a'' : A} {x x' x'' : Ctx}
    (h : R a x a' x') (h' : Q a' x' a'' x'') : LocRel.comp R Q a x a'' x'' := ⟨a', x', h, h'⟩

/-- Nothing happens. -/
def LocRel.still {A : Type} : LocRel A := fun a x a' x' => a' = a ∧ x' = x

/-- A first relation Rh and then the relations R 0 to R n behind each other. -/
def locRow {A : Type} (Rh : LocRel A) (R : Nat → LocRel A) : Nat → LocRel A
  | 0 => LocRel.comp Rh (R 0)
  | n + 1 => LocRel.comp (locRow Rh R n) (R (n + 1))

end KObj.Course

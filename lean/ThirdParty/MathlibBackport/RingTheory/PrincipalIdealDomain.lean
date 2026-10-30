/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Morenikeji Neri
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/RingTheory/PrincipalIdealDomain.lean, commit 5ed2965256430c3649e86755f9576b54eca72435
(v4.34.0), lines 232-247. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.PrincipalIdealDomain

variable {R : Type*}
open Finset

/-- A version of Bézout's lemma for greatest common divisors over arbitrary `Finset`s. -/
lemma Finset.gcd_eq_sum_mul {α : Type*} [CommRing R] [IsBezout R] [NormalizedGCDMonoid R]
    (s : Finset α) (f : α → R) :
    ∃ g : α → R, s.gcd f = ∑ a ∈ s, f a * g a := by classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨x, y, hxy⟩ := IsBezout.gcd_eq_sum (f a) (s.gcd f)
    obtain ⟨u, hu⟩ := IsBezout.associated_gcd_gcd R (x := f a) (y := s.gcd f)
    rw [← hxy, add_mul, mul_comm x, mul_comm y] at hu
    obtain ⟨g, hg⟩ := ih
    refine ⟨Function.update (g · * (y * u)) a (x * u), ?_⟩
    rw [gcd_insert, sum_insert ha, ← hu, hg]
    simp only [Function.update_self, add_right_inj, sum_mul, mul_assoc]
    exact sum_congr rfl fun b hb ↦ congrArg (f b * ·) <|
      (Function.update_of_ne (show b ≠ a by grind) (x * u) (g · * (y * u))).symm


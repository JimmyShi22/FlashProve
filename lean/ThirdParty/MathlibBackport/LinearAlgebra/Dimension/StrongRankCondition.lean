/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean, commit
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0), lines 557-559. Licence: Apache-2.0, see
ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

open Cardinal Submodule Function Set Module
variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [StrongRankCondition R]
variable {M' : Type*} [AddCommMonoid M'] [Module R M']

theorem LinearMap.finrank_le_finrank_of_surjective [Module.Finite R M] {f : M →ₗ[R] M'}
    (hf : Function.Surjective f) : Module.finrank R M' ≤ Module.finrank R M :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_surjective _ hf) (rank_lt_aleph0 _ _)


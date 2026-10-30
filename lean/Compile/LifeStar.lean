-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/LifeStar.lean: a uniform tuple is a uniform first entry and an independent uniform rest
(`unif_succ_bind`).
-/
import Compile.Spec
import Compile.Life

set_option autoImplicit false

noncomputable section

namespace Compile.Lifetime

open Prob Iop Rom
open scoped ENNReal

/-! ## Sampling a tuple one entry after the other -/

/-- A uniform tuple of n + 1 entries over a nonempty finite R is a uniform first entry and an
independent uniform tuple of n entries. -/
theorem unif_succ_bind {R γ : Type} [Fintype R] [Nonempty R]
    (n : ℕ) (F : (Fin (n + 1) → R) → PMF γ) :
    (unif (Fin (n + 1) → R)).bind F =
      (unif R).bind fun r => (unif (Fin n → R)).bind fun g => F (Fin.cons r g) := by
  rw [← map_unif_equiv (Fin.consEquiv fun _ => R), PMF.bind_map, unif_prod, bind_bind_eq_prod_bind]
  rfl

end Compile.Lifetime


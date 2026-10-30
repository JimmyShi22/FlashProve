-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LinkHVZK_rs.lean: a lemma on a function of uniform coins (`map_unif_two_rs`): see its
docstring. (Words of this library: lean/GLOSSARY.md.)
-/
import Blocks.PfrHVZK_rs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob

/-- Coins (γ, c), from nonempty finite types; a quantity s(γ) that is uniform; a quantity whose
distribution over c depends on s only. Then the distribution of any function of the two is known. -/
theorem map_unif_two_rs {Γ C Sg V Out : Type} [Fintype Γ] [Nonempty Γ] [Fintype C] [Nonempty C]
    [Fintype Sg] [Nonempty Sg] (s : Γ → Sg) (v : Γ → C → V) (Φ : Sg → V → Out) (K : Sg → PMF V)
    (h2 : (unif Γ).map s = unif Sg) (h3 : ∀ γ, (unif C).map (v γ) = K (s γ)) :
    (unif (Γ × C)).map (fun c => Φ (s c.1) (v c.1 c.2)) =
      (unif Sg).bind fun σ => (K σ).map fun b => Φ σ b := by
  rw [← h2, PMF.bind_map, map_unif_pair_eq_bind_rs]
  refine congrArg _ (funext fun γ => ?_)
  show _ = (K (s γ)).map fun b => Φ (s γ) b
  rw [← h3 γ, PMF.map_comp]
  rfl

end Blocks

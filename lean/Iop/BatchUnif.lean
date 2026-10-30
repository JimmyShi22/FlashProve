-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchUnif.lean: the challenges that one slot sees of a uniform ρ = (ρ_0, ρ_1, .., ρ_N) are
uniform (ρ_0: the challenges shared by all slots; ρ_j: those of slot j). (Words of this library:
lean/GLOSSARY.md.)

`BatchProtocol.Complete.prB` and the abort sets (`Honest.withheld`) are measured on the verifier randomness of
a slot's transcript (`Rho`); executions of a batch sample `BRho`; `prBRho_slot` shows that the two
measures agree.

Notation: `Kind` (Iop/Batch.lean): a round is called shared (`sh`) or local (`lo`) after its
verifier message; `k.All N C : Type` (there): the verifier message of the whole batch: "one uniform
string ρ_0" or "a tuple (ρ_1, .., ρ_N) of independent uniform strings"; `A : RoundSplits s` (there): the
annotation of a shape; `N : ℕ` (there, (D9)): the number of slots; `prRho S : ℝ≥0∞`
(Iop/InteractiveOracleProof.lean): the probability of a set of values of the verifier's randomness; `prBRho S : ℝ≥0∞`
(Iop/Batch.lean): the probability of a set of values of ρ = (ρ_0, ρ_1, .., ρ_N).
-/
import Iop.Batch
import Prob.Linear

namespace Iop
open Prob

theorem Kind.map_slot_unif {N : ℕ} {C : Type} [Fintype C] [Nonempty C] (j : Fin N) :
    ∀ k : Kind, (unif (k.All N C)).map (fun v => k.slot v j) = unif C
  | .sh => PMF.map_id _
  | .lo => map_eval_unif_pi (A := fun _ : Fin N => C) j

/-- One slot of a uniform ρ is uniform. -/
theorem BRho.map_slot_unif {N : ℕ} (j : Fin N) :
    ∀ (s : Shape) (A : RoundSplits s), (unif (BRho N s A)).map (BRho.slot j) = unif (Rho s)
  | [], _ => by
    have h : ∀ p : PMF Unit, p = PMF.pure () := fun p => by
      ext u
      have := p.tsum_coe
      rw [tsum_fintype] at this
      simpa using this
    exact (h _).trans (h _).symm
  | r :: s, (a, A) =>
    map_unif_prodMap (Ω₁ := a.kind.All N r.Chal) (Ω₂ := BRho N s A) (Y₁ := r.Chal)
      (Y₂ := Rho s) (fun v => a.kind.slot v j) (BRho.slot j)
      (Kind.map_slot_unif j a.kind) (BRho.map_slot_unif j s A)

/-- A set of values of slot j's randomness has the same probability on the whole ρ as on `Rho`. -/
theorem prBRho_slot {N : ℕ} (j : Fin N) {s : Shape} {A : RoundSplits s} (S : Set (Rho s)) :
    prBRho {ρ : BRho N s A | ρ.slot j ∈ S} = prRho S := by
  unfold prBRho prRho
  rw [← BRho.map_slot_unif j s A, pr_map]
  rfl

end Iop

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/PublicOne.lean: PUBLIC READINGS OFF ONE HASH FUNCTION, IN FRONT OF AN EXPERIMENT
OVER TYPED ORACLES THAT ARE CODED IN THAT HASH FUNCTION, the coding too hanging on the readings: the
bound at every fixed reading, over uniform typed oracles, holds over the uniform hash function.

By pub_le (Johnson/Prover/All/Public.lean) and Rom.Pr_overOne (Rom/Prefix.lean: the typed family
that is read out of a uniform hash function is uniform).

Main names.
  pub_overOne_le   THE STATEMENT.
  det_pub_overOne  without coins: the program's value at a hash function: the reading d there, and
    the typed program's value at the typed functions that the coding at d reads out of it.

Limits. A lemma on experiments. That the coded strings are no public strings is a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Public
import Rom.Prefix
import Run.DetOverOne

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open Rom Prob
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} {α D : Type}

/-- **Public readings off the hash function cost the typed experiment's bound nothing.** -/
theorem pub_overOne_le (Pub : OComp (rom lam) D) (m : D → OracleCoding S lam) (Y : D → OComp S α)
    (Pt : List Bool → Prop) (hP : Pub.AsksIn fun _ s => Pt s)
    (hY : ∀ d, ((Y d).overOne (m d)).AsksIn fun _ s => ¬ Pt s) (E : D → Set α) {ε : ℝ≥0∞}
    (h : ∀ d, Rom.Pr (Y d) (fun _ => E d) ≤ ε) :
    Rom.Pr (Pub.bind fun d => ((Y d).overOne (m d)).bind fun a => .pure (d, a))
      (fun _ => {z | z.2 ∈ E z.1}) ≤ ε := by
  show PrFrom (Table.empty _) _ _ ≤ ε
  refine pub_le Pub (fun d => (Y d).overOne (m d)) (fun _ s => Pt s) hP hY _ E fun d => ?_
  show Rom.Pr ((Y d).overOne (m d)) (fun _ => E d) ≤ ε
  rw [Pr_overOne]
  exact h d

/-- Without coins: the value at a hash function. -/
theorem det_pub_overOne (Pub : OComp (rom lam) D) (m : D → OracleCoding S lam) (Y : D → OComp S α)
    (g : Fam (rom lam)) :
    (Pub.bind fun d => ((Y d).overOne (m d)).bind fun a => .pure (d, a)).det g =
      (Pub.det g, (Y (Pub.det g)).det (readBlocks (m (Pub.det g)) g)) := by
  rw [OComp.det_bind, OComp.det_bind, Rom.det_overOne]
  rfl

end OnBytes.Prover

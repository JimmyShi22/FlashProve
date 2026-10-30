-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/ProverSelf.lean: where a prover's sides are the lists' own, the lists'
prover is that prover. `Sides.prover` (Honest/Rule.lean) puts the prover's sides that are built from
the lists into a prover's three fields and leaves the others; so at a prover that has these prover's
sides already it changes nothing. One statement with its proof, by unfolding. General in the lists
of parts.

What it is for. The rules on the three chains' invariants speak of `G.prover H`; a prover that is
built by another function has its prover's sides put in by that function. This joins the two where
the prover's sides are the same lists.

Limits.
  * The three hypotheses are equations of lists of prover's sides: whoever supplies the lists of
    parts proves them.
  * Nothing on a run, a coin or a measure.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Rule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {W₀ Rc Tr X₀ X : Type}

/-- **Where a prover's sides are the lists' own, the lists' prover is that prover.** -/
theorem Sides.prover_self {Xi Ky : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    (h₁ : H.first = G.first.map fun L => ⟨L.place, L.row.map (·.1)⟩)
    (h₂ : H.shared = G.shared.map fun L => ⟨L.place, L.row.map (·.1)⟩)
    (h₃ : H.second = G.second.map fun L => ⟨L.place, L.row.map (·.1)⟩) : G.prover H = H := by
  unfold Sides.prover
  rw [← h₁, ← h₂, ← h₃]

end ProofFile.Honest

#print axioms ProofFile.Honest.Sides.prover_self

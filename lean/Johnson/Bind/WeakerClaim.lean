-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/WeakerClaim.lean: soundness after an honest commitment
(SoundAfterHonestCommitmentFor, VerifiableInference/MoreStatements.lean) for a claim gives the same
for every weaker claim, at the same error. One theorem, general in the argument system.
Why. Johnson/Bind/Cpp/SoundAtCommittedExact.lean goes from "meets the policy of exact match" to "is
the model's output".
Beside it: Johnson/Bind/RejectsAll.lean, the other general law on this form (a verifier that accepts
nothing meets it).
Limits. A law on events: the weaker claim's bad event lies in the stronger claim's. Nothing on any
argument system.

-/
import VerifiableInference.StatementsNonEmpty

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- **From a claim to a weaker one.** The bad event of the weaker claim lies in that of the
stronger.
-/
theorem SoundAfterHonestCommitmentFor.weaken {system : ArgumentSystem}
    {claim claim' : system.Weights → List Token → List Token → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (imp : ∀ weights prompt output, claim weights prompt output → claim' weights prompt output)
    (h : SoundAfterHonestCommitmentFor system claim ε) :
    SoundAfterHonestCommitmentFor system claim' ε := by
  intro weights committerQueries proverQueries hc prover hp
  refine le_trans (Prob_mono _ ?_) (h weights committerQueries proverQueries hc prover hp)
  rintro ⟨prompt, output, accepted⟩ ⟨ha, hn⟩
  exact ⟨ha, fun hcl => hn (imp weights prompt output hcl)⟩

end VerifiableInference

#print axioms VerifiableInference.SoundAfterHonestCommitmentFor.weaken

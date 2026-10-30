-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/RejectsAll.lean: A verifier that accepts nothing meets soundness after an honest
commitment, at every error. General in the argument system. One theorem, for the split by cases in
Johnson/Bind/Cpp/SoundAtCommitted.lean; it shows soundness of nothing. The other general law on this
form: Johnson/Bind/WeakerClaim.lean.

  **SoundAfterHonestCommitmentFor.of_rejects** (namespace VerifiableInference): where the verifier
    rejects at every hash function, commitment, prompt, output and proof,
    SoundAfterHonestCommitmentFor (VerifiableInference/MoreStatements.lean) holds for every claim
    and every error: the bad event asks an accept, so it is empty.
Limits. The statement is true for the poorest of reasons. Whoever calls it says so where the call
stands.
Sources. The proof of of_rejects has the design of a proof in VerifiableInference/Checks.lean, step
for step; the statement is another. The last two lines of the experiment in the proof's "show"
resemble lines of that file too. That "show" writes the probability as the proof of
SoundForWith.afterHonestCommitment (VerifiableInference/HonestCommitment.lean) does. The head of the
helper prob_bind_zero is, but for names, that of a lemma in Compile/DigestKeyBinding.lean. That
lemma is kin to VCV-io: lean/CREDITS.md has VCV-io's entry.
Terms: lean/TERMS.md, lean/GLOSSARY.md.







-/
import VerifiableInference.HonestCommitment

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference
open RandomizedAlgorithm

private theorem prob_bind_zero {α β : Type} (p : PMF α) (k : α → PMF β) (E : Set β)
    (h : ∀ a, ZKCP.prob (k a) E = 0) : ZKCP.prob (p.bind k) E = 0 := by
  rw [ZKCP.prob_bind]
  simp only [h]
  exact ZKCP.expect_const p 0

/-- **A verifier that accepts nothing meets soundness after an honest commitment**, for every claim,
at every error: the bad event is empty. -/
theorem SoundAfterHonestCommitmentFor.of_rejects (system : ArgumentSystem)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℕ → ℝ≥0∞)
    (rejects : ∀ (hash : Hash) (commitment : Commitment) (prompt output : List Token)
      (proof : system.Proof),
      (system.verify commitment prompt output proof).evaluate hash = false) :
    SoundAfterHonestCommitmentFor system claim ε := by
  classical
  intro weights committerQueries proverQueries _ prover _
  refine le_trans (le_of_eq (Prob_eq_zero _ _ fun hash => ?_)) (zero_le _)
  show ZKCP.prob ((system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized.bind fun commitment =>
        (prover commitment randomness).bind fun y =>
            (system.verify commitment y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (y.1, y.2.1, accepted)).run hash)
        {o : List Token × List Token × Bool | o.2.2 = true ∧ ¬ claim weights o.1 o.2.1} = 0
  rw [run_bind]
  refine prob_bind_zero _ _ _ fun randomness => ?_
  rw [run_bind]
  refine prob_bind_zero _ _ _ fun commitment => ?_
  rw [run_bind]
  refine prob_bind_zero _ _ _ fun y => ?_
  rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done, ZKCP.prob_pure,
    rejects]
  exact if_neg fun hm => Bool.false_ne_true hm.1

end VerifiableInference

#print axioms VerifiableInference.SoundAfterHonestCommitmentFor.of_rejects

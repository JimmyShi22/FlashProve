-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/SilentAndBlind.lean: What soundness after an honest commitment does not test, and what
it tests beside completeness. General in the argument system. Two tests of the form
SoundAfterHonestCommitmentFor (VerifiableInference/MoreStatements.lean).

Why. That form says: after the honest committer has committed to weights w, an accepted output meets
the claim at w. It bounds accepts alone. So a committer under whose commitments the verifier accepts
nothing meets it, whatever it does with the weights: as a statement on the committer the form is
one-sided. Teeth are shown below against a committer that is one algorithm at two weights, beside an
accept; that it has teeth only beside an accept is an argument, no theorem.

Main names (namespace Bind.Control).
  **`soundAfter_of_silent`**: the positive test. Let soundness for some claim hold with an
    extractor (SoundForWith). A committer that samples nothing, asks nothing and returns one
    constant, at which that extractor finds nothing in the empty log, meets the form for every
    claim, "never" among them: soundness then bounds every accept.
  **`one_le_of_blind_join`**: the conditional negative test. Let the committer be one algorithm at
    weights w and w', at all randomness. Take a request that does not meet the claim at w'. If the
    honest prover at w is rejected at it with probability at most α, and the form holds at the error
    ε, then 1 ≤ α + ε c p, where c bounds the committer's queries and p the honest prover's (ε c p
    is the error ε at the two numbers: no product). The cheating prover at w' is the honest prover
    at w.
  `one_le_of_blind_join_complete`: the same with completeness for the claim in the library's own
    letter (CompleteFor, Ladder.lean): a committer that is one algorithm at two weights cannot meet
    the form and completeness together, at small errors, if some request parts the two weights.
  Tools: `run_then_verify`.
Limits. Tests alone. The first shows soundness of nothing: it is true for a poor reason, and is
stated to show that reason. The second refutes nothing by itself: it takes an accept (hα) as a
premise, and no theorem of this library gives one at a committer of Johnson/Bind/. Nothing on any
program.
Sources. The premise `hα` of `one_le_of_blind_join` (lines 134 to 139) has, token for token but for
the name of the weights, the text of the bound that ends the definition `Complete` in
VerifiableInference/Statements.lean (lines 183 to 189 there). The first test's proof also has the
frame of the proof of `SoundForWith.afterHonestCommitment`
(VerifiableInference/HonestCommitment.lean).
Terms: lean/GLOSSARY.md.








-/
import VerifiableInference.HonestCommitment
import VerifiableInference.ProbabilityGuards
import Ladder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory

namespace Bind.Control
open VerifiableInference VerifiableInference.RandomizedAlgorithm

/-- Under a hash function: an algorithm, then a deterministic one on its result, then a function of
both results. -/
theorem run_then_verify {γ β : Type} (first : RandomizedAlgorithm γ)
    (V : γ → DeterministicAlgorithm Bool) (f : γ → Bool → β) (hash : Hash) :
    (first.bind fun y => (V y).toRandomized.bind fun accepted =>
        RandomizedAlgorithm.done (f y accepted)).run hash =
      (first.run hash).bind fun y => PMF.pure (f y ((V y).evaluate hash)) := by
  rw [run_bind]
  refine congrArg _ (funext fun y => ?_)
  rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done]

/-- **THE POSITIVE TEST: a silent committer meets soundness after an honest commitment, for every
claim.** The committer samples nothing (hsample), asks nothing and returns the constant k (hcommit);
the extractor of a soundness statement finds nothing at k in the empty log (hE). Then that statement
bounds every accept after this committer, so the form holds whatever claim' is. -/
theorem soundAfter_of_silent {system : ArgumentSystem}
    {E : Commitment → QueryLog → Option system.Weights}
    {claim : system.Weights → List Token → List Token → Prop} {ε : ℕ → ℝ≥0∞}
    (sound : SoundForWith system E claim ε) {r₀ : system.CommitmentRandomness} {k : Commitment}
    (hsample : system.sampleCommitmentRandomness = .done r₀)
    (hcommit : ∀ w ρ, system.commit w ρ = .done k) (hE : E k [] = none)
    (claim' : system.Weights → List Token → List Token → Prop) :
    SoundAfterHonestCommitmentFor system claim' fun c p => ε (c + p) := by
  classical
  intro w c p _ prover hp
  have hS := sound c p Unit (.done (k, ())) trivial (fun _ => prover k r₀) fun _ => hp k r₀
  refine le_trans ?_ hS
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit w randomness).toRandomized.bind fun commitment =>
        (prover commitment randomness).bind fun y =>
            (system.verify commitment y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (y.1, y.2.1, accepted)).run hash)
        {o : List Token × List Token × Bool | o.2.2 = true ∧ ¬ claim' w o.1 o.2.1}
    ≤ ZKCP.prob (((prover k r₀).bind fun y =>
        (system.verify k y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (E k [], y.1, y.2.1, accepted)).run hash)
        {o : Option system.Weights × List Token × List Token × Bool |
          o.2.2.2 = true ∧ ¬ ∃ w, o.1 = some w ∧ claim w o.2.1 o.2.2.1}
  have eL : (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit w randomness).toRandomized.bind fun commitment =>
        (prover commitment randomness).bind fun y =>
            (system.verify commitment y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (y.1, y.2.1, accepted)).run hash =
      ((prover k r₀).run hash).bind fun y =>
        PMF.pure (y.1, y.2.1, (system.verify k y.1 y.2.1 y.2.2).evaluate hash) := by
    rw [run_bind, hsample, run_done, PMF.pure_bind, run_bind, hcommit,
      DeterministicAlgorithm.run_toRandomized, PMF.pure_bind]
    exact run_then_verify (prover k r₀) (fun y => system.verify k y.1 y.2.1 y.2.2)
      (fun y accepted => (y.1, y.2.1, accepted)) hash
  rw [eL, run_then_verify (prover k r₀) (fun y => system.verify k y.1 y.2.1 y.2.2)
    (fun y accepted => (E k [], y.1, y.2.1, accepted)) hash, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le fun hb => ⟨hb.1, fun hw => ?_⟩
  obtain ⟨w', e, -⟩ := hw
  have e' : E k [] = some w' := e
  rw [hE] at e'
  cases e'

/-- **THE CONDITIONAL NEGATIVE TEST: a committer that is one algorithm at two weights, beside an
accept.** At a request that does not meet the claim at w' (hn), let the honest prover at w be
rejected with probability at most α (hα), and let soundness after an honest commitment hold at ε
(hJ). Then 1 ≤ α + ε c p. The cheating prover at w' runs the honest prover at w: the commitment is
the same, so the verifier's answer is; "accepted" is the bad event at w', "rejected" the bad event
at w. -/
theorem one_le_of_blind_join {system : ArgumentSystem}
    {claim : system.Weights → List Token → List Token → Prop} {ε : ℕ → ℕ → ℝ≥0∞} {α : ℝ≥0∞}
    (hJ : SoundAfterHonestCommitmentFor system claim ε) {w w' : system.Weights}
    (hc : ∀ ρ, system.commit w ρ = system.commit w' ρ) (prompt output : List Token)
    (hn : ¬ claim w' prompt output)
    (hα : Prob (do
        let randomness ← system.sampleCommitmentRandomness
        let commitment ← (system.commit w randomness).toRandomized
        let proof ← system.prove w randomness prompt output
        (system.verify commitment prompt output proof).toRandomized)
      {accepted | accepted = false} ≤ α)
    {c p : ℕ}
    (hcq : (system.sampleCommitmentRandomness.bind fun ρ =>
      (system.commit w' ρ).toRandomized).QueryBound c)
    (hp : ∀ ρ, (system.prove w ρ prompt output).QueryBound p) : 1 ≤ α + ε c p := by
  classical
  have hS := hJ w' c p hcq
    (fun _ ρ => (system.prove w ρ prompt output).bind fun proof =>
      RandomizedAlgorithm.done (prompt, output, proof))
    (fun _ ρ => queryBound_map _ _ p (hp ρ))
  refine le_trans (le_of_eq (Prob_add_compl _ _).symm) (add_le_add hα (le_trans (le_of_eq ?_) hS))
  unfold Prob
  refine lintegral_congr fun hash => ?_
  show ZKCP.prob ((system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit w randomness).toRandomized.bind fun commitment =>
        (system.prove w randomness prompt output).bind fun proof =>
          (system.verify commitment prompt output proof).toRandomized).run hash)
        {accepted : Bool | accepted = false}ᶜ
    = ZKCP.prob ((system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit w' randomness).toRandomized.bind fun commitment =>
        ((system.prove w randomness prompt output).bind fun proof =>
          RandomizedAlgorithm.done (prompt, output, proof)).bind fun y =>
            (system.verify commitment y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (y.1, y.2.1, accepted)).run hash)
        {o : List Token × List Token × Bool | o.2.2 = true ∧ ¬ claim w' o.1 o.2.1}
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_congr _ fun ρ => ?_
  rw [run_bind, run_bind, DeterministicAlgorithm.run_toRandomized,
    DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, PMF.pure_bind, hc ρ, run_bind, run_bind,
    run_bind, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_congr _ fun proof => ?_
  rw [run_done, PMF.pure_bind, run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind,
    run_done, ZKCP.prob_pure, ZKCP.prob_pure]
  generalize
    (system.verify ((system.commit w' ρ).evaluate hash) prompt output proof).evaluate hash = v
  refine le_antisymm (ind_le fun h => ?_) (ind_le fun h => ?_)
  · have h' : ¬ v = false := h
    exact ⟨Bool.of_not_eq_false h', hn⟩
  · have h1 : v = true := h.1
    have h2 : ¬ v = false := by
      rw [h1]
      decide
    exact h2

/-- **A committer that is one algorithm at two weights cannot meet the form and completeness
together**, at small errors, if some request meets completeness' claim at the one and fails
soundness' claim at the other. The two claims may be one. -/
theorem one_le_of_blind_join_complete {system : ArgumentSystem}
    {claim served : system.Weights → List Token → List Token → Prop} {ε : ℕ → ℕ → ℝ≥0∞} {α : ℝ≥0∞}
    (hJ : SoundAfterHonestCommitmentFor system claim ε) (hC : VerifierAndGoals.CompleteFor system served α)
    {w w' : system.Weights} (hc : ∀ ρ, system.commit w ρ = system.commit w' ρ)
    (prompt output : List Token) (h1 : served w prompt output) (hn : ¬ claim w' prompt output)
    {c p : ℕ}
    (hcq : (system.sampleCommitmentRandomness.bind fun ρ =>
      (system.commit w' ρ).toRandomized).QueryBound c)
    (hp : ∀ ρ, (system.prove w ρ prompt output).QueryBound p) : 1 ≤ α + ε c p :=
  one_le_of_blind_join hJ hc prompt output hn (hC w prompt output h1) hcq hp

end Bind.Control

#print axioms Bind.Control.run_then_verify
#print axioms Bind.Control.soundAfter_of_silent
#print axioms Bind.Control.one_le_of_blind_join
#print axioms Bind.Control.one_le_of_blind_join_complete

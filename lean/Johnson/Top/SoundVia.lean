-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SoundVia.lean: a verifier that, at every hash function, accepts only where another
verifier accepts (at a proof that a fixed reader makes of its own, or under a named exception) has
that other's soundness at a larger error: ε (t + n) + δ t.

What this file states. Definitions and theorems with their proofs, in the terms of
VerifiableInference/Statements.lean. What it is for: the step from "the argument system of the
soundness theorem" to "the verifier that runs". Under the hypotheses below, soundness of the first
system is soundness of the second, at the first's error with n queries more plus the bound on the
exception's probability (ε (t + n) + δ t): a prover followed by the reader is again a prover.
  `ArgumentSystem.withVerifier`: the system with another type of proofs, another honest prover and
    another verifier; weights, model and committer stay.
  `soundForWith_via`, `soundForWithO_via`: the step, for `SoundForWith` and for `SoundForWithO`
    (Johnson/Top/SoundO.lean): the same extractor, the same claim.

Under which hypotheses. Let a second verifier, with proofs of a type of its own, be such that AT
EVERY HASH FUNCTION its yes at a commitment, a prompt, output tokens and a proof π gives the first
verifier's yes at THE SAME commitment, prompt and output tokens and at the proof that one fixed
reader makes of π; or an exception. The reader and the exception are algorithms over the hash
function, without coins; the reader asks at most n queries. The first system's soundness at ε and
`ExceptionBound exc δ` are hypotheses too.

What it does not show. The premise speaks of EVERY hash function: a linking statement that is proved
at one fixed function does not meet it. The reader makes the proof alone: commitment, prompt and
output tokens are handed on as they are. `ExceptionBound` speaks of an experiment of its own, in
which the reader does not run. No verifier is given here, and `ExceptionBound` is proved of no
exception in this file.

-/
import ZKCP.ManyOfOne
import Johnson.Top.SoundO

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

/-- The system with another type of proofs, another honest prover and another verifier. -/
def ArgumentSystem.withVerifier (system : ArgumentSystem) (Proof' : Type)
    (prove' : system.Weights → system.CommitmentRandomness → List Token → List Token →
      RandomizedAlgorithm Proof')
    (verify' : Commitment → List Token → List Token → Proof' → DeterministicAlgorithm Bool) :
    ArgumentSystem :=
  { system with Proof := Proof', prove := prove', verify := verify' }

/-- For every committer with at most `committerQueries` queries and every prover with at most
`proverQueries`: the exception, run on what they put out, says yes with probability at most
δ (committerQueries + proverQueries). -/
def ExceptionBound {Proof' : Type}
    (exc : Commitment → List Token → List Token → Proof' → DeterministicAlgorithm Bool)
    (δ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (committerQueries proverQueries : ℕ) (State : Type)
    (committer : RandomizedAlgorithm (Commitment × State)),
    committer.QueryBound committerQueries →
    ∀ prover : State → RandomizedAlgorithm (List Token × List Token × Proof'),
      (∀ state, (prover state).QueryBound proverQueries) →
      Prob (do
          let ((commitment, state), _) ← committer.withQueryLog
          let (prompt, output, proof) ← prover state
          (exc commitment prompt output proof).toRandomized)
        {excepted | excepted = true}
        ≤ δ (committerQueries + proverQueries)

/-- The queries of an algorithm followed by another add up. -/
theorem queryBound_bind_add {α β : Type} (rest : α → RandomizedAlgorithm β) (n : ℕ)
    (hr : ∀ a, (rest a).QueryBound n) (first : RandomizedAlgorithm α) (t : ℕ)
    (hf : first.QueryBound t) : (first.bind rest).QueryBound (t + n) := by
  refine (queryBound_toUpload _ _).mp ?_
  rw [toUpload_bind]
  exact ZKCP.OComp.QueryBound.bind _ n (fun a => (queryBound_toUpload _ n).mpr (hr a)) _ t
    ((queryBound_toUpload first t).mpr hf)

variable (system : ArgumentSystem) {Proof' : Type}
  (prove' : system.Weights → system.CommitmentRandomness → List Token → List Token →
    RandomizedAlgorithm Proof')
  (verify' : Commitment → List Token → List Token → Proof' → DeterministicAlgorithm Bool)
  (reader : List Token → List Token → Proof' → DeterministicAlgorithm system.Proof) (n : ℕ)
  (exc : Commitment → List Token → List Token → Proof' → DeterministicAlgorithm Bool)

/-- The step for `SoundForWith`. -/
theorem soundForWith_via
    (h : ∀ hash commitment prompt output proof,
      (verify' commitment prompt output proof).evaluate hash = true →
        system.accepts hash commitment prompt output
            ((reader prompt output proof).evaluate hash) = true ∨
          (exc commitment prompt output proof).evaluate hash = true)
    (hn : ∀ prompt output proof, (reader prompt output proof).toRandomized.QueryBound n)
    {extractor : Commitment → QueryLog → Option system.Weights}
    {claim : system.Weights → List Token → List Token → Prop} {ε δ : ℕ → ℝ≥0∞}
    (hs : SoundForWith system extractor claim ε) (hx : ExceptionBound exc δ) :
    SoundForWith (system.withVerifier Proof' prove' verify') extractor claim
      fun t => ε (t + n) + δ t := by
  classical
  intro tC tP St committer hC prover hP
  have b1 := hs tC (tP + n) St committer hC
    (fun state => (prover state).bind fun y => (reader y.1 y.2.1 y.2.2).toRandomized.bind fun π =>
      RandomizedAlgorithm.done (y.1, y.2.1, π))
    (fun state => queryBound_bind_add _ n
      (fun y => queryBound_map _ _ n (hn y.1 y.2.1 y.2.2)) (prover state) tP (hP state))
  have b2 := hx tC tP St committer hC prover hP
  rw [← Nat.add_assoc] at b1
  refine le_trans ?_ (add_le_add b1 b2)
  unfold Prob
  rw [← lintegral_add_left (measurable_eventProbability_run _ _)]
  refine lintegral_mono fun H => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (verify' c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run H) _
    ≤ ZKCP.prob ((committer.withQueryLog.bind fun c =>
        ((prover c.1.2).bind fun y => (reader y.1 y.2.1 y.2.2).toRandomized.bind fun π =>
          RandomizedAlgorithm.done (y.1, y.2.1, π)).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run H) _
      + ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (exc c.1.1 y.1 y.2.1 y.2.2).toRandomized).run H) _
  simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
    PMF.bind_bind]
  rw [ZKCP.prob_bind, ZKCP.prob_bind, ZKCP.prob_bind, ← ZKCP.expect_add]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.prob_bind, ZKCP.prob_bind, ZKCP.prob_bind, ← ZKCP.expect_add]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le_add ?_
  rintro ⟨hAccepted, hBad⟩
  rcases h H c.1.1 y.1 y.2.1 y.2.2 hAccepted with ha | he
  · exact Or.inl ⟨ha, hBad⟩
  · exact Or.inr he

/-- The step for `SoundForWithO`. -/
theorem soundForWithO_via
    (h : ∀ hash commitment prompt output proof,
      (verify' commitment prompt output proof).evaluate hash = true →
        system.accepts hash commitment prompt output
            ((reader prompt output proof).evaluate hash) = true ∨
          (exc commitment prompt output proof).evaluate hash = true)
    (hn : ∀ prompt output proof, (reader prompt output proof).toRandomized.QueryBound n)
    {extractor : Commitment → QueryLog → DeterministicAlgorithm (Option system.Weights)} {q : ℕ}
    {claim : system.Weights → List Token → List Token → Prop} {ε δ : ℕ → ℝ≥0∞}
    (hs : SoundForWithO system extractor q claim ε) (hx : ExceptionBound exc δ) :
    SoundForWithO (system.withVerifier Proof' prove' verify') extractor q claim
      fun t => ε (t + n) + δ t := by
  classical
  refine ⟨hs.1, ?_⟩
  intro tC tP St committer hC prover hP
  have b1 := hs.2 tC (tP + n) St committer hC
    (fun state => (prover state).bind fun y => (reader y.1 y.2.1 y.2.2).toRandomized.bind fun π =>
      RandomizedAlgorithm.done (y.1, y.2.1, π))
    (fun state => queryBound_bind_add _ n
      (fun y => queryBound_map _ _ n (hn y.1 y.2.1 y.2.2)) (prover state) tP (hP state))
  have b2 := hx tC tP St committer hC prover hP
  rw [← Nat.add_assoc] at b1
  refine le_trans ?_ (add_le_add b1 b2)
  unfold Prob
  rw [← lintegral_add_left (measurable_eventProbability_run _ _)]
  refine lintegral_mono fun H => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c =>
        (extractor c.1.1 c.2).toRandomized.bind fun s => (prover c.1.2).bind fun y =>
        (verify' c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (s, y.1, y.2.1, accepted)).run H) _
    ≤ ZKCP.prob ((committer.withQueryLog.bind fun c =>
        (extractor c.1.1 c.2).toRandomized.bind fun s =>
        ((prover c.1.2).bind fun y => (reader y.1 y.2.1 y.2.2).toRandomized.bind fun π =>
          RandomizedAlgorithm.done (y.1, y.2.1, π)).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (s, y.1, y.2.1, accepted)).run H) _
      + ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (exc c.1.1 y.1 y.2.1 y.2.2).toRandomized).run H) _
  simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
    PMF.bind_bind]
  rw [ZKCP.prob_bind, ZKCP.prob_bind, ZKCP.prob_bind, ← ZKCP.expect_add]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.prob_bind, ZKCP.prob_bind, ZKCP.prob_bind, ← ZKCP.expect_add]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le_add ?_
  rintro ⟨hAccepted, hBad⟩
  rcases h H c.1.1 y.1 y.2.1 y.2.2 hAccepted with ha | he
  · exact Or.inl ⟨ha, hBad⟩
  · exact Or.inr he

end VerifiableInference

#print axioms VerifiableInference.soundForWith_via
#print axioms VerifiableInference.soundForWithO_via

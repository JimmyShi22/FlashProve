-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/SoundBehind.lean: soundness behind every parser. If an argument system is sound, so is
the system whose proofs are of another type and whose verifier says yes only where the first
verifier says yes on what a parser makes of such a proof: whatever the parser is, with its queries
counted as the adversary's.

Why. A verifier takes a typed proof; what the prover's side hands over is a filled-in form, which a
parser turns into that typed proof. A statement on "a parser, then the verifier" should trust no
parser. Here it follows from the statement on the verifier alone, for all parsers at once.

States.
  `DeterministicAlgorithm.followedBy`, `evaluate_followedBy`: one algorithm, then another on its
    result; its value at a hash function.
  `soundForWith_behind`: from `SoundForWith system extractor claim ε`: the same extractor, the same
    claim, the error ε (t + n), for the system with proofs of the type Form and any verifier verify'
    that, at every hash function, says yes only where the first verifier says yes on what the parser
    returns there (hv); n bounds the parser's queries (hn).
  `sound_behind`: the same for `Sound` (VerifiableInference/Statements.lean).

Limits. One application of `soundForWith_via` (Johnson/Top/SoundVia.lean) at the exception that
never says yes. Two small things stand here under names of their own though the library has them, in
Johnson/Top/FrontGeneral.lean, a file with no program beneath it: that this exception has the bound
0 (`exceptionBound_never` there; here a private copy) and `followedBy`
(`DeterministicAlgorithm.andThen` there). This file does not import that one.
The parser sees the
prompt, the output tokens and the form, not the commitment. It has no coins. Nothing is said on
acceptance: a verifier that refuses everything meets hv, and the statement holds of it. The first
system's soundness is a hypothesis. For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.SoundVia

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- The exception that never says yes has the bound 0: the library's `exceptionBound_never` once
more (the head says why). -/
private theorem exceptionBound_neverHere {Form : Type} :
    ExceptionBound (fun (_ : Commitment) (_ _ : List Token) (_ : Form) =>
      (DeterministicAlgorithm.done false : DeterministicAlgorithm Bool)) fun _ => 0 := by
  intro tC tP St committer _ prover _
  refine le_of_eq ?_
  unfold Prob
  have z : ∀ H : Hash, ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun _ =>
      (DeterministicAlgorithm.done false : DeterministicAlgorithm Bool).toRandomized).run H)
      {excepted | excepted = true} = 0 := by
    intro H
    unfold ZKCP.prob
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro b hb hb'
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hb
    obtain ⟨_, -, _, -, rfl⟩ := hb
    exact Bool.false_ne_true hb'
  exact (MeasureTheory.lintegral_congr z).trans MeasureTheory.lintegral_zero

/-- Run one algorithm, then another on its result. (The text of `DeterministicAlgorithm.andThen`,
Johnson/Top/FrontParts.lean, under another name: the head says why.) -/
def DeterministicAlgorithm.followedBy {α β : Type} :
    DeterministicAlgorithm α → (α → DeterministicAlgorithm β) → DeterministicAlgorithm β
  | .done a, f => f a
  | .query s k, f => .query s fun d => (k d).followedBy f

theorem DeterministicAlgorithm.evaluate_followedBy {α β : Type} (g : Hash) :
    ∀ (a : DeterministicAlgorithm α) (f : α → DeterministicAlgorithm β),
      (a.followedBy f).evaluate g = (f (a.evaluate g)).evaluate g
  | .done _, _ => rfl
  | .query s k, f => evaluate_followedBy g (k (g s)) f

variable (system : ArgumentSystem) {Form : Type}
  (prove' : system.Weights → system.CommitmentRandomness → List Token → List Token →
    RandomizedAlgorithm Form)
  (verify' : Commitment → List Token → List Token → Form → DeterministicAlgorithm Bool)
  (parse : List Token → List Token → Form → DeterministicAlgorithm system.Proof) (n : ℕ)

/-- **Soundness behind every parser**, with the extractor and the claim named. -/
theorem soundForWith_behind
    (hv : ∀ hash commitment prompt output F,
      (verify' commitment prompt output F).evaluate hash = true →
        system.accepts hash commitment prompt output ((parse prompt output F).evaluate hash) = true)
    (hn : ∀ prompt output F, (parse prompt output F).toRandomized.QueryBound n)
    {extractor : Commitment → QueryLog → Option system.Weights}
    {claim : system.Weights → List Token → List Token → Prop} {ε : ℕ → ℝ≥0∞}
    (hs : SoundForWith system extractor claim ε) :
    SoundForWith (system.withVerifier Form prove' verify') extractor claim fun t => ε (t + n) := by
  have b := soundForWith_via system prove' verify' parse n
    (fun _ _ _ _ => DeterministicAlgorithm.done false)
    (fun hash c p o F h => Or.inl (hv hash c p o F h)) hn hs exceptionBound_neverHere
  simpa using b

/-- **The same for `Sound`.** -/
theorem sound_behind
    (hv : ∀ hash commitment prompt output F,
      (verify' commitment prompt output F).evaluate hash = true →
        system.accepts hash commitment prompt output ((parse prompt output F).evaluate hash) = true)
    (hn : ∀ prompt output F, (parse prompt output F).toRandomized.QueryBound n)
    {ε : ℕ → ℝ≥0∞} (hs : Sound system ε) :
    Sound (system.withVerifier Form prove' verify') fun t => ε (t + n) := by
  obtain ⟨extractor, h⟩ := hs
  exact ⟨extractor, soundForWith_behind system prove' verify' parse n hv hn
    (claim := system.IsModelOutput) h⟩

end VerifiableInference

#print axioms VerifiableInference.soundForWith_behind
#print axioms VerifiableInference.sound_behind

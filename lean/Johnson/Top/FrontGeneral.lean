-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontGeneral.lean: eight general declarations on the front of an argument system: its
verifier in the library's own terms, when that verifier says yes, two tools on deterministic
algorithms, the way out that never says yes, and the library's cost of the step behind a key's code.

"The front" is an argument system in the sense of VerifiableInference/Statements.lean
(`ArgumentSystem`): its verifier takes a commitment, a prompt, output tokens and a proof, and
queries one hash function. It is made from a scheme over one hash function in two steps. The
verifier's key goes behind a digest: a proof brings the key, and the verifier compares the hash of
the key's code `enc key` with the commitment (`ZKCP.Arg.digestKey`). The instance is built from the
prompt, the output tokens and further tokens that the proof brings (`ZKCP.Arg.buildInstance`).

Why this file. None of the eight names the Lean program `verify-on-bytes` or a tie to it. No file
under OnBytes/, Run/ or Fmt/ lies beneath this file, so that a statement on a front can call them
without importing either. More lies beneath than the first six import lines name: through
Johnson/Top/SoundVia.lean (for `ExceptionBound`) come the compiler's files, Iop/ and
Johnson/RecCompile/. Called in Johnson/Top/TieFront.lean, FrontOnlyLaws.lean, FrontParts.lean and
Johnson/TypedOracleCompiler/Top/OnFilesArmsCPlain.lean, and in what stands above these.

Main names.
  `VerifiableInference.DeterministicAlgorithm.andThen`, `evaluate_andThen`: run one algorithm, then
    another on its result; the evaluation of that.
  `VerifiableInference.exceptionBound_never`: the way out that never says yes has the price 0
    (`ExceptionBound`, Johnson/Top/SoundVia.lean).
  `OnBytes.K.evaluate_ofRom`: the front's evaluation of an algorithm over one oracle is its run
    (`.det`) at that hash function.
  `OnBytes.K.frontV`: the front's verifier, written with the library's own terms. It is what
    `ArgumentSystem.ofArgument` evaluates; the proved form of this is `frontV_is_verify`
    (Johnson/Top/TieOnFiles.lean [not in this library]).
  `OnBytes.K.front_yes`: if the instance is built, the key has a code, the hash of that code is
    the commitment, and the scheme's verifier over the one hash function says yes, then the front's
    verifier says yes.
  `OnBytes.K.front_yes_only`: the converse.
  `VerifiableInference.OnPublicFiles.epsCode`: the library's cost, (t + 2)² / 2^256, of the step from a
    scheme whose verifier holds the key to the scheme whose verifier holds the hash function's
    answer at the key's code, at the library's extractor (`extCodeC`,
    Johnson/TypedOracleCompiler/Top/OnFilesArmsCPlain.lean).

Limits. The scheme G, `enc`, `build`, `bound` and `π₀` are letters: nothing is said of any scheme or
code. Where `enc` returns none at every key, the front's verifier refuses every proof. So too where
`build` returns none everywhere. The front's verifier reads neither `bound` nor `π₀`: the committer
and the honest prover do. `.det` and `deterministicOf` take every draw as 0. `front_yes` and
`front_yes_only` speak of one hash function at a time. `epsCode` is a definition: that the step
costs so much is a theorem of other files, under their hypotheses. The docstring of `front_yes_only`
names Johnson/Top/TieFront.lean as the place of `front_yes`: it stands above it in this file.
Nothing on soundness of any system. For proofs only; no program imports this file.


-/
import ZKCP.SpecialAny
import ZKCP.DigestKey
import ZKCP.BuildInstance
import ZKCP.CoinsFirstArg
import VerifiableInference.Deterministic
import Rom.Bridge
import Johnson.Top.SoundVia

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal
open MeasureTheory

/-! ### two tools on deterministic algorithms -/

namespace VerifiableInference

/-- Run one algorithm, then another on its result. -/
def DeterministicAlgorithm.andThen {α β : Type} :
    DeterministicAlgorithm α → (α → DeterministicAlgorithm β) → DeterministicAlgorithm β
  | .done a, f => f a
  | .query s k, f => .query s fun d => (k d).andThen f

theorem DeterministicAlgorithm.evaluate_andThen {α β : Type} (g : Hash) :
    ∀ (a : DeterministicAlgorithm α) (f : α → DeterministicAlgorithm β),
      (a.andThen f).evaluate g = (f (a.evaluate g)).evaluate g
  | .done _, _ => rfl
  | .query s k, f => evaluate_andThen g (k (g s)) f

end VerifiableInference

/-! ### the way out that never says yes -/

namespace VerifiableInference

open RandomizedAlgorithm

/-- The way out that never says yes has the price 0. -/
theorem exceptionBound_never {Proof' : Type} :
    ExceptionBound (fun _ _ _ (_ : Proof') => DeterministicAlgorithm.done false) fun _ => 0 := by
  intro tC tP St committer _ prover _
  have h0 : ∀ H : Hash, eventProbability ((committer.withQueryLog.bind fun c =>
      (prover c.1.2).bind fun _ =>
        (DeterministicAlgorithm.done false : DeterministicAlgorithm Bool).toRandomized).run H)
      {excepted | excepted = true} = 0 := by
    intro H
    unfold eventProbability
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro e he ht
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at he
    obtain ⟨_, _, _, _, he'⟩ := he
    rw [he'] at ht
    exact Bool.false_ne_true ht
  refine le_of_eq ?_
  unfold Prob
  exact (lintegral_congr h0).trans lintegral_zero

end VerifiableInference

/-! ### the front's verifier, and when it says yes -/

namespace OnBytes.K

open Rom
open VerifiableInference (Token Hash deterministicOf)

/-- The front's evaluation of an algorithm over one oracle is its run at that hash function. -/
theorem evaluate_ofRom {α : Type} (hash : Hash) : ∀ c : Rom.OComp (rom 256) α,
    (deterministicOf (ofRom c)).evaluate hash = c.det fun _ => hash
  | .pure _ => rfl
  | .query _ q k => evaluate_ofRom hash (k (hash q))
  | .sample _ k => evaluate_ofRom hash (k 0)

section General
variable {I X IVK ISK Pf : Type} (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
  (enc : IVK → Option ZKCP.Str) (bound : ℕ)
  (build : List Token × List Token → List Token → Option X) (π₀ : IVK × Pf)

/-- The front's verifier, in the library's own terms. -/
def frontV (commitment : ZKCP.Digest 256) (prompt output : List Token)
    (proof : List Token × (IVK × Pf)) : VerifiableInference.DeterministicAlgorithm Bool :=
  deterministicOf
    (((((ZKCP.SpecialAny.oneOf G).digestKey enc).coinsFirst bound).buildInstance build
      (fun _ => []) π₀).V commitment (prompt, output) proof)

/-- If the instance is built, the key has a code whose hash is the commitment, and the scheme's
verifier says yes, then the front's verifier says yes. -/
theorem front_yes (hash : Hash) (commitment : ZKCP.Digest 256) (prompt output aux : List Token)
    (key : IVK) (π : Pf) (x : X) (code : ZKCP.Str) (hb : build (prompt, output) aux = some x)
    (hc : enc key = some code) (hd : hash code = commitment)
    (hv : (G.V key x π).det (fun _ => hash) = true) :
    (frontV G enc bound build π₀ commitment prompt output (aux, (key, π))).evaluate hash =
      true := by
  unfold frontV
  show (deterministicOf (match build (prompt, output) aux with
    | some x => ZKCP.verifyDigestKey (ZKCP.SpecialAny.oneOf G).V enc commitment x (key, π)
    | none => .pure false)).evaluate hash = true
  rw [hb]
  show (deterministicOf (match enc key with
    | some code => ZKCP.OComp.query code fun answer =>
        if answer = commitment then ofRom (G.V key x π) else .pure false
    | none => .pure false)).evaluate hash = true
  rw [hc]
  show (deterministicOf (if hash code = commitment then ofRom (G.V key x π)
    else .pure false)).evaluate hash = true
  rw [if_pos hd, evaluate_ofRom]
  exact hv

end General

section General
variable {I X IVK ISK Pf : Type} (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
  (enc : IVK → Option ZKCP.Str) (bound : ℕ)
  (build : List Token × List Token → List Token → Option X) (π₀ : IVK × Pf)

/-- The converse of `front_yes` (Johnson/Top/TieFront.lean): where the front's verifier says yes,
the instance is built, the key has a code whose hash is the commitment, and the scheme's verifier
says yes. -/
theorem front_yes_only (hash : Hash) (commitment : ZKCP.Digest 256) (prompt output aux : List Token)
    (key : IVK) (π : Pf)
    (h : (frontV G enc bound build π₀ commitment prompt output (aux, (key, π))).evaluate hash =
      true) :
    ∃ x code, build (prompt, output) aux = some x ∧ enc key = some code ∧
      hash code = commitment ∧ (G.V key x π).det (fun _ => hash) = true := by
  unfold frontV at h
  have h1 : (deterministicOf (match build (prompt, output) aux with
    | some x => ZKCP.verifyDigestKey (ZKCP.SpecialAny.oneOf G).V enc commitment x (key, π)
    | none => .pure false)).evaluate hash = true := h
  cases hb : build (prompt, output) aux with
  | none =>
    rw [hb] at h1
    exact absurd h1 Bool.false_ne_true
  | some x =>
    rw [hb] at h1
    have h2 : (deterministicOf (match enc key with
      | some code => ZKCP.OComp.query code fun answer =>
          if answer = commitment then ofRom (G.V key x π) else .pure false
      | none => .pure false)).evaluate hash = true := h1
    cases hc : enc key with
    | none =>
      rw [hc] at h2
      exact absurd h2 Bool.false_ne_true
    | some code =>
      rw [hc] at h2
      have h3 : (deterministicOf (if hash code = commitment then ofRom (G.V key x π)
        else .pure false)).evaluate hash = true := h2
      by_cases hd : hash code = commitment
      · rw [if_pos hd, evaluate_ofRom] at h3
        exact ⟨x, code, rfl, rfl, hd, h3⟩
      · rw [if_neg hd] at h3
        exact absurd h3 Bool.false_ne_true

end General

end OnBytes.K

/-! ### the cost of the step behind a key's code

The step: from index binding of a scheme whose verifier holds the key itself to index binding of the
scheme whose verifier holds the hash function's answer at the key's code, at the library's extractor
(`extCodeC`, `HoleArmsC.commitment_of_code`, Johnson/TypedOracleCompiler/Top/OnFilesArmsCPlain.lean). -/

namespace VerifiableInference.OnPublicFiles

/-- The library's cost of that step. -/
def epsCode : ℕ → ℝ≥0∞ := fun t => (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.DeterministicAlgorithm.evaluate_andThen
#print axioms VerifiableInference.exceptionBound_never
#print axioms OnBytes.K.evaluate_ofRom
#print axioms OnBytes.K.front_yes
#print axioms OnBytes.K.front_yes_only

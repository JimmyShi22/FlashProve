-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsInGameOne.lean: with placeholder provers, in index privacy's real experiment, against the
adversary that asks nothing and requests one batch, all three proofs are produced, except with
probability at most 71 · 2 ^ -256.

Summary. The three proofs are the session's proof, the first table's proof and the link proof of the
session's copy. As typed: for every session's proof in the view, that proof is produced, and with it
the other two; against this adversary the view has one session (`realExp_one`, E2E/GameOne.lean).
The environment names one fixed instance. At that adversary the experiment is the scheme's own run
(`pr_one_le`, E2E/GameOne.lean), so the bound of E2E/StringsAtScheme.lean
(`stringsAtScheme_description`) carries over. The provers are the placeholder provers, which send
each round's fixed message, and every search has at least 2 ^ 40 tries.

Main results.
  `oneInGame_description`: `OneInGame` holds at the verifier's parameters at Z, for every Z in
    scope. `OneInGame r` is the statement above for arbitrary r.

Terms: E2E/HidingTerms.lean.

Limits.
- One adversary, which asks no oracle query, one environment, which reads nothing of the view, and
  one request. Nothing is proved here about an adversary that asks a query, an instance that is
  named from the view, or a second request (why the bound that is used does not reach them: the
  header of E2E/StringsInGame.lean). For the key alone, against every adversary, see that file. For
  the sessions' proofs, against every adversary with a bound on its queries, see
  E2E/SessionsInGame.lean.
- The bound says that proofs are produced, not that the verifier accepts them: whether it accepts
  such a proof is proved at these parameters neither way.
- All limits of E2E/StringsAtScheme.lean hold, and the model (E2E/HidingTerms.lean).
- Nothing on completeness, on soundness or on what is hidden.

Definitions and helper lemmas.
  `oneInGame_of`: for arbitrary r.


-/
import E2E.GameOne
import E2E.StringsAtScheme

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Shown
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.WholeKey
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open AtPublicFiles.Premises (silentAtC)
open VerifierAndGoals (PublicFiles InScope)

/-- **For every session's proof in the view of the real experiment, against the one adversary: it is
produced, and with it the first table's proof and its copy's link proof.** -/
def OneInGame (r : InnerCompilerInput) : Prop :=
  ∀ (capT capL capB : ℕ → ℕ), (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) → ∀ (b : r.LeafBody) (M ℓ ℓr : ℕ) (i : r.Index) (x : r.Instance),
      Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r (silentAtC r b M ℓ ℓr capT capL capB).side) oneAdv
          (oneEnv x ()) i 1)
          (fun _ => {v | ¬ ∀ s ∈ v.sessions, ∀ y ∈ s, Strings (v.ivk, y.2)}) ≤
        71 * (2⁻¹ : ℝ≥0∞) ^ 256

theorem oneInGame_of (r : InnerCompilerInput) (h : StringsAtScheme r) : OneInGame r :=
  fun capT capL capB h1 h2 h3 b M ℓ ℓr i x =>
    (pr_one_le (wholeKeySchemeOverTypedOracles r (silentAtC r b M ℓ ℓr capT capL capB).side) i x ()
      fun k π => Strings (k, π)).trans (h capT capL capB h1 h2 h3 b M ℓ ℓr i x)

/-- **At the verifier's parameters at Z**, for every Z in scope. -/
theorem oneInGame_description (Z : PublicFiles) (scope : InScope Z = true)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    OneInGame ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  oneInGame_of _ (stringsAtScheme_description Z scope c m)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.oneInGame_of
#print axioms AtPublicFiles.Shown.oneInGame_description

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaAndStrings.lean: index privacy with its number, and that the proofs are produced, in one
statement for one choice of parameters, with the placeholder provers.

Summary. `PrivacyWithNumber` (E2E/ZetaAtCaps.lean) and `StringsAtScheme` (E2E/StringsAtScheme.lean)
speak about the same scheme only where their parameters agree. This file states both for the same r,
b and ℓr, one copy, ℓ := 320 and every search limit 2 ^ 40, so that the same scheme, `wholeKeySchemeOverTypedOracles r
(silentAtC r b 0 320 ℓr …).side`, appears in all three clauses. The main limit: the third clause is
about the scheme's own run, not about the first clause's experiment.

Main result.
  `numberAndStrings_description` (`NumberAndStrings r`): at the verifier's parameters at Z, for each
    fixed c and m, for public files Z in scope with a live description: the two clauses of
    `PrivacyWithNumber r`; and a third: for every index and instance the scheme's own committer and
    prover produce the proofs, except with probability at most 71 · 2 ^ -256.

Terms: E2E/HidingTerms.lean.

Limits.
- In the first clause's experiment the environment names the instance after the key and after the
  adversary's queries. In the third clause index and instance are fixed before the oracles are
  sampled, and nobody asks a query first. For the key's two proofs that does not matter: the key is
  made first. For the session's proof the third clause covers a fixed instance and an adversary that
  asks nothing before its request, and no more. For statements on that experiment see
  E2E/StringsInGameOne.lean (the adversary that asks nothing and requests one batch),
  E2E/StringsInGame.lean (the key's proofs, against every adversary) and E2E/SessionsInGame.lean
  (the sessions' proofs, against every adversary with a bound on its queries).
- Nothing on acceptance. What a produced proof opens of the committed tables is not stated here: see
  E2E/StringsHold.lean for any provers, and E2E/StringsHoldAtInput.lean, E2E/StringsHoldLink.lean
  and E2E/StringsHoldClosed.lean at these parameters. On a proof's plain messages, and on the
  openings of the prover's own oracle messages, these files say nothing.
- All limits of E2E/ZetaAtCaps.lean and E2E/StringsAtScheme.lean hold.

Definitions and helper lemmas.
  `numberAndStrings_of`: the statement for arbitrary r, from the two.


-/
import E2E.ZetaAtCaps
import E2E.StringsAtScheme

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Shown
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt Rom
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **The bound with its number, and that the proofs are produced, for one choice of parameters.**
-/
def NumberAndStrings (r : InnerCompilerInput) : Prop :=
  ∀ (b : r.LeafBody) (s1 ℓr : ℕ) (Ryes : r.Index → r.Instance → Prop) (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit)
    (i₀ : r.Index), 1 ≤ s1 → s1 ≤ 688127 → (∀ i x w, R.yes i x w → Ryes i x) →
    (ZKCP.Gen.PrivacyOn R
        (wholeKeySchemeOverTypedOracles r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                fun _ => 2 ^ 40).side) 1
        (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40)
                                              (fun _ => 2 ^ 40) fun _ => 2 ^ 40).side (fixedSims r.protocol) i₀ s1 (fun _ => True) Unit)
        (zetaW r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                              fun _ => 2 ^ 40) (coinNums r b 320 ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0)) (fun _ => True) ∧
      ∀ t, t ≤ 2 ^ 64 →
        zetaW r.queryLayout r.seedQueries r.compilerParameters (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                              fun _ => 2 ^ 40) (coinNums r b 320 ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) t 1 ≤
          (2⁻¹ : ℝ≥0∞) ^ 135) ∧
      ∀ (i : r.Index) (x : r.Instance),
        PrFrom (Table.empty _)
          (runScheme r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
            fun _ => 2 ^ 40).side i x) {z | ¬ AllStrings z} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256

theorem numberAndStrings_of (r : InnerCompilerInput) (h₁ : PrivacyWithNumber r) (h₂ : StringsAtScheme r) :
    NumberAndStrings r :=
  fun b s1 ℓr Ryes R i₀ a₁ a₂ hR => ⟨h₁ b s1 ℓr Ryes R i₀ a₁ a₂ hR, fun i x =>
    h₂ _ _ _ (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) b 0 320 ℓr
      i x⟩

/-- **At the verifier's parameters at Z**, for each fixed c and m, for public files Z in scope with
a live description. -/
theorem numberAndStrings_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    NumberAndStrings ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  numberAndStrings_of _ (privacyWithNumber_description Z scope live c m)
    (stringsAtScheme_description Z scope c m)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.numberAndStrings_of
#print axioms AtPublicFiles.Shown.numberAndStrings_description

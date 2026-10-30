-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsAtScheme.lean: the bound of E2E/StringsAtInput.lean, stated for the scheme's own
committer and prover.

Summary. E2E/StringsAtInput.lean bounds the probability that a proof is not produced in a program
`runOf`. This file proves that this program is the committer `(wholeKeySchemeOverTypedOracles r h).C` followed by the
prover `(wholeKeySchemeOverTypedOracles r h).P` (Johnson/WholeKey/AtInput.lean), the very scheme that `PrivacyFromFive`
(E2E/PrivacyAtDescription.lean) is about. So the bound is a statement on that scheme. The main
limit: it says that a proof is produced, not that the verifier accepts it.

Main results.
  `runScheme_eq`: an equation of programs: `runScheme r h i x` is `runOf r h i x` with the one proof
    put into a list.
  `stringsAtScheme_description` (`StringsAtScheme r`): `StringsAt` in these terms: at the verifier's
    parameters at Z, for each fixed c and m, for public files Z in scope: for the placeholder
    provers with at least 2 ^ 40 tries in every search, `AllStrings` holds for the scheme's own run,
    except with probability at most 71 · 2 ^ -256.

Terms: E2E/HidingTerms.lean.

Limits.
- All limits of E2E/StringsAtInput.lean hold: the provers are placeholders that send fixed messages
  · nothing on acceptance · one link proof · one commitment and one request · structured oracles,
  keys and proofs.

Definitions and helper lemmas.
  `runScheme r h i x`: the scheme's committer on the index i, then its prover on the batch of the
    one request x; it returns the key and the list of the batch's proofs.
  `AllStrings z`: for a key and a list of proofs: `Strings` holds for the key with each proof of the
    list.
  `pr_runScheme`: so the two events have the same probability, starting from every table of oracle
    answers.
  `stringsAtScheme_of`: the statement for arbitrary r, from `StringsAt r`.


-/
import E2E.StringsAtInput

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open AtPublicFiles.Premises (silentAtC)
open VerifierAndGoals (PublicFiles InScope)

/-- **The scheme's own run**: its committer, then its prover on the batch of one request. -/
def runScheme (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (i : r.Index) (x : r.Instance) :
    TypedOracleComputation 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits × List (RequestProof 256 r.protocol)) :=
  ((wholeKeySchemeOverTypedOracles r h).C i).bind fun key =>
    ((wholeKeySchemeOverTypedOracles r h).P key.2 [(x, ())]).bind fun πs => .pure (key.1, πs.val)

/-- **It is `runOf` with the one proof put into a list.** -/
theorem runScheme_eq (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (i : r.Index) (x : r.Instance) :
    runScheme r h i x = (runOf r h i x).bind fun y => .pure (y.1, [y.2]) := by
  show ((commitW r.queryLayout r.seedQueries r.answerCode h i).bind fun key =>
    ((coinsP r.queryLayout h).bind fun d => (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x d).bind fun π =>
      (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof 256 r.protocol) [(x, ())]))).bind fun πs =>
        .pure (key.1, πs.val)) =
    ((commitW r.queryLayout r.seedQueries r.answerCode h i).bind fun key => (coinsP r.queryLayout h).bind fun d =>
      (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x d).bind fun π => .pure (key.1, π)).bind fun y =>
        .pure (y.1, [y.2])
  simp only [OComp.bind_assoc]
  rfl

/-- `Strings` holds for the key with each proof of the list. -/
def AllStrings {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (z : FullKey lam L aT aL × List (RequestProof lam L)) : Prop :=
  ∀ π ∈ z.2, Strings (z.1, π)

/-- The two events have the same probability. -/
theorem pr_runScheme (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (i : r.Index) (x : r.Instance)
    (T : Table (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) :
    PrFrom T (runScheme r h i x) {z | ¬ AllStrings z} =
      PrFrom T (runOf r h i x) {y | ¬ Strings y} := by
  rw [runScheme_eq, PrFrom_bind_pure]
  refine congrArg _ (Set.ext fun y => ?_)
  show (¬ ∀ π ∈ [y.2], Strings (y.1, π)) ↔ ¬ Strings y
  rw [List.forall_mem_singleton]

/-- `StringsAt`, stated for the scheme's own committer and prover. -/
def StringsAtScheme (r : InnerCompilerInput) : Prop :=
  ∀ (capT capL capB : ℕ → ℕ), (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) → ∀ (b : r.LeafBody) (M ℓ ℓr : ℕ) (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (runScheme r (silentAtC r b M ℓ ℓr capT capL capB).side i x)
        {z | ¬ AllStrings z} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256

theorem stringsAtScheme_of (r : InnerCompilerInput) (h : StringsAt r) : StringsAtScheme r :=
  fun capT capL capB h1 h2 h3 b M ℓ ℓr i x =>
    le_of_eq_of_le (pr_runScheme r _ i x _) (h capT capL capB h1 h2 h3 b M ℓ ℓr i x)

/-- **At the verifier's parameters at Z**, for each fixed c and m, for public files Z in scope. -/
theorem stringsAtScheme_description (Z : PublicFiles) (scope : InScope Z = true)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    StringsAtScheme ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  stringsAtScheme_of _ (stringsAt_description Z scope c m)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.runScheme_eq
#print axioms AtPublicFiles.Shown.pr_runScheme
#print axioms AtPublicFiles.Shown.stringsAtScheme_of
#print axioms AtPublicFiles.Shown.stringsAtScheme_description

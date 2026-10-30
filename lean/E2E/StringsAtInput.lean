-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsAtInput.lean: with the placeholder provers, at the verifier's parameters, with at least
2 ^ 40 tries in every search, the scheme's three proofs are produced, except with probability at
most 71 · 2 ^ -256.

Summary. E2E/StringsShown.lean bounds the probability that a proof is not produced by an expression
in the parameters. This file evaluates that bound at the verifier's parameters at Z, for the
placeholder provers (`silentAtC`, E2E/FiveLeftSilentCaps.lean), with at least 2 ^ 40 tries in every
search. The main limit: it says that the proofs are produced. The placeholder provers send fixed
messages, and nothing here says that any verifier accepts them.

Main results.
  `stringsAt_description` (`StringsAt r`): at the verifier's parameters at Z, for each fixed c and
    m, for public files Z in scope: with at least 2 ^ 40 tries in every search, for every b, M, ℓ,
    ℓr, index and instance, `Strings` holds for the run `runOf`, except with probability at most
    71 · 2 ^ -256.
  `strings_silent`: for arbitrary r, under `LawFit` and `WiresFit`: with the placeholder provers and
    all their parameters arbitrary, `Strings` holds, except with probability at most `alphaAll r.queryLayout
    capT capL capB 0 0 0 0 0`.

How. `strings_law` (E2E/StringsShown.lean) · `alpha_of_tries`, `tries_built`
(E2E/ZetaTriesAtInput.lean) · `lawFit_fullD`, `wiresFit_fullD` (Johnson/Prover/At/FitAt.lean) ·
`Meaning.numbersFit_the` (Johnson/Prover/At/ToldAt.lean) · `VerifierAndGoals.ofBuilt`.

Terms: E2E/HidingTerms.lean.

Limits.
- All limits of E2E/StringsShown.lean hold: nothing on acceptance · one link proof, at the place
  that the prover samples (all M + 1: E2E/StringsAllLinks.lean) · one commitment and one request ·
  structured oracles, keys and proofs.
- Index and instance are fixed before the oracles are sampled, and nobody asks a query first. For
  the key's two proofs that does not matter: the key is made first. For the session's proof the
  statement covers a fixed instance and an adversary that asks nothing before its request, and no
  more: in the experiment of index privacy the environment names the instance after the key and
  after the adversary's queries. For statements on that experiment see E2E/StringsInGameOne.lean,
  E2E/StringsInGame.lean and E2E/SessionsInGame.lean.
- That a proof is produced does not say that it opens a column. What a produced proof opens of the
  committed tables is not stated here: see E2E/StringsHold.lean for any provers, and
  E2E/StringsHoldAtInput.lean, E2E/StringsHoldLink.lean and E2E/StringsHoldClosed.lean at these
  parameters. On a proof's plain messages, and on the openings of the prover's own oracle messages,
  these files say nothing. The statement asks only that Z is in scope. It also holds where the
  description is not live, and there the first table's proof and a session's proof open nothing
  (`holdNothing_description`, E2E/StringsHoldClosed.lean; the two verifiers read no column:
  `reads_filesAt_shut`, E2E/ReadsAtFiles.lean).
- There is no premise on ℓ: no verifier runs, so no length of a salt is asked for.
- Index and instance are arbitrary: no relation between them is asked for.

Definitions and helper lemmas.
  `neverStops_silent`: the placeholder provers never abort: both parts of each abort set are empty.
  `runOf r h i x`: the program: the scheme's committer with the provers h, then its prover of one
    request; it returns the key and the proof. That it is the scheme's own committer and prover,
    with the one proof taken out of its list, is an equation in E2E/StringsAtScheme.lean.
  `stringsAt_of`: `StringsAt r` from `Tries r`, `LawFit` for all search limits and `WiresFit`.
  `fits_built`: these two hold at the parameters of the value that the library builds, for every Z.


-/
import E2E.StringsShown
import E2E.FiveLeftSilentCaps
import E2E.ZetaTriesAtInput
import Johnson.Prover.At.ToldAt

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
open VerifiableInference.OnPublicFiles (InnerCompilerInput lawFit_fullD wiresFit_fullD)
open AtPublicFiles.Premises (silentAtC)
open AtPublicFiles.ZetaAt (Tries alpha_of_tries tries_built)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

/-- **The placeholder provers never abort.** -/
theorem neverStops_silent {I X : Type} (L : HolographicProtocol I X) (dc : Decs (silent L)) :
    NeverStops (Plays.ofRecs (silent L) dc) :=
  ⟨fun _ _ _ _ => @decide_eq_false _ (dc.T _ _ _) fun h => h.elim (fun a => a) fun a => a,
    fun _ _ _ _ => @decide_eq_false _ (dc.Lk _ _ _) fun h => h.elim (fun a => a) fun a => a,
    fun _ _ _ _ _ _ => @decide_eq_false _ (dc.B _ _ _) fun h => h.elim (fun a => a) fun a => a⟩

/-- **The program**: the committer, then the prover of one request; it returns the key and the
proof. -/
def runOf (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (i : r.Index) (x : r.Instance) :
    TypedOracleComputation 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits × RequestProof 256 r.protocol) :=
  (commitW r.queryLayout r.seedQueries r.answerCode h i).bind fun key =>
    (coinsP r.queryLayout h).bind fun d => (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x d).bind fun π => .pure (key.1, π)

/-- **With the placeholder provers, for arbitrary r.** -/
theorem strings_silent (r : InnerCompilerInput) (capT capL capB : ℕ → ℕ)
    (hL : LawFit r.queryLayout r.seedQueries capT capL capB) (hW : WiresFit r.queryLayout r.answerCode) (b : r.LeafBody) (M ℓ ℓr : ℕ) (i : r.Index)
    (x : r.Instance) :
    PrFrom (Table.empty _) (runOf r (silentAtC r b M ℓ ℓr capT capL capB).side i x)
      {y | ¬ Strings y} ≤ alphaAll r.queryLayout capT capL capB 0 0 0 0 0 :=
  strings_law r.queryLayout r.seedQueries r.answerCode r.fixedSample (silentAtC r b M ℓ ℓr capT capL capB).side hL hW
    (neverStops_silent r.protocol _) i x

/-- With at least 2 ^ 40 tries in every search, `Strings` fails with probability at most
71 · 2 ^ -256. -/
def StringsAt (r : InnerCompilerInput) : Prop :=
  ∀ (capT capL capB : ℕ → ℕ), (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) → ∀ (b : r.LeafBody) (M ℓ ℓr : ℕ) (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (runOf r (silentAtC r b M ℓ ℓr capT capL capB).side i x)
        {y | ¬ Strings y} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256

theorem stringsAt_of (r : InnerCompilerInput) (ht : Tries r)
    (hL : ∀ capT capL capB, LawFit r.queryLayout r.seedQueries capT capL capB) (hW : WiresFit r.queryLayout r.answerCode) :
    StringsAt r :=
  fun capT capL capB h1 h2 h3 b M ℓ ℓr i x =>
    (strings_silent r capT capL capB (hL capT capL capB) hW b M ℓ ℓr i x).trans
      (alpha_of_tries r ht capT capL capB h1 h2 h3)

/-- `LawFit`, for all search limits, and `WiresFit` hold at the parameters of the value that the
library builds. -/
theorem fits_built (Z : PublicFiles) (c : VerifiableInference.Digest)
    (m : (FlashProve.descriptionOfDataOnBytes flashProveData).More) :
    (∀ capT capL capB, LawFit ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).queryLayout
        ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).seedQueries capT capL capB) ∧
      WiresFit ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).queryLayout
        ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).answerCode :=
  ⟨fun capT capL capB => lawFit_fullD ((dataAtFiles flashProveData Z).inputFieldsAtReadings c m) (Meaning.numbersFit_the Z)
      (FlashProve.depth_pl0_tOf _ c m) (FlashProve.depth_pl1_tOf _ c m) capT capL capB,
    wiresFit_fullD ((dataAtFiles flashProveData Z).inputFieldsAtReadings c m) (Meaning.numbersFit_the Z)⟩

/-- **At the verifier's parameters at Z**, for each fixed c and m, for public files Z in scope. -/
theorem stringsAt_description (Z : PublicFiles) (scope : InScope Z = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      StringsAt ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), StringsAt (D.input Z c m))
    fun c m => stringsAt_of _ (tries_built Z scope c m) (fits_built Z c m).1 (fits_built Z c m).2

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.neverStops_silent
#print axioms AtPublicFiles.Shown.strings_silent
#print axioms AtPublicFiles.Shown.stringsAt_of
#print axioms AtPublicFiles.Shown.fits_built
#print axioms AtPublicFiles.Shown.stringsAt_description

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsOpen.lean: the scheme's three proofs are produced, and each opens a column of the index's
encoded table for the randomness that the committer has sampled, except with the probability that a
proof-of-work search runs out.

Summary. E2E/StringsShown.lean says that the proofs are produced. E2E/StringsHold.lean,
E2E/StringsHoldAtInput.lean and E2E/StringsHoldLink.lean say what a produced proof opens of the
committed tables. This file joins the two in one event and bounds its failure: for arbitrary
parameters, and then for the placeholder provers at the verifier's parameters. The main limit: it
says what is opened. It does not say that the verifier accepts it, and it says nothing on what a
column tells about the index.

Main results.
  `opens_law`: for arbitrary r and any provers that never abort, `Opens` holds, except with
    probability at most `alphaAll r.queryLayout capT capL capB 0 0 0 0 0`. Premises: `LawFit`, `WiresFit`, and
    that each verifier reads a column for all instances and verifier messages (`ReadsSome`,
    `ReadsLink`).
  `opensAt_description` (`OpensAt r`): at the verifier's parameters at Z, for each fixed c and m,
    for public files Z in scope with a live description: for the placeholder provers (`silentAtC`)
    with at least 2 ^ 40 tries in every search, `Opens` holds, except with probability at most
    71 · 2 ^ -256.
  `numberStringsColumns_description` (`NumberStringsColumns r`): under the same premises on Z, for
    the placeholder provers: the three clauses of `NumberAndStrings` (E2E/ZetaAndStrings.lean) and
    this one as a fourth, for one choice of parameters.
  `runOf_eq_coins`: an equation of programs: `runOf r h i x` is `runCoins r h i x` with the coins
    dropped.

Why the program returns its coins. An event on the key and the proof alone could only say "a column
of the table for some randomness", which says next to nothing. So the run is taken with the coins
that it has sampled, and the event names the committer's own randomness: `c.r` for the first table,
`e.r` for the copy at the sampled place.

Terms: E2E/HidingTerms.lean.

Limits.
- At least one column of each table named: how many, and which, is not stated here. At most how
  many: E2E/StringsHoldClosed.lean.
- Index and instance are fixed before the oracles are sampled, and nobody asks a query first:
  neither the third nor the fourth clause of `NumberStringsColumns` is about the first clause's
  experiment. For statements on that experiment, for the adversary that asks nothing and requests
  one batch, see E2E/StringsInGameOne.lean and E2E/StringsOpenInGame.lean.
- That the description is live is a premise of `opensAt_description`. Where it is not, the first
  table's proof and the session's proof open nothing (`key_nothing`, `session_nothing`,
  E2E/StringsHoldAtInput.lean).
- The salts and the paths are "some": they are not tied to the committer's trees here (`OpensOf`,
  E2E/StringsHold.lean, ties them).
- All limits of E2E/StringsAtInput.lean and E2E/ZetaAndStrings.lean hold: nothing on acceptance ·
  one link proof, at the sampled place · one commitment and one request.

Definitions and helper lemmas.
  `Out r h`, `runCoins r h i x`: the committer's coins, then the committer, the prover's coins, then
    the prover of one request; it returns both coins, the key and the proof.
  `Opens r h i z`: the first table's proof in the key is produced and opens, at some position, the
    symbol of `encodeIndex i c.r` there · the link proof at the sampled place is produced and opens one of
    `encodeIndex i c.r` and one of `encodeIndex i e.r` · the session's proof is produced and opens one of
    `encodeIndex i e.r`.
  `opens_of_not_ev`: pointwise in the oracle functions. `opens_fixed`: for fixed coins.
  `fits_description`: `LawFit` for all search limits and `WiresFit` at the verifier's parameters,
    for every Z.
  `opensAt_of`, `numberStringsColumns_of`: the two statements for arbitrary r, from their premises.


-/
import E2E.ZetaAndStrings
import E2E.StringsAllLinks
import E2E.StringsHoldLink

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey AtPublicFiles.Premises AtPublicFiles.ZetaAt
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed flashProveData)

variable (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)

/-- What the run with its coins returns. -/
abbrev Out : Type :=
  DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL × DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB ×
    FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits × RequestProof 256 r.protocol

/-- **The run, with the coins that it has sampled.** -/
def runCoins (i : r.Index) (x : r.Instance) : TypedOracleComputation 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Out r h) :=
  (coinsC r.queryLayout h).bind fun c => (commitAt r.queryLayout r.seedQueries r.answerCode h i c).bind fun key =>
    (coinsP r.queryLayout h).bind fun d => (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x d).bind fun π =>
      .pure (c, d, key.1, π)

/-- **`runOf` is that run with the coins dropped.** -/
theorem runOf_eq_coins (i : r.Index) (x : r.Instance) :
    runOf r h i x = (runCoins r h i x).bind fun z => .pure (z.2.2.1, z.2.2.2) := by
  show (((coinsC r.queryLayout h).bind fun c => commitAt r.queryLayout r.seedQueries r.answerCode h i c).bind fun key =>
      (coinsP r.queryLayout h).bind fun d => (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x d).bind fun π =>
        .pure (key.1, π)) =
    ((coinsC r.queryLayout h).bind fun c => (commitAt r.queryLayout r.seedQueries r.answerCode h i c).bind fun key =>
      (coinsP r.queryLayout h).bind fun d => (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x d).bind fun π =>
        (.pure (c, d, key.1, π) : TypedOracleComputation 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Out r h))).bind
      fun z => .pure (z.2.2.1, z.2.2.2)
  simp only [OComp.bind_assoc]
  rfl

/-- **The three proofs are produced, and each opens a column of the encoder's table of the index i
for the randomness that was sampled.** -/
def Opens (i : r.Index) (z : Out r h) : Prop :=
  (∃ π, z.2.2.1.piT = some π ∧ ∃ p sa pa, π.ext p = some ⟨r.protocol.encodeIndex i z.1.r p, sa, pa⟩) ∧
    ∃ e, z.1.copies[z.2.1.j]? = some e ∧
      (∃ l π, z.2.2.1.links[z.2.1.j]? = some l ∧ l.2.2 = some π ∧
        (∃ p sa pa, π.ext (Sum.inl p) = some ⟨r.protocol.encodeIndex i z.1.r p, sa, pa⟩) ∧
          ∃ p sa pa, π.ext (Sum.inr p) = some ⟨r.protocol.encodeIndex i e.r p, sa, pa⟩) ∧
      ∃ π, z.2.2.2.piB = some π ∧ ∃ p sa pa, π.ext p = some ⟨r.protocol.encodeIndex i e.r p, sa, pa⟩

variable {r h}

/-- **Pointwise**, outside the event for the five empty sets. -/
theorem opens_of_not_ev
    (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (hW : WiresFit r.queryLayout r.answerCode)
    (hs : NeverStops h.st) (hR : ReadsSome r) (hK : ReadsLink r) (i : r.Index) (x : r.Instance)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (e : DrawCopy 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KL)
    (dP : DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB) (hj : c.copies[dP.j]? = some e)
    (hn : (allY r.queryLayout r.seedQueries r.answerCode r.fixedSample h.b₀ h.st.joint h.capT h.capL h.capB
      (i, c.r, cutS (2 ^ r.queryLayout.depth) c.s) x (drawOf r.queryLayout h c e dP)).det g ∉ EvY (noBads r.protocol)) :
    Opens r h i (c, dP, ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).1,
      (proveAt r.queryLayout r.answerCode r.fixedSample h ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).2 x dP).det g) := by
  obtain ⟨sT, -, sB⟩ := strings_of_not_ev r.queryLayout r.seedQueries r.answerCode r.fixedSample h g hW hs i x c e dP hj hn
  obtain ⟨l, hl, sL⟩ := link_of_not_ev r.queryLayout r.seedQueries r.answerCode r.fixedSample h g hW hs i x c e dP hj hn
  obtain ⟨πT, hT⟩ := Option.isSome_iff_exists.1 sT
  obtain ⟨πL, hLk⟩ := Option.isSome_iff_exists.1 sL
  obtain ⟨πB, hB⟩ := Option.isSome_iff_exists.1 sB
  exact ⟨⟨πT, hT, key_column r h g hR i c πT hT⟩, e, hj,
    ⟨l, πL, hl, hLk, link_columns r h g hK i c dP.j e hj l hl πL hLk⟩,
    πB, hB, session_column r h g hR i x c e dP hj πB hB⟩

/-- **For fixed coins.** -/
theorem opens_fixed (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB) (hW : WiresFit r.queryLayout r.answerCode)
    (hs : NeverStops h.st) (hR : ReadsSome r) (hK : ReadsLink r) (i : r.Index) (x : r.Instance)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (dP : DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB)
    (hj : dP.j < c.copies.length) :
    PrFrom (Table.empty _) ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).bind fun key =>
      (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x dP).bind fun π =>
        (.pure (c, dP, key.1, π) : TypedOracleComputation 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Out r h)))
      {z | ¬ Opens r h i z} ≤ alphaAll r.queryLayout h.capT h.capL h.capB 0 0 0 0 0 := by
  have he : c.copies[dP.j]? = some c.copies[dP.j] := List.getElem?_eq_getElem hj
  refine (PrFrom_le_of_det (E' := EvY (noBads r.protocol)) ?_
    (noCoin_allY r.queryLayout r.seedQueries r.answerCode r.fixedSample h.b₀ h.st.joint h.capT h.capL h.capB
      (i, c.r, cutS (2 ^ r.queryLayout.depth) c.s) x (drawOf r.queryLayout h c c.copies[dP.j] dP)) _
    fun g hg => ?_).trans
    (allY_law r.answerCode r.fixedSample h.b₀ h.st.joint h.capT h.capL h.capB (freshAll_empty r.queryLayout r.seedQueries) hL
      (i, c.r, cutS (2 ^ r.queryLayout.depth) c.s) x (drawOf r.queryLayout h c c.copies[dP.j] dP) _
      (setsSmall_none r.queryLayout r.seedQueries))
  · exact (noCoin_commitAt r.queryLayout r.seedQueries r.answerCode h i c).bind fun key =>
      (noCoin_proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x dP).bind fun _ => trivial
  · by_contra hn
    have hy := opens_of_not_ev g hW hs hR hK i x c c.copies[dP.j] dP he hn
    have hg' : ¬ Opens r h i (OComp.det g _) := hg
    simp only [OComp.det_bind] at hg'
    exact hg' hy

/-- **The bound.** -/
theorem opens_law (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB) (hW : WiresFit r.queryLayout r.answerCode)
    (hs : NeverStops h.st) (hR : ReadsSome r) (hK : ReadsLink r) (i : r.Index) (x : r.Instance) :
    PrFrom (Table.empty _) (runCoins r h i x) {z | ¬ Opens r h i z} ≤
      alphaAll r.queryLayout h.capT h.capL h.capB 0 0 0 0 0 := by
  unfold runCoins
  refine PrFrom_coins_le _ _ _ (fun c hc => ?_) _ (onlyCoins_coinsC r.queryLayout h)
  refine PrFrom_bind_coins_le _ (commitAt r.queryLayout r.seedQueries r.answerCode h i c) _ _ (fun dP hdP => ?_) _
    (onlyCoins_coinsP r.queryLayout h)
  exact opens_fixed hL hW hs hR hK i x c dP (by rw [hc.2.2.1]; exact hdP.1)

/-- `LawFit`, for all search limits, and `WiresFit` hold at the verifier's parameters, for every Z.
-/
theorem fits_description (Z : PublicFiles) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      (∀ capT capL capB, LawFit ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).queryLayout
          ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).seedQueries capT capL capB) ∧
        WiresFit ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).queryLayout
          ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).answerCode :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More),
      (∀ capT capL capB, LawFit (D.input Z c m).queryLayout (D.input Z c m).seedQueries capT capL capB) ∧
        WiresFit (D.input Z c m).queryLayout (D.input Z c m).answerCode)
    fun c m => fits_built Z c m

variable (r)

/-- With at least 2 ^ 40 tries in every search, `Opens` fails with probability at most
71 · 2 ^ -256. -/
def OpensAt : Prop :=
  ∀ (capT capL capB : ℕ → ℕ), (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) → ∀ (b : r.LeafBody) (M ℓ ℓr : ℕ) (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (runCoins r (silentAtC r b M ℓ ℓr capT capL capB).side i x)
        {z | ¬ Opens r (silentAtC r b M ℓ ℓr capT capL capB).side i z} ≤
          71 * (2⁻¹ : ℝ≥0∞) ^ 256

theorem opensAt_of (ht : Tries r) (hL : ∀ capT capL capB, LawFit r.queryLayout r.seedQueries capT capL capB)
    (hW : WiresFit r.queryLayout r.answerCode) (hR : ReadsSome r) (hK : ReadsLink r) : OpensAt r :=
  fun capT capL capB h1 h2 h3 b M ℓ ℓr i x =>
    (opens_law (h := (silentAtC r b M ℓ ℓr capT capL capB).side) (hL capT capL capB) hW
      (neverStops_silent r.protocol _) hR hK i x).trans (alpha_of_tries r ht capT capL capB h1 h2 h3)

/-- **At the verifier's parameters at Z**, for each fixed c and m, for public files Z in scope with
a live description. -/
theorem opensAt_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    OpensAt ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  opensAt_of _ (tries_description Z scope c m) (fits_description Z c m).1 (fits_description Z c m).2
    (readsSome_description Z scope live c m) (readsLink_description Z c m)

/-- **The bound with its number · the proofs are produced · each opens a column: for one choice of
parameters.** -/
def NumberStringsColumns : Prop :=
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
      (∀ (i : r.Index) (x : r.Instance),
        PrFrom (Table.empty _)
          (runScheme r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
            fun _ => 2 ^ 40).side i x) {z | ¬ AllStrings z} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256) ∧
      ∀ (i : r.Index) (x : r.Instance),
        PrFrom (Table.empty _)
          (runCoins r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
            fun _ => 2 ^ 40).side i x)
          {z | ¬ Opens r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
            fun _ => 2 ^ 40).side i z} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256

theorem numberStringsColumns_of (h₁ : NumberAndStrings r) (h₂ : OpensAt r) :
    NumberStringsColumns r :=
  fun b s1 ℓr Ryes R i₀ a₁ a₂ hR =>
    ⟨(h₁ b s1 ℓr Ryes R i₀ a₁ a₂ hR).1, (h₁ b s1 ℓr Ryes R i₀ a₁ a₂ hR).2, fun i x =>
      h₂ _ _ _ (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) b 0 320 ℓr
        i x⟩

/-- **At the verifier's parameters at Z**, for each fixed c and m, for public files Z in scope with
a live description. -/
theorem numberStringsColumns_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    NumberStringsColumns ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  numberStringsColumns_of _ (numberAndStrings_description Z scope live c m)
    (opensAt_description Z scope live c m)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.runOf_eq_coins
#print axioms AtPublicFiles.Shown.opens_of_not_ev
#print axioms AtPublicFiles.Shown.opens_fixed
#print axioms AtPublicFiles.Shown.opens_law
#print axioms AtPublicFiles.Shown.fits_description
#print axioms AtPublicFiles.Shown.opensAt_of
#print axioms AtPublicFiles.Shown.opensAt_description
#print axioms AtPublicFiles.Shown.numberStringsColumns_of
#print axioms AtPublicFiles.Shown.numberStringsColumns_description

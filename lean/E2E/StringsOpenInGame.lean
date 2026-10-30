-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsOpenInGame.lean

What this file has. allAtOnce_description collects eight statements to one purpose: by its clauses 5
and 8, index privacy with placeholder provers is not about views that lack proofs. The eight are
stated for one choice of parameters, on the hashed scheme with three placeholder provers that send
fixed messages. The first two are index privacy with the simulator simWholeKey; E2E/HidingTerms.lean
says what the simulator is given. For these placeholder provers its error is at most 2 ^ -135 (one
request, 2 ^ 64 oracle queries), and by clauses 5 and 8 proofs are produced under the same search
limits. Of the other six, clauses 3 and 4 are about the scheme's own run, 6 and 7 about one
adversary that asks no query, and 5 and 8 about every adversary. Clauses 3, 5, 6 and 8 say that
proofs are produced; 4 and 7 that each opens at least one position of the index's encoded tables.
Clause 8's bound includes the error of index privacy itself, so it is of that size, not near
2 ^ -256. The proofs are placeholder provers': fixed messages, nonces, and opened columns of the
index's encoded tables.

Where this stands (in full: E2E/ZetaAtCaps.lean): the step through hashing is proved for any provers
that meet twenty premises, here with an error bound; all three provers here are placeholders.

The index: in the release's use, the model's weights (Terms: E2E/HidingTerms.lean).

Theorems.
  `allAtOnce_description` (`AllAtOnce r`): at the verifier's parameters at Z, for each fixed c and
    m, for public files Z in scope with a live description: with one copy, ℓ := 320 free bits in a
    leaf's salt and every search limit 2 ^ 40:
    1. `ZKCP.Gen.PrivacyOn` holds for the scheme, with the simulator `simWholeKey` and the error
    `zetaW`.
    2. For one request and at most 2 ^ 64 oracle queries, `zetaW` is at most the number given above.
    3. For every index and instance, in the scheme's own run (the committer, then the prover of one
    request), the first table's proof, the link proof at the place that the prover samples and the
    session's proof are produced, except with probability at most 71 · 2 ^ -256.
    4. In that run, taken with its coins, each of these three proofs opens at least one position of
    the index's encoded table (the link proof: one of the first table and one of the copy), except
    with probability at most 71 · 2 ^ -256.
    5. In the real experiment of index privacy (`ZKCP.Gen.realExp`), against every adversary and
    every environment, for any number of batches, the first table's proof and the link proof in the
    key are produced, except with probability at most 2 · 71 · 2 ^ -256.
    6. In that experiment, for the adversary that asks no query and requests one batch and the
    environment that names one fixed instance, every proof in the view is produced, and so are the
    first table's proof and its copy's link proof in the key, except with probability at most
    71 · 2 ^ -256.
    7. For the same adversary and environment, with the coins returned, the view holds one batch of
    one proof and clause 4 holds for it, except with probability at most 71 · 2 ^ -256.
    8. In that experiment, against every adversary with at most tV queries and every valid
    environment, for n ≤ s1 batches of at most one instance each, every session's proof is produced,
    except with probability at most n · 46 · 2 ^ -256 + `boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0 tV
    n`.
    Clauses 1 to 4 are `NumberStringsColumns` (E2E/StringsOpen.lean); 5 is `KeyInGame`
    (E2E/StringsInGame.lean), 6 `OneInGame` (E2E/StringsInGameOne.lean), 7 `OpensInGame`, 8
    `SessionsInGame` (E2E/SessionsInGame.lean).
  `opensInGame_description` (`OpensInGame r`): under the same premises on Z: clause 7 for every
    number of copies, every ℓ and at least 2 ^ 40 tries in every search.
  `opensView_law`: for arbitrary parameters r and any provers that never abort, under `LawFit`,
    `WiresFit`, `ReadsSome` and `ReadsLink`: clause 7's event holds, except with probability at most
    `alphaAll r.queryLayout capT capL capB 0 0 0 0 0`, the bound on the three searches' failures.
  `realExp_one_coins`, `realExp_one_drop`: two equations of programs. The library's real experiment,
    for the adversary and the environment of clause 6 (`oneAdv`, `oneEnv`, E2E/GameOne.lean), is the
    scheme's run with its coins (`runCoins`, E2E/StringsOpen.lean) followed by `viewOf`; and it is
    `gameCoins` with the coins dropped.

Why the coins are returned. A view holds no coin of the committer. An event on the view alone could
only say "a column of the table for some randomness", which says next to nothing. So the experiment
is taken together with the coins that it has sampled, and dropping them is proved to give back the
library's own experiment.

Limits, the weightiest first.
- The three provers are placeholders. They send each round's fixed message and no message of the
  protocol.
- The statements say what is opened. They do not say that the verifier accepts it, and they say
  nothing on what an opened column tells about the index.
- What the proofs open inside the real experiment is stated for one adversary (no query, one batch)
  and one environment (one fixed instance). Against an adversary that asks queries first, clause 8
  says that the sessions' proofs are produced, and clause 5 that the key's proofs are; neither says
  what they open.
- At least one position is opened; how many, and which, is not stated here (at most how many:
  E2E/StringsHoldClosed.lean).
- For clauses 1 and 2 all limits of E2E/ZetaAtCaps.lean hold; for the others those of
  E2E/StringsOpen.lean.

Tests and notes.
- The eight are not independent: clause 6 is proved from 3 and clause 7 from the bound behind 4.
- Clause 6 alone would hold of a view without sessions; clause 7 says that the view holds one batch
  of one proof.
- gameCoins is this folder's own program; realExp_one_drop ties it to the library's experiment.
- The clauses for every instance say nothing where the type of instances is empty; it has a member
  at these parameters (instance_nonempty_description, E2E/StringsInGame.lean).

Terms: E2E/HidingTerms.lean.

Helper lemmas without a docstring. All other definitions and lemmas have docstrings.
  `opensInGame_of`, `allAtOnce_of`: the two statements for arbitrary r, from their premises.


-/
import E2E.StringsOpen
import E2E.StringsInGame
import E2E.StringsInGameOne
import E2E.SessionsInGame

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
open FlashProve (protocolDataWellFormed)

variable (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)

/-- The type of the experiment's views. -/
abbrev ViewT : Type :=
  ZKCP.Gen.View (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance
    (RequestProof 256 r.protocol)

/-- The view that the experiment makes of a run with its coins. -/
def viewOf (x : r.Instance) (z : Out r h) : ViewT r :=
  ⟨z.2.2.1, [ZKCP.Gen.Batch.released [(x, (), true)] [z.2.2.2]], [], []⟩

/-- **The real experiment, for the adversary that asks no query and requests one batch, is the
scheme's run with its coins, followed by `viewOf`.** -/
theorem realExp_one_coins (i : r.Index) (x : r.Instance) :
    ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r h) oneAdv (oneEnv x ()) i 1 =
      (runCoins r h i x).bind fun z => .pure (viewOf r h x z) := by
  rw [realExp_one]
  show (((coinsC r.queryLayout h).bind fun c => commitAt r.queryLayout r.seedQueries r.answerCode h i c).bind fun key =>
      ((coinsP r.queryLayout h).bind fun d => (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x d).bind fun π =>
        (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof 256 r.protocol) [(x, ())]))).bind fun πs =>
          (.pure ⟨key.1, [ZKCP.Gen.Batch.released [(x, (), true)] πs.val], [], []⟩ :
            OComp _ (ViewT r))) =
    ((coinsC r.queryLayout h).bind fun c => (commitAt r.queryLayout r.seedQueries r.answerCode h i c).bind fun key =>
      (coinsP r.queryLayout h).bind fun d => (proveAt r.queryLayout r.answerCode r.fixedSample h key.2 x d).bind fun π =>
        (.pure (c, d, key.1, π) : TypedOracleComputation 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Out r h))).bind
      fun z => .pure (viewOf r h x z)
  simp only [OComp.bind_assoc]
  rfl

/-- What the experiment with its coins returns. -/
abbrev OutV : Type :=
  DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL × DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB × ViewT r

/-- **That experiment, with the coins that it has sampled.** -/
def gameCoins (i : r.Index) (x : r.Instance) : TypedOracleComputation 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (OutV r h) :=
  (runCoins r h i x).bind fun z => .pure (z.1, z.2.1, viewOf r h x z)

/-- **The library's experiment is that program with the coins dropped.** -/
theorem realExp_one_drop (i : r.Index) (x : r.Instance) :
    ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r h) oneAdv (oneEnv x ()) i 1 =
      (gameCoins r h i x).bind fun w => .pure w.2.2 := by
  rw [realExp_one_coins]
  unfold gameCoins
  simp only [OComp.bind_assoc]
  rfl

/-- **Of both coins and a view**: the view's sessions are one batch of one proof, for x, and `Opens`
holds of the coins, the view's key and that proof. -/
def OpensView (i : r.Index) (x : r.Instance) (w : OutV r h) : Prop :=
  ∃ π, w.2.2.sessions = [[(x, π)]] ∧ Opens r h i (w.1, w.2.1, w.2.2.ivk, π)

/-- It fails at most as often as `Opens` fails for the run with its coins. -/
theorem pr_gameCoins_le (i : r.Index) (x : r.Instance) :
    PrFrom (Table.empty _) (gameCoins r h i x) {w | ¬ OpensView r h i x w} ≤
      PrFrom (Table.empty _) (runCoins r h i x) {z | ¬ Opens r h i z} := by
  unfold gameCoins
  rw [PrFrom_bind_pure]
  exact PrFrom_mono _ _ fun z hz hO => hz ⟨z.2.2.2, rfl, hO⟩

variable {r h}

/-- **The bound, in the real experiment taken with its coins.** -/
theorem opensView_law (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB) (hW : WiresFit r.queryLayout r.answerCode)
    (hs : NeverStops h.st) (hR : ReadsSome r) (hK : ReadsLink r) (i : r.Index) (x : r.Instance) :
    PrFrom (Table.empty _) (gameCoins r h i x) {w | ¬ OpensView r h i x w} ≤
      alphaAll r.queryLayout h.capT h.capL h.capB 0 0 0 0 0 :=
  (pr_gameCoins_le r h i x).trans (opens_law hL hW hs hR hK i x)

variable (r)

/-- With at least 2 ^ 40 tries in every search, `OpensView` fails with probability at most
71 · 2 ^ -256. -/
def OpensInGame : Prop :=
  ∀ (capT capL capB : ℕ → ℕ), (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) → ∀ (b : r.LeafBody) (M ℓ ℓr : ℕ) (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (gameCoins r (silentAtC r b M ℓ ℓr capT capL capB).side i x)
        {w | ¬ OpensView r (silentAtC r b M ℓ ℓr capT capL capB).side i x w} ≤
          71 * (2⁻¹ : ℝ≥0∞) ^ 256

theorem opensInGame_of (h₀ : OpensAt r) : OpensInGame r :=
  fun capT capL capB h1 h2 h3 b M ℓ ℓr i x =>
    (pr_gameCoins_le r _ i x).trans (h₀ capT capL capB h1 h2 h3 b M ℓ ℓr i x)

/-- **At the verifier's parameters at Z**, for each fixed c and m, for public files Z in scope with
a live description. -/
theorem opensInGame_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    OpensInGame ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  opensInGame_of _ (opensAt_description Z scope live c m)

/-- **Eight clauses for one choice of parameters.** -/
def AllAtOnce : Prop :=
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
      (∀ (i : r.Index) (x : r.Instance),
        PrFrom (Table.empty _)
          (runCoins r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
            fun _ => 2 ^ 40).side i x)
          {z | ¬ Opens r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
            fun _ => 2 ^ 40).side i z} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256) ∧
      (∀ (i : r.Index)
          (Vt : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits → ZKCP.Gen.AdvVerifier
            (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Instance (RequestProof 256 r.protocol))
          (Ze : ZKCP.Gen.ViewEnv (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
            (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol)) (n : ℕ),
        Rom.Pr (ZKCP.Gen.realExp
            (wholeKeySchemeOverTypedOracles r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                    fun _ => 2 ^ 40).side) Vt Ze i n)
          (fun _ => {v | ¬ KeyFull (0 + 1) v.ivk}) ≤
            ((0 + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256)) ∧
      (∀ (i : r.Index) (x : r.Instance),
        Rom.Pr (ZKCP.Gen.realExp
            (wholeKeySchemeOverTypedOracles r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                    fun _ => 2 ^ 40).side) oneAdv (oneEnv x ()) i 1)
          (fun _ => {v | ¬ ∀ s ∈ v.sessions, ∀ y ∈ s, Strings (v.ivk, y.2)}) ≤
            71 * (2⁻¹ : ℝ≥0∞) ^ 256) ∧
      (∀ (i : r.Index) (x : r.Instance),
        PrFrom (Table.empty _)
          (gameCoins r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
            fun _ => 2 ^ 40).side i x)
          {w | ¬ OpensView r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
            fun _ => 2 ^ 40).side i x w} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256) ∧
      ∀ (i : r.Index)
          (Ze : ZKCP.Gen.ViewEnv (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
            (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol)),
        ZKCP.Gen.ViewEnv.IsValid R 1 Ze i → ∀ (tV : ℕ)
          (Vt : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits → ZKCP.Gen.AdvVerifier
            (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Instance (RequestProof 256 r.protocol)),
        (∀ ivk, (Vt ivk).QueryBound tV) → ∀ n, n ≤ s1 →
        Rom.Pr (ZKCP.Gen.realExp
            (wholeKeySchemeOverTypedOracles r (silentAtC r b 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
                                    fun _ => 2 ^ 40).side) Vt Ze i n)
          (fun _ => {v | BadView (fun π => π.piB = none) v}) ≤
            (n : ℝ≥0∞) * (46 * (2⁻¹ : ℝ≥0∞) ^ 256) + boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0 tV n

theorem allAtOnce_of (h₁ : NumberStringsColumns r) (h₂ : KeyInGame r) (h₃ : OneInGame r)
    (h₄ : OpensInGame r) (h₅ : SessionsInGame r) (hs : 320 ≤ r.compilerParameters.sMT) : AllAtOnce r :=
  fun b s1 ℓr Ryes R i₀ a₁ a₂ hR =>
    have e := h₁ b s1 ℓr Ryes R i₀ a₁ a₂ hR
    have c40 : ∀ _ : ℕ, 2 ^ 40 ≤ 2 ^ 40 + 1 := fun _ => Nat.le_succ _
    ⟨e.1, e.2.1, e.2.2,
      fun i Vt Ze n => h₂ _ _ _ c40 c40 c40 b 0 320 ℓr i Vt Ze n,
      fun i x => h₃ _ _ _ c40 c40 c40 b 0 320 ℓr i x,
      fun i x => h₄ _ _ _ c40 c40 c40 b 0 320 ℓr i x,
      fun i Ze hv tV Vt hq n hn =>
        h₅ b 0 s1 320 ℓr (2 ^ 40) (2 ^ 40) (2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
          (fun _ => 2 ^ 40) Ryes R (by norm_num) a₂ (by norm_num) hs (fun _ => le_rfl)
          (fun _ => le_rfl) (fun _ => le_rfl) c40 hR i Ze hv tV Vt hq n hn⟩

/-- **At the verifier's parameters at Z**, for each fixed c and m, for public files Z in scope with
a live description. -/
theorem allAtOnce_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    AllAtOnce ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  allAtOnce_of _ (numberStringsColumns_description Z scope live c m)
    (keyInGame_description Z scope c m) (oneInGame_description Z scope c m)
    (opensInGame_description Z scope live c m) (sessionsInGame_description Z scope c m)
    (salt_within Z scope live c m).2.1

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.realExp_one_coins
#print axioms AtPublicFiles.Shown.realExp_one_drop
#print axioms AtPublicFiles.Shown.pr_gameCoins_le
#print axioms AtPublicFiles.Shown.opensView_law
#print axioms AtPublicFiles.Shown.opensInGame_of
#print axioms AtPublicFiles.Shown.opensInGame_description
#print axioms AtPublicFiles.Shown.allAtOnce_of
#print axioms AtPublicFiles.Shown.allAtOnce_description

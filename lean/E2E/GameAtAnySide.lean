-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/GameAtAnySide.lean: the results of E2E/StringsInGame.lean and E2E/SessionsInGame.lean on the
real experiment of index privacy, for arbitrary provers.

Summary. Those two files speak of the placeholder provers, which send each round's fixed message.
Their proofs use only this about them: their search limits; that they never abort; that their listed
coins hold as many sibling digests as the request trees are deep; that the session's simulator
always returns a value; and index privacy of the scheme with them. Here these are hypotheses on
arbitrary provers h of the scheme `wholeKeySchemeOverTypedOracles r h`, for arbitrary parameters r.
E2E/LinkLaidAllAtOnce.lean applies the two lemmas with the explicit link prover substituted.

Main results.
  `keyInGame_side`: against every adversary and environment, for every N, the key in the view
    satisfies `KeyFull (h.M + 1)`, except with probability at most (h.M + 2) · 71 · 2 ^ -256.
    Hypotheses: an instance x₀ (the bound that is used runs a session beside the key; the statement
    does not name it) · `Tries r` · `LawFit` at h's search limits · `WiresFit` · h never aborts ·
    every search has at least 2 ^ 40 tries.
  `sessionsInGame_side`: against every adversary with at most tV queries, every environment that is
    valid for batches of at most one instance, and N ≤ s1 batches, every session's proof in the view
    is produced, except with probability at most N · 46 · 2 ^ -256 + ζ tV N. Hypotheses: index
    privacy of `wholeKeySchemeOverTypedOracles r h` with the simulator `simWholeKey … h Sm i₀ s1 (fun _ => True) Unit` and
    an error ζ, at all indices · `PathsFit r.queryLayout h` · Sm's simulator of a session always returns a
    value · `Tries r` · `WiresFit` · every search of a session has at least 2 ^ 40 tries.

Terms: E2E/HidingTerms.lean.

Limits.
- Every premise is a hypothesis: no provers are named here.
- All limits of the two files hold: the model (E2E/HidingTerms.lean); proofs are produced, not
  accepted; nothing about what a proof in a view opens.
- Nothing on completeness or on soundness, and on what is hidden nothing beyond the hypothesis that
  is used.


-/
import E2E.StringsInGame
import E2E.SessionsInGame

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Shown
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open AtPublicFiles.ZetaAt (Tries alpha_of_tries capFail_le_cnt)

variable (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)

theorem keyInGame_side (x₀ : r.Instance) (ht : Tries r) (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB)
    (hW : WiresFit r.queryLayout r.answerCode) (hs : NeverStops h.st) (h1 : ∀ i, 2 ^ 40 ≤ h.capT i + 1)
    (h2 : ∀ i, 2 ^ 40 ≤ h.capL i + 1) (h3 : ∀ i, 2 ^ 40 ≤ h.capB i + 1) (i : r.Index)
    (Vt : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits →
      ZKCP.Gen.AdvVerifier (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Instance (RequestProof 256 r.protocol))
    (Z : ZKCP.Gen.ViewEnv (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
      (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol)) (N : ℕ) :
    Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r h) Vt Z i N)
        (fun _ => {v | ¬ KeyFull (h.M + 1) v.ivk}) ≤
      ((h.M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256) :=
  (game_key (wholeKeySchemeOverTypedOracles r h) Z (KeyFull (h.M + 1)) Vt i N).trans
    ((key_law r.queryLayout r.seedQueries r.answerCode r.fixedSample h hL hW hs i x₀).trans
      (mul_le_mul' le_rfl (alpha_of_tries r ht h.capT h.capL h.capB h1 h2 h3)))

theorem sessionsInGame_side (Sm : Sims r.protocol) (i₀ : r.Index) (s1 : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞)
    (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit)
    (hp : ZKCP.Gen.PrivacyOn R (wholeKeySchemeOverTypedOracles r h) 1
      (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample h Sm i₀ s1 (fun _ => True) Unit) ζ (fun _ => True))
    (hpaths : PathsFit r.queryLayout h) (hSm : ∀ n y ρ ans, none ∉ (Sm.B n y ρ ans).support) (ht : Tries r)
    (hW : WiresFit r.queryLayout r.answerCode) (hB' : ∀ i, 2 ^ 40 ≤ h.capB i + 1) (i : r.Index)
    (Z : ZKCP.Gen.ViewEnv (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
      (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol)) (hZ : Z.IsValid R 1 i) (tV : ℕ)
    (Vt : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits →
      ZKCP.Gen.AdvVerifier (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Instance (RequestProof 256 r.protocol))
    (hq : ∀ ivk, (Vt ivk).QueryBound tV) (N : ℕ) (hN : N ≤ s1) :
    Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r h) Vt Z i N)
        (fun _ => {v | BadView (fun π => π.piB = none) v}) ≤
      (N : ℝ≥0∞) * (46 * (2⁻¹ : ℝ≥0∞) ^ 256) + ζ tV N := by
  refine (real_le_ideal (hp i trivial Z hZ) tV Vt N hq _).trans (add_le_add ?_ le_rfl)
  have e : (2 : ℕ) ^ 32 * 256 = 2 ^ 40 := by norm_num
  refine (ideal_le r.queryLayout r.seedQueries r.answerCode r.fixedSample h Sm i₀ s1 (fun _ => True) Unit R Vt Z i hZ N hN
    (fun _ => trivial) (fun _ n => hpaths.B n) hSm hW.oka.B.sh hW.fmt.2.2).trans
    (mul_le_mul' le_rfl ?_)
  exact (capFail_le_cnt 32 256 h.capB (fun i => e ▸ hB' i) _ _ _ 0 ht.bB).trans
    (mul_le_mul' (by exact_mod_cast ht.nB) le_rfl)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.keyInGame_side
#print axioms AtPublicFiles.Shown.sessionsInGame_side

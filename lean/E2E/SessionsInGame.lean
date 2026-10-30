-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SessionsInGame.lean: with placeholder provers, in the real experiment of index privacy, against
every adversary with a bound on its queries, every session's proof in the view is produced, except
with small probability.

Summary. The environment may name each instance from the adversary's whole view. The proof goes
through index privacy itself. "Some session's proof in the view is not produced" is a set of views,
and index privacy carries every such set from the ideal experiment to the real one at the cost of
its error (E2E/GameCarry.lean). In the ideal experiment the simulator answers a simulated run's
Fiat-Shamir queries with fresh uniform samples, whatever the adversary has asked
(E2E/DryRunsOut.lean, E2E/DryEndsWell.lean, E2E/IdealOneCall.lean). Its setup is never refused and
its counts stay within the bounds for s1 batches (E2E/IdealInvariant.lean). A union bound along the
experiment gives the result (E2E/IdealLoop.lean, E2E/IdealStrings.lean). The main limit: the provers
are the placeholder provers, which send each round's fixed message.

Main results.
  `sessionsInGame_description`: `SessionsInGame` holds at the verifier's parameters at Z, for every
    Z in scope.
  `SessionsInGame r` states: under the premises of `PrivacyWithBound r` (E2E/ZetaAtCaps.lean), and
    if every search of a session has at least 2 ^ 40 tries: against every adversary with at most tV
    oracle queries, every valid environment and N ≤ s1 batches of at most one instance each, every
    session's proof in the view is produced, except with probability at most N · 46
    · 2 ^ -256 + `boundZ (9 + CT + CL + CB) M tV N`.

Terms: E2E/HidingTerms.lean.

Limits.
- The bound is not 2 ^ -249: its second summand, `boundZ (9 + CT + CL + CB) M tV N`, is the error of
  index privacy.
- It inherits every premise and limit of `privacyWithBound_description`: the model
  (E2E/HidingTerms.lean); the scheme `wholeKeySchemeOverTypedOracles r` at fixed parameters; batches of at most one
  instance; at most s1 batches in all.
- The bound says that proofs are produced, not that the verifier accepts them: whether it accepts
  such a proof is proved at these parameters neither way. What a proof opens is not stated for a
  view: a view holds none of the committer's coins.
- The simulator's fixed index is not a parameter of the statement: the experiment's own index is
  supplied for it.
- For the key in the view see E2E/StringsInGame.lean.
- Nothing on completeness or on soundness, and on what is hidden nothing beyond the statement that
  is used.

Definitions and helper lemmas.
  `sessionsInGame_of`: for arbitrary r.


-/
import E2E.IdealStrings
import E2E.GameCarry
import E2E.ZetaAtCaps
import E2E.StringsAtInput
import Johnson.WholeKey.WorkOf

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Shown
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open AtPublicFiles.Premises (silentAtC fixedSims coinsFit_silentC)
open AtPublicFiles.ZetaAt (PrivacyWithBound privacyWithBound_description boundZ Tries tries_description
  capFail_le_cnt)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (flashProveData)

/-- **The sessions in the real experiment**, for arbitrary r. -/
def SessionsInGame (r : InnerCompilerInput) : Prop :=
  ∀ (b : r.LeafBody) (M s1 ℓ ℓr CT CL CB : ℕ) (capT capL capB : ℕ → ℕ) (Ryes : r.Index → r.Instance → Prop)
    (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit),
    M + 1 ≤ 710324 → s1 ≤ 688127 → 256 ≤ ℓ → ℓ ≤ r.compilerParameters.sMT →
    (∀ i, capT i ≤ CT) → (∀ i, capL i ≤ CL) → (∀ i, capB i ≤ CB) → (∀ i, 2 ^ 40 ≤ capB i + 1) →
    (∀ i x w, R.yes i x w → Ryes i x) →
    ∀ (i : r.Index)
      (Z : ZKCP.Gen.ViewEnv (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
        (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol)), Z.IsValid R 1 i →
    ∀ (tV : ℕ)
      (Vt : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits →
        ZKCP.Gen.AdvVerifier (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Instance (RequestProof 256 r.protocol)),
      (∀ ivk, (Vt ivk).QueryBound tV) → ∀ N : ℕ, N ≤ s1 →
      Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r (silentAtC r b M ℓ ℓr capT capL capB).side) Vt Z i N)
          (fun _ => {v | BadView (fun π => π.piB = none) v}) ≤
        (N : ℝ≥0∞) * (46 * (2⁻¹ : ℝ≥0∞) ^ 256) + boundZ (9 + CT + CL + CB) M tV N

theorem sessionsInGame_of (r : InnerCompilerInput) (hP : PrivacyWithBound r) (ht : Tries r)
    (hW : WiresFit r.queryLayout r.answerCode) : SessionsInGame r := by
  intro b M s1 ℓ ℓr CT CL CB capT capL capB Ryes R h1 h2 h3 h4 hT hL hB hB' hR i Z hZ tV Vt hq N hN
  obtain ⟨hp, hz⟩ := hP b M s1 ℓ ℓr CT CL CB capT capL capB Ryes R i h1 h2 h3 h4 hT hL hB hR
  refine (real_le_ideal (hp i trivial Z hZ) tV Vt N hq _).trans (add_le_add ?_ (hz tV N hN))
  have e : (2 : ℕ) ^ 32 * 256 = 2 ^ 40 := by norm_num
  refine (ideal_le r.queryLayout r.seedQueries r.answerCode r.fixedSample (silentAtC r b M ℓ ℓr capT capL capB).side (fixedSims r.protocol) i
    s1 (fun _ => True) Unit R Vt Z i hZ N hN (fun _ => trivial)
    (fun _ n => (pathsFit_of_coins (coinsFit_silentC r b M ℓ ℓr capT capL capB h4)).B n)
    (fun _ _ _ _ hm => by cases (PMF.mem_support_pure_iff _ _).1 hm) hW.oka.B.sh
    hW.fmt.2.2).trans (mul_le_mul' le_rfl ?_)
  exact (capFail_le_cnt 32 256 capB (fun i => e ▸ hB' i) _ _ _ 0 ht.bB).trans
    (mul_le_mul' (by exact_mod_cast ht.nB) le_rfl)

/-- **At the verifier's parameters at Z**, for every Z in scope. -/
theorem sessionsInGame_description (Z : PublicFiles) (scope : InScope Z = true)
    (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    SessionsInGame ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  sessionsInGame_of _ (privacyWithBound_description Z scope c m) (tries_description Z scope c m)
    (VerifierAndGoals.ofBuilt
      (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More),
        WiresFit (D.input Z c m).queryLayout (D.input Z c m).answerCode)
      (fun c m => (fits_built Z c m).2) c m)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.sessionsInGame_of
#print axioms AtPublicFiles.Shown.sessionsInGame_description

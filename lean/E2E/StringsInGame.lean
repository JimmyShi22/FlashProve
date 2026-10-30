-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsInGame.lean: with placeholder provers, in the real experiment of index privacy, against
every adversary and environment, the first table's proof and all link proofs in the key are
produced, except with small probability.

Summary. E2E/StringsAtInput.lean and E2E/StringsAllLinks.lean bound the scheme's run for an index
and an instance fixed before the oracles are sampled, with no adversary. The experiment that the
error bound of E2E/ZetaAtCaps.lean speaks of has one. The key is made from the empty table of oracle
answers, before anything is asked, and the experiment never changes it (`game_key`,
E2E/GameKey.lean), so the bound carries over. Without it, index privacy could be a statement about
keys without proofs. The main limit: the provers are the placeholder provers, which send each
round's fixed message.

Main results.
  `keyInGame_description`: `KeyInGame` holds at the verifier's parameters at Z, for every Z in
    scope.
  `KeyInGame r` states: if every search has at least 2 ^ 40 tries (2 ^ 40 ≤ cap i + 1), then for all
    b, M, ℓ, ℓr, every index, every adversary (any number of queries), every environment and every
    number of batches, the view's key satisfies `KeyFull (M + 1)`, except with probability at most
    (M + 2) · 71 · 2 ^ -256.
  `KeyFull n k`: the first table's proof is produced, and so is the link proof at each place below
    n.

Terms: E2E/HidingTerms.lean.

Limits.
- No session is covered here. The bound that is used (`allY_law`, Johnson/Prover/All/Law.lean) asks
  that the table of oracle answers has no entry at any query with the run's tag that holds a plain
  part of one of its rounds with that round's number (`FreshFrom`, Johnson/Prover/Law/Defs.lean),
  whatever the query's salt. In the experiment that fails as soon as the adversary has asked one
  such query with a session's tag, and after the first session for every later one. For sessions see
  E2E/SessionsInGame.lean, which does not use that bound.
- The bound says that proofs are produced, not that the verifier accepts them. Whether it accepts a
  proof of the placeholder provers is proved at these parameters neither way. What a produced proof
  opens: E2E/StringsHoldAtInput.lean, E2E/StringsHoldLink.lean.
- The lemmas `key_fixed`, `key_law` and `keyInGame_of` have an instance x₀ as a parameter: the bound
  that is used runs a session beside the key, and its share is in the number. `KeyInGame` names
  none; at the verifier's parameters the library's own fixed instance is supplied
  (`instance_nonempty_description`: the type of instances is not empty).
- All limits of E2E/StringsAllLinks.lean hold, and the model (E2E/HidingTerms.lean).
- Nothing on completeness, on soundness or on what is hidden.

Definitions and helper lemmas.
  `key_fixed`, `key_law`: the committer alone, at fixed coins and on average, from `full_fixed`
    (E2E/StringsAllLinks.lean); for any interface, wiring and provers.
  `keyInGame_of`: for arbitrary r.


-/
import E2E.GameKey
import E2E.StringsAllLinks

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Letters
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The first table's proof is produced, and so is the link proof at each place below n. -/
def KeyFull (n : ℕ) (k : FullKey lam L aT aL) : Prop :=
  k.piT.isSome = true ∧ ∀ j, j < n → LinkAt j k

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
  (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA) (hs : NeverStops h.st)
  (i : I) (x₀ : X)
include r₀ hL hW hs x₀

/-- The committer alone, at fixed coins. -/
theorem key_fixed (c : DrawC lam L Bd aT aL h.KT h.KL) (hc : 0 < c.copies.length) :
    PrFrom (Table.empty _) (commitAt W S cA h i c) {key | ¬ KeyFull c.copies.length key.1} ≤
      ((c.copies.length + 1 : ℕ) : ℝ≥0∞) * alphaAll W h.capT h.capL h.capB 0 0 0 0 0 := by
  refine (PrFrom_le_of_det (E' := {y | ¬ FullTo c.copies.length y}) (noCoin_commitAt W S cA h i c)
    ?_ _ fun g hg => ?_).trans
    (full_fixed W S cA r₀ h hL hW hs i x₀ c ⟨0, h.kB.e 0, h.coB.e 0⟩ hc)
  · exact (noCoin_commitAt W S cA h i c).bind fun key =>
      (noCoin_proveAt W cA r₀ h key.2 x₀ ⟨0, h.kB.e 0, h.coB.e 0⟩).bind fun _ => trivial
  · intro hf
    have hf' : FullTo c.copies.length (((commitAt W S cA h i c).det g).1,
        (proveAt W cA r₀ h ((commitAt W S cA h i c).det g).2 x₀
          ⟨0, h.kB.e 0, h.coB.e 0⟩).det g) := by
      simpa only [OComp.det_bind] using hf
    exact hg ⟨hf'.1.1, hf'.2⟩

/-- **The committer alone.** -/
theorem key_law :
    PrFrom (Table.empty _) (commitW W S cA h i) {key | ¬ KeyFull (h.M + 1) key.1} ≤
      ((h.M + 2 : ℕ) : ℝ≥0∞) * alphaAll W h.capT h.capL h.capB 0 0 0 0 0 := by
  show PrFrom _ ((coinsC W h).bind fun d => commitAt W S cA h i d) _ ≤ _
  refine PrFrom_coins_le _ _ _ (fun c hc => ?_) _ (onlyCoins_coinsC W h)
  have e := key_fixed W S cA r₀ h hL hW hs i x₀ c (by rw [hc.2.2.1]; exact Nat.succ_pos _)
  rw [hc.2.2.1] at e
  exact e

end Letters

open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open AtPublicFiles.Premises (silentAtC)
open AtPublicFiles.ZetaAt (Tries alpha_of_tries tries_built)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (flashProveData)

/-- **The key in the real experiment**, for arbitrary r. -/
def KeyInGame (r : InnerCompilerInput) : Prop :=
  ∀ (capT capL capB : ℕ → ℕ), (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) → ∀ (b : r.LeafBody) (M ℓ ℓr : ℕ) (i : r.Index)
      (Vt : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits →
        ZKCP.Gen.AdvVerifier (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Instance (RequestProof 256 r.protocol))
      (Z : ZKCP.Gen.ViewEnv (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
        (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol)) (N : ℕ),
      Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r (silentAtC r b M ℓ ℓr capT capL capB).side) Vt Z i N)
          (fun _ => {v | ¬ KeyFull (M + 1) v.ivk}) ≤
        ((M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256)

theorem keyInGame_of (r : InnerCompilerInput) (x₀ : r.Instance) (ht : Tries r)
    (hL : ∀ capT capL capB, LawFit r.queryLayout r.seedQueries capT capL capB) (hW : WiresFit r.queryLayout r.answerCode) :
    KeyInGame r :=
  fun capT capL capB h1 h2 h3 b M ℓ ℓr i Vt Z N =>
    (game_key (wholeKeySchemeOverTypedOracles r (silentAtC r b M ℓ ℓr capT capL capB).side) Z (KeyFull (M + 1)) Vt i
      N).trans
      ((key_law r.queryLayout r.seedQueries r.answerCode r.fixedSample (silentAtC r b M ℓ ℓr capT capL capB).side (hL capT capL capB)
        hW (neverStops_silent r.protocol _) i x₀).trans
        (mul_le_mul' le_rfl (alpha_of_tries r ht capT capL capB h1 h2 h3)))

/-- The type of instances is not empty at the verifier's parameters at Z, for every Z. -/
theorem instance_nonempty_description (Z : PublicFiles) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      Nonempty ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).Instance :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), Nonempty (D.input Z c m).Instance)
    fun _ _ => ⟨(FlashProve.dataAtFiles flashProveData Z).G.z₀.1⟩

/-- **At the verifier's parameters at Z**, for every Z in scope. -/
theorem keyInGame_description (Z : PublicFiles) (scope : InScope Z = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      KeyInGame ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), KeyInGame (D.input Z c m))
    fun c m => keyInGame_of _ (FlashProve.dataAtFiles flashProveData Z).G.z₀.1 (tries_built Z scope c m)
      (fits_built Z c m).1 (fits_built Z c m).2

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.key_fixed
#print axioms AtPublicFiles.Shown.key_law
#print axioms AtPublicFiles.Shown.keyInGame_of
#print axioms AtPublicFiles.Shown.instance_nonempty_description
#print axioms AtPublicFiles.Shown.keyInGame_description

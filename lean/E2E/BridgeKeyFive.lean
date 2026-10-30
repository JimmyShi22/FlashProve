-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/BridgeKeyFive.lean: `KeyFive` (E2E/BridgeNineCut.lean: the five clauses of
`OnBytes.Prover.HonFit` on the key file's prover and on the measure of the OOD seeds that are set
aside) FROM THE HYPOTHESES BY NAME ON THAT PROVER (`AtPublicFiles.KeyBridge.Sentences`, E2E/KeyBridge.lean)
and one measure on the OOD-seed wire. In general letters. With a member.

  **`keyFive_of`**: from `Sentences` at hT, W, a fall FT, a range ok and a set Gs of OOD seeds;
    every index with a true instance in range; the chance δ of a seed outside Gs: `KeyFive hT W
    (guardT hT (asideOf Gs) FT) (asideOf Gs) S Yes δ (zB + z + pF)`: THE SEEDS OUTSIDE Gs ARE SET
    ASIDE, and the fall is made empty there.
  `keyFive_idle`: A MEMBER, IDLE: the prover whose public abort set is everything (`idleT`), with 1
    + 0 + 0 for pT.

Limits. Four of the five clauses are E2E/KeyBridge.lean's `extT_of`, `whT_of`, `accT_of`, `prT_of`,
which are stated at three provers; here they are had at the key file's prover alone, by these
theorems' own proofs. The fifth is E2E/BridgeSeeds.lean's `prZ_of_seeds`. OF `Sentences` THREE
FIELDS ARE NOT SPENT: `exact`, `runVals`, `runForm`: so its letters sim, pv, rv and okV are idle
here. THE SET THAT IS SET ASIDE IS FORCED: all seeds outside Gs, at every index and committer's
randomness: E2E/BridgeSeeds.lean's warning on that bites here. No prover that sends a message of the
protocol is shown here to meet `Sentences`. At the idle member the accept law asks nothing. Those of
E2E/KeyBridge.lean and E2E/BridgeSeeds.lean. No property is had.


-/
import E2E.BridgeNineCut
import E2E.KeyBridge
import E2E.BridgeSeeds

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.KeyBridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open AtPublicFiles.Bridge (KeyFive asideOf not_mem_asideOf prZ_of_seeds)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
  {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {sim : SimT L} {Tied TiedM : TiedT L} {FT : FallT hT}
  {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {RV : Type} {pv : Plains L.offline.shape → RV}
  {rv : hT.Coin → RV} {okV : RV → Prop} {z zB pF : ℝ≥0∞}

/-- **The five, from the hypotheses by name.** -/
theorem keyFive_of (h : Sentences hT W sim Tied TiedM FT ok Gs pv rv okV z zB pF)
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) {Yes : I → X → Prop} {δ : ℝ≥0∞} (hy : ∀ i x, Yes i x → ok i)
    (hδ : pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ) :
    KeyFive hT W (guardT hT (asideOf Gs) FT) (asideOf Gs) S Yes δ (zB + z + pF) where
  extT := h.ext
  whT := by
    rintro w x c ρ ((hb | hh) | ⟨hz, hf⟩)
    · exact Or.inl (Or.inl (h.badZero ρ hb))
    · exact Or.inl (Or.inr (h.hidZero w x ρ hh))
    · exact (h.fallZero w x c ρ hf).elim Or.inl fun h' => Or.inr ⟨hz, h'⟩
  accT := by
    intro i x r e c hx he
    rw [guardT_eq hT FT (asideOf Gs) he]
    exact h.acc (i, r, e) (L.recOf i r e) c
      (h.tied i r e (hy i x hx) ((not_mem_asideOf Gs i r e).1 he))
  prZ := fun i _ r _ => prZ_of_seeds S i r (fun _ he => he) hδ
  prT := by
    intro i x r e c hx
    refine (pr_union_le _ _ _).trans
      (add_le_add ((pr_union_le _ _ _).trans (add_le_add h.badSmall ?_)) ?_)
    · exact h.hidSmall (i, r, e) (L.recOf i r e) (h.tiedAll i r e (hy i x hx) trivial)
    · by_cases he : e ∈ asideOf (I := I) Gs i r
      · exact (le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h' => h'.1 he)).trans (zero_le _)
      · rw [guardT_eq hT FT (asideOf Gs) he]
        exact h.fallSmall (i, r, e) (L.recOf i r e) c
          (h.tied i r e (hy i x hx) ((not_mem_asideOf Gs i r e).1 he))

/-- **A member, idle**: at the prover whose public abort set is everything. -/
theorem keyFive_idle (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) {Yes : I → X → Prop} {δ : ℝ≥0∞}
    (hy : ∀ i x, Yes i x → ok i)
    (hδ : pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ) :
    KeyFive (idleT L) W (guardT (idleT L) (asideOf Gs) fun _ _ _ => ∅) (asideOf Gs) S Yes δ
      (1 + 0 + 0) :=
  keyFive_of (sentences_idle W ok Gs) S hy hδ

end AtPublicFiles.KeyBridge

#print axioms AtPublicFiles.KeyBridge.keyFive_of
#print axioms AtPublicFiles.KeyBridge.keyFive_idle

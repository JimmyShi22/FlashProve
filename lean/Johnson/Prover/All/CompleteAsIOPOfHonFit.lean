-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/All/CompleteAsIOPOfHonFit.lean: HonFit with no seed set aside gives completeness as
an IOP, at every coin. It states no goal.

How. A failure at challenges with their work bits cleared is an abort there, or a rejected
transcript; that transcript's challenges are the cleared ones, and they pass, so the acceptance law
puts them in the abort set or the fall (everyCoinOfLaws). The clause wh carries that set from the
cleared challenges back to the challenges, and the clause pr bounds it.
-/
import Johnson.Prover.All.CompleteAsIOPEveryCoin

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.Compilation (CompleteInParts HonestProvers)

/-- At one protocol: the laws of HonFit give the bound at one coin. -/
theorem everyCoinOfLaws {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} {H : Honest Q Wt}
    {work : WorkBits Q.shape} {y : E.Str} {w : Wt} {x : Y} {c : H.Coin} {error : ℝ≥0∞}
    {B : Set (Rho Q.shape)} (hf : WorkBitsFaithful Q work)
    (hW : H.withheld w x ⊆ B) (hwh : ∀ ρ, work.cleared ρ ∈ B → ρ ∈ B)
    (hacc : ∀ τ : Tr Q.shape, work.passes τ.rho = true →
      work.sameButForNonces ((H.strat w x c).run τ.rho).1 τ → τ.rho ∉ B → Q.accept x y τ = true)
    (hpr : prRho B ≤ error) : chanceAtPassing work (FailsAt H work y w x c) ≤ error := by
  have hb : pr (unif (Rho Q.shape)) B ≤ error := hpr
  refine le_trans (pr_mono _ ?_) hb
  intro ρ hρ
  apply hwh
  rcases hρ with hw | ⟨τ, hs, hrej⟩
  · exact hW hw
  · have ht : τ.rho = work.cleared ρ :=
      (hf.noncesKeepChallenges _ _ hs).trans (Strat.rho_run _ _)
    by_contra hn
    have hp : work.passes τ.rho = true := by
      rw [ht]
      exact hf.clearedPasses ρ
    have hs' : work.sameButForNonces ((H.strat w x c).run τ.rho).1 τ := by
      rw [ht]
      exact hs
    have hn' : τ.rho ∉ B := by
      rw [ht]
      exact hn
    have ha := hacc τ hp hs' hn'
    rw [hrej] at ha
    exact Bool.noConfusion ha

variable {Index Request : Type} {lam : ℕ} {L : HolographicProtocol Index Request} {Bd : Type}
  {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- **HonFit with no seed set aside gives the form at every coin.** -/
theorem everyCoin_of_honFit {prover : HonestProvers L} {F : Falls (toRecs prover)}
    {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {Relation : Index → Request → Prop} {ζ offlineError linkError onlineError : ℝ≥0∞}
    (hf : (partsWorkOfWire (aT := aT) (aL := aL) W).Faithful)
    (h : HonFit (toRecs prover) F W S Relation (fun _ _ => ∅) ζ offlineError linkError onlineError) :
    CompleteAtEveryCoin L prover (partsWorkOfWire (aT := aT) (aL := aL) W) Relation
      offlineError linkError onlineError where
  offline := fun i x r e hy c =>
    everyCoinOfLaws hf.offline Set.subset_union_left (h.whT _ _ c)
      (fun τ hp hs hn => by
        have ha := h.accT i x r e c hy (Set.notMem_empty e) τ hp hs hn
        rw [h.extT i r e] at ha
        exact ha)
      (h.prT i x r e c hy)
  link := fun i x r e r' e' hy c =>
    everyCoinOfLaws hf.link Set.subset_union_left (h.whL _ _ c)
      (fun τ hp hs hn => by
        have ha := h.accL i x r e r' e' c hy (Set.notMem_empty e) (Set.notMem_empty e') τ hp hs hn
        rw [h.extL i r e r' e'] at ha
        exact ha)
      (h.prL i x r e r' e' c hy)
  online := fun i x r e n hy c =>
    everyCoinOfLaws hf.online Set.subset_union_left (h.whB _ _ c)
      (fun τ hp hs hn => by
        have ha := h.accB i x r e n c hy (Set.notMem_empty e) τ hp hs hn
        rw [h.extB i r e n] at ha
        exact ha)
      (h.prB i x r e n c hy)

/-- **And so the parts.** -/
theorem parts_of_honFit {prover : HonestProvers L} {F : Falls (toRecs prover)}
    {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {Relation : Index → Request → Prop} {ζ offlineError linkError onlineError : ℝ≥0∞}
    (hf : (partsWorkOfWire (aT := aT) (aL := aL) W).Faithful)
    (h : HonFit (toRecs prover) F W S Relation (fun _ _ => ∅) ζ offlineError linkError onlineError) :
    CompleteInParts L prover (partsWorkOfWire (aT := aT) (aL := aL) W) S.num Relation
      offlineError linkError onlineError :=
  have hc := everyCoin_of_honFit hf h
  { offlineAccepted := fun i x r e hy =>
      everyCoinGivesFailsRarely _ _ _ _ _ _ (hc.offline i x r e hy)
    linkAccepted := fun i x r e r' e' hy =>
      everyCoinGivesFailsRarely _ _ _ _ _ _ (hc.link i x r e r' e' hy)
    onlineAccepted := fun i x r e n hy =>
      everyCoinGivesFailsRarely _ _ _ _ _ _ (hc.online i x r e n hy)
    sendsCopyNumber := fun i x r e n c τ hy hs => h.num i x r e n c τ hy hs }

end OnBytes.Prover

#print axioms OnBytes.Prover.everyCoin_of_honFit
#print axioms OnBytes.Prover.parts_of_honFit

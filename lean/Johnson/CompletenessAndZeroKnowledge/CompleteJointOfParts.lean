-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/CompleteJointOfParts.lean: COMPLETENESS AS AN IOP, OVER COINS AND CHALLENGES TOGETHER, GIVES
THE PREMISE OF complete_argW_joint (Johnson/CompletenessAndZeroKnowledge/CompleteJoint.lean), and so the compiled scheme's
completeness at an honest side read off the three records. No goal. An implication: completeness as an IOP
is a premise, proved here of no protocol. At letters.

How. The set that AccLawsJoint measures lies in FailsRarely's (the withheld set is a failure: FailsAt's
first arm). No seed is set aside. The rest is partsGiveCompilerPremise's text. Faithful is not spent
here: it stays in CompleteIOP as the guard of what the work bits mean.
-/
import Johnson.CompletenessAndZeroKnowledge.CompleteJoint
import Johnson.Prover.All.CompleteAsIOPGivesAccLaws

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open VerifiableInference.Compilation (CompleteInParts HonestProvers)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {Index Request : Type} {lam : ℕ} {L : HolographicProtocol Index Request} {Bd : Type}
  {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- **The parts, over coins and challenges together, give AccLawsJoint.** No seed is set aside. -/
theorem partsGiveAccLawsJoint (prover : HonestProvers L) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (Relation : Index → Request → Prop)
    (offlineError linkError onlineError : ℝ≥0∞)
    (hP : CompleteInParts L prover (partsWorkOfWire (aT := aT) (aL := aL) W) S.num Relation
      offlineError linkError onlineError) :
    AccLawsJoint W S (toRecs prover).strats Relation
      (badsByOf (toRecs prover) (rejectingFalls prover (partsWorkOfWire (aT := aT) (aL := aL) W))
        fun _ _ => ∅)
      0 0 offlineError linkError onlineError := by
  refine ⟨fun i r₁ x d hy => ⟨?_, ?_, ?_, ?_⟩, fun _ _ _ _ => noSeedAside S.seed,
    fun _ _ _ _ => noSeedAside S.seed, fun i r x e hy => ?_, fun i r r' x e e' hy => ?_,
    fun i r x n e hy => ?_⟩
  · intro e₁ _ τ _ hs hn
    exact acceptedOff (H := prover.offlineProver)
      (work := (partsWorkOfWire (aT := aT) (aL := aL) W).offline) (fun ρ h => Or.inr h) τ hs hn
  · intro e₁ e₂ _ _ τ _ hs hn
    exact acceptedOff (H := prover.linkProver)
      (work := (partsWorkOfWire (aT := aT) (aL := aL) W).link) (fun ρ h => Or.inr h) τ hs hn
  · intro e₂ _ τ _ hs hn
    exact acceptedOff (H := prover.onlineProver)
      (work := (partsWorkOfWire (aT := aT) (aL := aL) W).online) (fun ρ h => Or.inr h) τ hs hn
  · intro e₂ τ hs
    exact hP.sendsCopyNumber i x d.r e₂ d.n d.κ.2.2 τ hy hs
  · have hb : pr (unif (prover.offlineProver.Coin × Rho L.offline.shape))
        {d | FailsAt prover.offlineProver (partsWorkOfWire (aT := aT) (aL := aL) W).offline
          (L.encodeIndex i r) (i, r, e) (L.recOf i r e) d.1
          ((partsWorkOfWire (aT := aT) (aL := aL) W).offline.cleared d.2)} ≤ offlineError :=
      hP.offlineAccepted i x r e hy
    refine le_trans (pr_mono _ fun q hq => ?_) hb
    rcases hq with h | h
    · exact Or.inl h
    · exact h
  · have hb : pr (unif (prover.linkProver.Coin × Rho L.link.shape))
        {d | FailsAt prover.linkProver (partsWorkOfWire (aT := aT) (aL := aL) W).link
          (L.encodeIndex i r, L.encodeIndex i r') (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') d.1
          ((partsWorkOfWire (aT := aT) (aL := aL) W).link.cleared d.2)} ≤ linkError :=
      hP.linkAccepted i x r e r' e' hy
    refine le_trans (pr_mono _ fun q hq => ?_) hb
    rcases hq with h | h
    · exact Or.inl h
    · exact h
  · have hb : pr (unif (prover.onlineProver.Coin × Rho L.onlineBatch.loc.shape))
        {d | FailsAt prover.onlineProver (partsWorkOfWire (aT := aT) (aL := aL) W).online
          (L.encodeIndex i r) (i, r, e, n) (x, L.recOf i r e) d.1
          ((partsWorkOfWire (aT := aT) (aL := aL) W).online.cleared d.2)} ≤ onlineError :=
      hP.onlineAccepted i x r e n hy
    refine le_trans (pr_mono _ fun q hq => ?_) hb
    rcases hq with h | h
    · exact Or.inl h
    · exact h

/-- **THE JOIN: completeness of the scheme with the whole key, from completeness as an IOP in its
parts**, at every honest side whose strategies, with the types of their coins, are those read off
the three records (hst, as in complete_of_honFit), whose enumerations of coins list each coin once. -/
theorem complete_of_parts (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)
    (prover : HonestProvers L) (dc : Decs (toRecs prover))
    (hst : (⟨h.KT, h.KL, h.KB, h.st⟩ : Σ KT : Type, Σ KL : Type, Σ KB : Type, Plays L KT KL KB) =
      ⟨prover.offlineProver.Coin, prover.linkProver.Coin, prover.onlineProver.Coin,
        Plays.ofRecs (toRecs prover) dc⟩)
    {Relation : Index → Request → Prop} {offlineError linkError onlineError : ℝ≥0∞}
    (hP : CompleteInParts L prover (partsWorkOfWire (aT := aT) (aL := aL) W) S.num Relation
      offlineError linkError onlineError)
    (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA) (hF : SideFit W p h)
    (okT : h.kT.OK) (okL : h.kL.OK) (okB : h.kB.OK) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Relation))
      (argW W S cA r₀ p h) 1
      (alphaAll W h.capT h.capL h.capB 0 0 offlineError linkError onlineError) := by
  cases h
  cases hst
  refine complete_argW_joint W S cA r₀ p _ Relation
    (badsByOf (toRecs prover) (rejectingFalls prover (partsWorkOfWire (aT := aT) (aL := aL) W))
      fun _ _ => ∅) hL hW hF ?_ ?_ okT okL okB
  · exact partsGiveAccLawsJoint prover W S Relation offlineError linkError onlineError hP
  · exact stopsIn_ofRecs (toRecs prover)
      (rejectingFalls prover (partsWorkOfWire (aT := aT) (aL := aL) W)) dc fun _ _ => ∅

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.partsGiveAccLawsJoint
#print axioms OnBytes.WholeKey.complete_of_parts

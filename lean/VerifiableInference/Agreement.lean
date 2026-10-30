-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Agreement.lean

Proved: two statements of VerifiableInference/Statements.lean, `Complete` and `Sound`, agree with
the properties that ZKCP/Defs.lean of this library defines, for the relation
`system.uploadRelation` and the three algorithms `system.uploadArgument` of an argument system (in
names, "upload" means: in the form of ZKCP/Defs.lean):
  * `Complete system α` is completeness error α (ZKCP.HasCompletenessError): `complete_iff`;
  * `Sound system ε` is index binding with error ε (tC + tP) (ZKCP.HasIndexBinding), with the
    extractor of `Sound` as the first part of that definition's extractor:
    `sound_iff`; its two directions are `indexBinding_of_sound` and `sound_of_indexBinding` (the
    latter for any bound in two arguments that is at most ε (tC + tP)).
So a theorem about `ZKCP.HasIndexBinding`, for these two objects, is a theorem about `Sound`.
-/
import VerifiableInference.Checks

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

variable (system : ArgumentSystem)

/-- The relation of an argument system, in the form of ZKCP/Defs.lean:
index = weights, instance = prompt and output tokens, no witness; the public parameters of an index
are those of the weights. -/
def ArgumentSystem.uploadRelation : ZKCP.IndexedRelation system.Weights (List Token × List Token)
    Unit system.PublicParameters where
  rel weights x _ := system.IsModelOutput weights x.1 x.2
  pp := system.publicParameters

/-- The honest committer, as one algorithm: it returns the commitment, and the weights with the
randomness. -/
def ArgumentSystem.committer (weights : system.Weights) : RandomizedAlgorithm
    (Commitment × (system.Weights × system.CommitmentRandomness)) :=
  system.sampleCommitmentRandomness.bind fun randomness =>
    (system.commit weights randomness).toRandomized.bind fun commitment => .done
        (commitment, (weights, randomness))

/-- The honest committer, prover and verifier of an argument system, in the form of ZKCP/Defs.lean:
the verifier's key is the commitment; the prover's key is the weights with the committer's
randomness. -/
def ArgumentSystem.uploadArgument :
    ZKCP.Arg 256 system.Weights (List Token × List Token) Unit Commitment
        (system.Weights × system.CommitmentRandomness) system.Proof where
  C weights := (system.committer weights).toUpload
  P key x _ := (system.prove key.1 key.2 x.1 x.2).toUpload
  V commitment x proof := (system.verify commitment x.1 x.2 proof).toRandomized.toUpload

/-- `Complete` is completeness error α (ZKCP/Defs.lean: HasCompletenessError), for the relation and
the algorithms of the argument system. -/
theorem complete_iff (α : ℝ≥0∞) : Complete system α ↔ ZKCP.HasCompletenessError
    system.uploadRelation system.uploadArgument α := by
  have key : ∀ (weights : system.Weights) (prompt output : List Token),
      Prob (do let randomness ← system.sampleCommitmentRandomness
               let commitment ← (system.commit weights randomness).toRandomized
               let proof ← system.prove weights randomness prompt output
               (system.verify commitment prompt output proof).toRandomized)
                   {accepted | accepted = false}
        = ZKCP.Pr (ZKCP.completenessExp system.uploadArgument weights (prompt, output) ())
            (fun _ => {b | b = false}) := by
    intro weights prompt output
    unfold Prob ZKCP.Pr ZKCP.PrCoins
    refine lintegral_congr fun H => ?_
    show ZKCP.prob ((system.sampleCommitmentRandomness.bind fun randomness =>
          (system.commit weights randomness).toRandomized.bind fun commitment =>
          (system.prove weights randomness prompt output).bind fun proof =>
          (system.verify commitment prompt output proof).toRandomized).run H) _
      = ZKCP.prob (((system.committer weights).toUpload.bind fun k =>
          (system.prove k.2.1 k.2.2 prompt output).toUpload.bind fun π =>
          (system.verify k.1 prompt output π).toRandomized.toUpload).run H) _
    congr 1
    simp only [ZKCP.run_bind, run_toUpload, ArgumentSystem.committer, run_bind, run_done,
        PMF.bind_bind, PMF.pure_bind]
  constructor
  · intro h weights x w hx
    obtain ⟨prompt, output⟩ := x
    rw [← key]
    exact h weights prompt output hx
  · intro h weights prompt output hOutput
    rw [key]
    exact h weights (prompt, output) () hOutput

/-- `Sound` gives index binding (ZKCP/Defs.lean: HasIndexBinding), with the extractor of `Sound` as
the first part of that definition's extractor and ε (tC + tP) as the error. -/
theorem indexBinding_of_sound (ε : ℕ → ℝ≥0∞) (h : Sound system ε) :
    ZKCP.HasIndexBinding system.uploadRelation system.uploadArgument (fun tC tP => ε (tC + tP)) :=
        by
  classical
  obtain ⟨extractor, h0⟩ := h
  refine ⟨⟨extractor, fun _ _ _ _ _ => ()⟩, fun tC tP St Ct Pt hC hP => ?_⟩
  have b1 := h0 tC tP St (ofUpload Ct) ((queryBound_ofUpload Ct tC).mpr hC)
    (fun state => (ofUpload (Pt state)).bind fun xp => .done (xp.1.1, xp.1.2, xp.2))
    (fun state => queryBound_map _ (ofUpload (Pt state)) tP
        ((queryBound_ofUpload (Pt state) tP).mpr (hP state)))
  refine le_trans ?_ b1
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_mono fun H => ?_
  have e1 : (Ct.withTrace.bind fun c => (Pt c.1.2).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, extractor c.1.1 c.2, p.1.1, ()⟩ : ZKCP.BindingOutcome system.Weights
              (List Token × List Token) Unit)).run H
      = ((ofUpload Ct).withQueryLog.run H).bind fun c =>
          ((ofUpload (Pt c.1.2)).withQueryLog.run H).bind fun p =>
          PMF.pure ⟨(system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H, extractor c.1.1 c.2,
              p.1.1, ()⟩ := by
    simp only [ZKCP.run_bind, run_toUpload, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind,
        run_ofUpload_withQueryLog]
    rfl
  have e2 : ((ofUpload Ct).withQueryLog.bind fun c =>
        ((ofUpload (Pt c.1.2)).bind fun xp => RandomizedAlgorithm.done (xp.1.1, xp.1.2, xp.2)).bind
            fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run H
      = ((ofUpload Ct).withQueryLog.run H).bind fun c =>
          ((ofUpload (Pt c.1.2)).withQueryLog.run H).bind fun p =>
          PMF.pure (extractor c.1.1 c.2, p.1.1.1, p.1.1.2,
              (system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
        PMF.bind_bind]
    refine congrArg _ (funext fun c => ?_)
    rw [run_withQueryLog_bind_fst H (ofUpload (Pt c.1.2))
      (fun xp => PMF.pure (extractor c.1.1 c.2, xp.1.1, xp.1.2,
          (system.verify c.1.1 xp.1.1 xp.1.2 xp.2).evaluate H))]
  show ZKCP.prob ((Ct.withTrace.bind fun c => (Pt c.1.2).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, extractor c.1.1 c.2, p.1.1, ()⟩ : ZKCP.BindingOutcome system.Weights
              (List Token × List Token) Unit)).run H) _
    ≤ ZKCP.prob (((ofUpload Ct).withQueryLog.bind fun c =>
        ((ofUpload (Pt c.1.2)).bind fun xp => RandomizedAlgorithm.done (xp.1.1, xp.1.2, xp.2)).bind
            fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run H) _
  rw [e1, e2, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun p => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le ?_
  rintro ⟨hAccepted, hBad⟩
  show (system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H = true
    ∧ ¬ ∃ weights, extractor c.1.1 c.2 = some weights ∧ system.IsModelOutput weights p.1.1.1 p.1.1.2
  refine ⟨hAccepted, ?_⟩
  rintro ⟨weights, hWeights, hOutput⟩
  change p.1.1 ∉ system.uploadRelation.L (extractor c.1.1 c.2) ∨ ¬ system.uploadRelation.rel'
      (extractor c.1.1 c.2) p.1.1 () at hBad
  rw [hWeights] at hBad
  rcases hBad with hb | hb
  · exact hb ⟨(), hOutput⟩
  · exact hb hOutput

/-- The other direction: index binding (ZKCP/Defs.lean: HasIndexBinding), for the relation and the
algorithms of an argument system, gives `Sound`.
The extractor of `Sound` is the first part of that definition's extractor. That definition's bound
has two arguments; `Sound` asks for a bound in tC + tP. Assumed (`hε`): ε₂ tC tP is at most
ε (tC + tP), for all tC and tP. -/
theorem sound_of_indexBinding (ε₂ : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (h : ZKCP.HasIndexBinding system.uploadRelation system.uploadArgument ε₂)
        (hε : ∀ tC tP, ε₂ tC tP ≤ ε (tC + tP)) : Sound system ε := by
  classical
  obtain ⟨E, hE⟩ := h
  refine ⟨E.Ei, fun tC tP St committer hC prover hP => ?_⟩
  have b1 := hE tC tP St committer.toUpload
    (fun state => ((prover state).bind fun y => RandomizedAlgorithm.done
        ((y.1, y.2.1), y.2.2)).toUpload)
    ((queryBound_toUpload committer tC).mpr hC)
    (fun state => (queryBound_toUpload _ tP).mpr (queryBound_map _ (prover state) tP (hP state)))
  refine le_trans ?_ (le_trans b1 (hε tC tP))
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_mono fun H => ?_
  have e1 : (committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (E.Ei c.1.1 c.2, y.1, y.2.1, accepted)).run H
      = (committer.withQueryLog.run H).bind fun c =>
          (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
              ((y.1, y.2.1), y.2.2)).withQueryLog.run H).bind fun p =>
            PMF.pure (E.Ei c.1.1 c.2, p.1.1.1, p.1.1.2, (system.verify c.1.1 p.1.1.1 p.1.1.2
                p.1.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done]
    refine congrArg _ (funext fun c => ?_)
    rw [run_withQueryLog_bind_fst H ((prover c.1.2).bind fun y => RandomizedAlgorithm.done
        ((y.1, y.2.1), y.2.2))
      (fun x => PMF.pure (E.Ei c.1.1 c.2, x.1.1, x.1.2, (system.verify c.1.1 x.1.1 x.1.2
          x.2).evaluate H))]
    simp only [run_bind, run_done, PMF.bind_bind, PMF.pure_bind]
  have e2 : (committer.toUpload.withTrace.bind fun c =>
        (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
            ((y.1, y.2.1), y.2.2)).toUpload).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, E.Ei c.1.1 c.2, p.1.1, E.Ew c.1.1 c.2 p.1.1 p.1.2 p.2⟩ :
            ZKCP.BindingOutcome system.Weights (List Token × List Token) Unit)).run H
      = (committer.withQueryLog.run H).bind fun c =>
          (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
              ((y.1, y.2.1), y.2.2)).withQueryLog.run H).bind fun p =>
            PMF.pure ⟨(system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H, E.Ei c.1.1 c.2, p.1.1,
                ()⟩ := by
    simp only [ZKCP.run_bind, run_toUpload, run_toUpload_withTrace,
        DeterministicAlgorithm.run_toRandomized, PMF.pure_bind]
    rfl
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (E.Ei c.1.1 c.2, y.1, y.2.1, accepted)).run H) _
    ≤ ZKCP.prob ((committer.toUpload.withTrace.bind fun c =>
        (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
            ((y.1, y.2.1), y.2.2)).toUpload).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, E.Ei c.1.1 c.2, p.1.1, E.Ew c.1.1 c.2 p.1.1 p.1.2 p.2⟩ :
            ZKCP.BindingOutcome system.Weights (List Token × List Token) Unit)).run H) _
  rw [e1, e2, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun p => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le ?_
  rintro ⟨hAccepted, hBad⟩
  show (system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H = true ∧
    (p.1.1 ∉ system.uploadRelation.L (E.Ei c.1.1 c.2) ∨ ¬ system.uploadRelation.rel'
        (E.Ei c.1.1 c.2) p.1.1 ())
  refine ⟨hAccepted, ?_⟩
  cases hExtracted : E.Ei c.1.1 c.2 with
  | none => exact Or.inl (fun hx => hx)
  | some weights => exact Or.inr (fun hOutput => hBad ⟨weights, hExtracted, hOutput⟩)

/-- `Sound system ε` is index binding with error ε (tC + tP), for the relation and the algorithms of
the argument system. -/
theorem sound_iff (ε : ℕ → ℝ≥0∞) :
    Sound system ε ↔ ZKCP.HasIndexBinding system.uploadRelation system.uploadArgument
        (fun tC tP => ε (tC + tP)) :=
  ⟨indexBinding_of_sound system ε, fun h => sound_of_indexBinding system _ ε h fun _ _ => le_rfl⟩

end VerifiableInference

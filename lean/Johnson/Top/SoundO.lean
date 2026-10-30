-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SoundO.lean: soundness for a claim with an extractor that may query the hash function,
next to `SoundForWith` (VerifiableInference/MoreStatements.lean), and the way to it from index
binding with such an extractor (Johnson/Top/GameO.lean).

What this file states. Definitions and theorems with their proofs.
  `SoundForWithO system extractor q claim ε`: the experiment and the event of `SoundForWith` with
    one change: the extractor is handed the commitment and the committer's query log, as there, and
    is an algorithm without coins that may also query the hash function, at most q times. It runs
    when the committer has ended, before the prover: nothing that the prover does enters the weights
    that it gives. Its queries are shown to nobody.
  `soundForWithO_of_soundForWith`: an extractor of `SoundForWith` is one that asks nothing.
  `soundForWithO_of_indexBindingWithO`, `soundForWithO_ofArgument`:
    `soundForWith_of_indexBindingWith` (VerifiableInference/AgreementWith.lean) and
    `soundForWith_ofArgument` (VerifiableInference/OfArgument.lean) for such an extractor.
  `Rec.CommitmentBindsO`, `Rec.soundForWithO_systemE`: Johnson/Top/FrontCommit.lean's
    `CommitmentBinds` and `soundForWith_systemE_ext` likewise: the scheme whose verifier holds the
    key itself keeps `bindingExp`'s game; the step behind the commitment alone takes the new one.

Under which hypotheses. Each theorem takes the notion before its step as a hypothesis:
`SoundForWith` (h); index binding with such an extractor (hE), with its bound at most ε (tC + tP)
(hε), and that the relation gives the claim (hR) or that the verifier draws no coin (hV).
`Rec.soundForWithO_systemE` takes index binding of the scheme whose verifier holds the key itself
(hb), that this verifier tosses no coin (hV), `Rec.CommitmentBindsO …` (hc: a proposition by
definition), the premise `sound` on the builder, and hε.

What it does not show. `SoundForWith` and every statement that names it stay as they are. The new
notion asks less of an extractor: that the weights can be told from what the committer has seen
ALONE is not said by it. Kept: given the hash function, the weights are fixed when the commitment is
put out. No theorem of this library passes from `SoundForWithO` at q > 0 to `SoundForWith`,
`SoundFor` or `Sound`. The library's theorems on many proofs, several commitments, an honest
commitment and a map of weights have no counterpart here: one commitment, one proof.

-/
import Johnson.Top.GameO
import Johnson.Top.FrontCommit

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

/-- Soundness for a claim, for a given extractor that may query the hash function at most q times
and draws no coin. For every committer with at most `committerQueries` queries to the hash function
and every prover with at most `proverQueries` queries: the probability that the verifier accepts,
while the extractor, run on the committer's commitment and queries when the committer has ended,
gives no weights, or gives weights for which the claim does not hold for the prompt and the output
tokens, is at most ε (committerQueries + proverQueries). -/
def SoundForWithO (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → DeterministicAlgorithm (Option system.Weights)) (q : ℕ)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞) : Prop :=
  (∀ commitment queryLog, (extractor commitment queryLog).toRandomized.QueryBound q) ∧
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let extracted ← (extractor commitment queryLog).toRandomized
            let (prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (extracted, prompt, output, accepted))
          {(extracted, prompt, output, accepted) |
            accepted = true ∧
            ¬ ∃ weights, extracted = some weights ∧ claim weights prompt output}
          ≤ ε (committerQueries + proverQueries)

variable (system : ArgumentSystem)

/-- An extractor of `SoundForWith` is one that asks nothing. -/
theorem soundForWithO_of_soundForWith
    {extractor : Commitment → QueryLog → Option system.Weights}
    {claim : system.Weights → List Token → List Token → Prop} {ε : ℕ → ℝ≥0∞}
    (h : SoundForWith system extractor claim ε) :
    SoundForWithO system (fun c l => DeterministicAlgorithm.done (extractor c l)) 0 claim ε :=
  ⟨fun _ _ => trivial, h⟩

/-- Index binding with a named extractor that may query the hash function gives soundness for a
claim with that extractor. `soundForWith_of_indexBindingWith`
(VerifiableInference/AgreementWith.lean), its proof with one step more. -/
theorem soundForWithO_of_indexBindingWithO {PP : Type}
    (R : ZKCP.IndexedRelation system.Weights (List Token × List Token) Unit PP)
    (claim : system.Weights → List Token → List Token → Prop)
    (hR : ∀ (weights : system.Weights) (x : List Token × List Token), R.rel weights x () →
      claim weights x.1 x.2)
    (E : ZKCP.ExtractorO 256 system.Weights (List Token × List Token) Unit Commitment system.Proof)
    (q : ℕ) (ε₂ : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (hE : ZKCP.HasIndexBindingWithO R system.uploadArgument E q ε₂)
    (hε : ∀ tC tP, ε₂ tC tP ≤ ε (tC + tP)) :
    SoundForWithO system (fun c l => deterministicOf (E.Ei c l)) q claim ε := by
  classical
  refine ⟨fun c l => (queryBound_toUpload _ q).mp (by
    rw [toUpload_deterministicOf _ (hE.1 c l).2]
    exact (hE.1 c l).1), ?_⟩
  intro tC tP St committer hC prover hP
  have b1 := hE.2 tC tP St committer.toUpload
    (fun state => ((prover state).bind fun y => RandomizedAlgorithm.done
        ((y.1, y.2.1), y.2.2)).toUpload)
    ((queryBound_toUpload committer tC).mpr hC)
    (fun state => (queryBound_toUpload _ tP).mpr (queryBound_map _ (prover state) tP (hP state)))
  refine le_trans ?_ (le_trans b1 (hε tC tP))
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_mono fun H => ?_
  have hrun : ∀ c l, (E.Ei c l).run H = PMF.pure ((deterministicOf (E.Ei c l)).evaluate H) := by
    intro c l
    rw [← DeterministicAlgorithm.run_toRandomized, ← run_toUpload,
      toUpload_deterministicOf _ (hE.1 c l).2]
  have e1 : (committer.withQueryLog.bind fun c =>
        (deterministicOf (E.Ei c.1.1 c.2)).toRandomized.bind fun s =>
        (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (s, y.1, y.2.1, accepted)).run H
      = (committer.withQueryLog.run H).bind fun c =>
          (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
              ((y.1, y.2.1), y.2.2)).withQueryLog.run H).bind fun p =>
            PMF.pure ((deterministicOf (E.Ei c.1.1 c.2)).evaluate H, p.1.1.1, p.1.1.2,
              (system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done]
    refine congrArg _ (funext fun c => ?_)
    rw [run_withQueryLog_bind_fst H ((prover c.1.2).bind fun y => RandomizedAlgorithm.done
        ((y.1, y.2.1), y.2.2))
      (fun x => PMF.pure ((deterministicOf (E.Ei c.1.1 c.2)).evaluate H, x.1.1, x.1.2,
        (system.verify c.1.1 x.1.1 x.1.2 x.2).evaluate H))]
    simp only [run_bind, run_done, PMF.bind_bind, PMF.pure_bind]
  have e2 : (committer.toUpload.withTrace.bind fun c => (E.Ei c.1.1 c.2).bind fun s =>
        (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
            ((y.1, y.2.1), y.2.2)).toUpload).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, s, p.1.1, E.Ew c.1.1 c.2 p.1.1 p.1.2 p.2⟩ :
            ZKCP.BindingOutcome system.Weights (List Token × List Token) Unit)).run H
      = (committer.withQueryLog.run H).bind fun c =>
          (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
              ((y.1, y.2.1), y.2.2)).withQueryLog.run H).bind fun p =>
            PMF.pure ⟨(system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H,
              (deterministicOf (E.Ei c.1.1 c.2)).evaluate H, p.1.1, ()⟩ := by
    simp only [ZKCP.run_bind, hrun, run_toUpload, run_toUpload_withTrace,
        DeterministicAlgorithm.run_toRandomized, PMF.pure_bind]
    rfl
  show ZKCP.prob ((committer.withQueryLog.bind fun c =>
        (deterministicOf (E.Ei c.1.1 c.2)).toRandomized.bind fun s =>
        (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (s, y.1, y.2.1, accepted)).run H) _
    ≤ ZKCP.prob ((committer.toUpload.withTrace.bind fun c => (E.Ei c.1.1 c.2).bind fun s =>
        (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
            ((y.1, y.2.1), y.2.2)).toUpload).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, s, p.1.1, E.Ew c.1.1 c.2 p.1.1 p.1.2 p.2⟩ :
            ZKCP.BindingOutcome system.Weights (List Token × List Token) Unit)).run H) _
  rw [e1, e2, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun p => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le ?_
  rintro ⟨hAccepted, hBad⟩
  show (system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H = true ∧
    (p.1.1 ∉ R.L ((deterministicOf (E.Ei c.1.1 c.2)).evaluate H) ∨
      ¬ R.rel' ((deterministicOf (E.Ei c.1.1 c.2)).evaluate H) p.1.1 ())
  refine ⟨hAccepted, ?_⟩
  cases hExtracted : (deterministicOf (E.Ei c.1.1 c.2)).evaluate H with
  | none => exact Or.inl (fun hx => hx)
  | some weights =>
      exact Or.inr (fun hRel => hBad ⟨weights, hExtracted, hR weights p.1.1 hRel⟩)

section OfArgument
variable {I Pf : Type} {bound : ℕ}
  (A : ZKCP.Arg 256 I (List Token × List Token) Unit (ZKCP.Digest 256) (I × Fin (bound + 1)) Pf)
  (commit : I → Fin (bound + 1) → ZKCP.OComp 256 (ZKCP.Digest 256))
  (nextToken : I → List Token → Option Token)

/-- `soundForWith_ofArgument` (VerifiableInference/OfArgument.lean) for an extractor that may query
the hash function. -/
theorem soundForWithO_ofArgument (hV : ∀ key x proof, (A.V key x proof).DrawsNoCoin)
    (claim : I → List Token → List Token → Prop)
    (E : ZKCP.ExtractorO 256 I (List Token × List Token) Unit (ZKCP.Digest 256) Pf) (q : ℕ)
    (ε₂ : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (hE : ZKCP.HasIndexBindingWithO
      (ZKCP.languageRelation fun i (x : List Token × List Token) => claim i x.1 x.2) A E q ε₂)
    (hε : ∀ tC tP, ε₂ tC tP ≤ ε (tC + tP)) :
    SoundForWithO (ArgumentSystem.ofArgument A commit nextToken)
      (fun c l => deterministicOf (E.Ei c l)) q claim ε :=
  soundForWithO_of_indexBindingWithO (ArgumentSystem.ofArgument A commit nextToken)
    (ZKCP.languageRelation fun i (x : List Token × List Token) => claim i x.1 x.2) claim
    (fun _ _ h => h) E q ε₂ ε
    (hE.of_sameV (ArgumentSystem.uploadArgument_ofArgument_V A commit nextToken hV)) hε

end OfArgument

namespace Rec
open Rom ZKCP

variable {I X IVK ISK Pf : Type} (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
  (E : ZKCP.Gen.Extractor (rom 256) I X Unit IVK Pf) (enc : IVK → Option ZKCP.Str)
  (extO : ZKCP.ExtractorO 256 I X Unit (ZKCP.Digest 256) (IVK × Pf)) (q : ℕ)

/-- Index binding, in `bindingExp`'s game, of the scheme whose verifier holds the key itself gives
index binding of the scheme whose verifier holds the hash function's answer at the key's code, in
the game where the extractor `extO` may query the hash function at most q times, at the bound ε'. -/
def CommitmentBindsO (IsTrue : I → X → Prop) (ε ε' : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ZKCP.HasIndexBindingWith (ZKCP.languageRelation IsTrue) (SpecialAny.oneOf G) (Special.extOf E) ε →
    ZKCP.HasIndexBindingWithO (ZKCP.languageRelation IsTrue) ((SpecialAny.oneOf G).digestKey enc)
      extO q ε'

variable (bound : ℕ) {build : List Token × List Token → List Token → Option X} (π₀ : IVK × Pf)
  (nextToken : I → List Token → Option Token)

/-- `soundForWith_systemE_ext` (Johnson/Top/FrontCommit.lean) with `CommitmentBindsO` in the place
of `CommitmentBinds`. -/
theorem soundForWithO_systemE {IsTrue : I → X → Prop} {ε ε' : ℕ → ℕ → ℝ≥0∞} {ε'' : ℕ → ℝ≥0∞}
    (hb : ZKCP.Gen.HasIndexBindingWith (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) G E ε)
    (hV : ∀ k x π, (G.V k x π).NoCoin) (hc : CommitmentBindsO G E enc extO q IsTrue ε ε')
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε' tC tP ≤ ε'' (tC + tP)) :
    SoundForWithO (tokenArgumentSystem G enc bound build π₀ nextToken)
      (fun c l => deterministicOf (extO.Ei c l)) q claim ε'' :=
  soundForWithO_ofArgument (tokenScheme G enc bound build π₀) (commitE G enc bound) nextToken
    (ZKCP.drawsNoCoin_buildInstance_V _ _ _ _
      (ZKCP.drawsNoCoin_verifyDigestKey enc fun k x π => drawsNoCoin_ofRom _ (hV k x π)))
    claim extO.buildInstance q ε' ε''
    (ZKCP.HasIndexBindingWithO.buildInstance x₀ sound
      (ZKCP.HasIndexBindingWithO.of_sameV rfl
        (hc (ZKCP.SpecialAny.bindingWith_of_gen (ZKCP.languageRelation IsTrue)
          (ZKCP.SpecialAny.agrees_oneOf G) (ZKCP.Special.extOf E) ε
          (by rw [ZKCP.Special.extTo_extOf]; exact hb)))))
    hε

end Rec

end VerifiableInference

#print axioms VerifiableInference.soundForWithO_of_soundForWith
#print axioms VerifiableInference.soundForWithO_of_indexBindingWithO
#print axioms VerifiableInference.soundForWithO_ofArgument
#print axioms VerifiableInference.Rec.soundForWithO_systemE

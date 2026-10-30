-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ExtractorAnswersOnHonestTables.lean: THE EXTRACTOR OF SOUNDNESS ANSWERS ON THE HONEST COMMITTER's TABLES. A sentence whose proof spends soundness AND completeness on one
object: at the index of a request of the relation, at every randomness of the encoding and every out-of-domain seed at which the honest
table has no collision, soundness's extractor returns an index on the honest table with its own sample.

  `offline_rounds_few`     the offline part has at most 2^20 rounds
  `offline_work_small`     no round of it has more than 64 bits of proof of work
  `lost_is_rarely_accepted`  from soundness's offline clause: where the extractor answers nothing, EVERY prover of the offline part is accepted
                           with probability at most 2^-44, over the challenges that pass
  `extractor_answers`      **the sentence**

The proof. Suppose that the extractor answers nothing. Soundness's offline clause: the prover has lost, at the start, towards «the offline
verifier rejects»; so every prover is accepted with probability at most 2^-44 over cleared challenges (`probability_of_doomed`,
Hiop/SoundAsIOPSum.lean). Completeness's offline list: the honest prover is accepted at EVERY cleared challenge
(`offline_accepts_own_run`, E2E/OfflineAcceptedInSoundnessWords.lean): probability 1. The two contradict.

WHY IT IS A TEST OF «ONE PROTOCOL». The step from «rejects» to «accepts» goes through only if the verifier, the table, the sample and the law of the
challenges are the same terms in the two. Were soundness and completeness said of two verifiers, or over two laws, this proof would not
type-check.

WHAT COUNTS HERE IS THE PROOF, NOT THE SENTENCE. At an index in range the sentence, and more (WHICH index is returned; that there is no collision), follows from the
decoder's own clause with neither property spent: E2E/OneIndexOneRelation.lean.

Limits. AN IMPLICATION from two premises: soundness in parts with its errors within 2^-128 a round, and `OfflineDebts` at no fall and measures 0: no value of
either is shown here. It says that an index is returned, NOT WHICH. Nothing at a seed with a collision. Nothing on any property.
-/
import E2E.OfflineAcceptedInSoundnessWords
import E2E.SoundAsIOPProbabilityAtFilesProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.OneProtocol
open Iop Prob
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open TypedOracleCompiler.Iop (RoundsQueryLayout.clearing_atMostToOne RoundsQueryLayout.clearedToOne_eachAtMost RoundsQueryLayout.mostWork
  RoundsQueryLayout.clearedToOne)
open TypedOracleCompiler.Compile.Batch.Cms (wTC)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts)
open LPFD.Full (XF)
open AtPublicFiles.AtFiles AtPublicFiles.Committed
open VerifierAndGoals (PublicFiles)

local instance (priority := high) extractorAnswersPads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) extractorAnswersNonempty {α : Type} [Inhabited α] : Nonempty α :=
  ⟨default⟩

variable {Z : PublicFiles}

/-- The offline part has at most 2^20 rounds. -/
theorem offline_rounds_few (fill : (protocolAtFiles Z).Fill) : (protocolAtFiles Z).offline.shape.length ≤ 2 ^ 20 := by
  have h := roundsAtFiles_le Z (filesAt Z).fixedMessageProvers fill
  rw [HolographicProtocol.length_wholeRunShape] at h
  exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans h))

/-- No round of the offline part has more than 64 bits of proof of work. -/
theorem offline_work_small (Z : PublicFiles) :
    RoundsQueryLayout.mostWork (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh ≤ 64 :=
  (le_max_left _ _).trans (mostWorkAtFiles_le Z)

/-- **Where the extractor answers nothing, every prover of the offline part is accepted with probability at most 2^-44**, over the
challenges that pass. -/
theorem lost_is_rarely_accepted {errors : (protocolAtFiles Z).RoundErrors}
    (within : errors.Within (filesAt Z).annT (offlinePlaces Z) (filesAt Z).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (sound : (protocolAtFiles Z).SoundInParts (relationAtFiles Z) errors) (fill : (protocolAtFiles Z).Fill)
    (firstTable : (protocolAtFiles Z).Table) (firstSample : (protocolAtFiles Z).Sample)
    (hc : ¬ (protocolAtFiles Z).hasCollisionAt firstTable firstSample.1)
    (hx : (protocolAtFiles Z).extractIndex firstTable firstSample = none) (β : Type)
    (prover : Strat (protocolAtFiles Z).offline.shape β) :
    pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | ¬ (protocolAtFiles Z).offline.accept firstSample firstTable
          (prover.run ((offlineClearing Z).cleared ρ)).1 = false} ≤ (2 : ℝ≥0∞)⁻¹ ^ 44 := by
  have lost := sound.offline firstTable firstSample hc hx
  have below : Err.Below errors.offline ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
    Err.Below.of_timesShared (Nat.two_pow_pos _) within.offline
  refine (probability_of_doomed _ _ _ β prover (offlineClearing Z) _
    (RoundsQueryLayout.clearing_atMostToOne _ _ _ (four_wiringAtFiles Z).2.1.sh) lost).trans ?_
  refine (sumOfProbabilities_timesByRound_le _ _ _ _ _ (RoundsQueryLayout.clearedToOne_eachAtMost _ _ _)
    below).trans ?_
  calc ((protocolAtFiles Z).offline.shape.length : ℝ≥0∞) *
        (((2 ^ RoundsQueryLayout.mostWork (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh : ℕ) :
          ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128)
      ≤ ((2 ^ 20 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 64 :=
        mul_le_mul' (Nat.cast_le.2 (offline_rounds_few fill)) (work_times_bound (offline_work_small Z))
    _ = (2 : ℝ≥0∞)⁻¹ ^ 44 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (64 : ℕ) = 20 + 44 from rfl, pow_add, ← mul_assoc,
          ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

variable {Fx : FileDescription KeyInst} {TrT X₀T XT Q₂ Q₃ : Type} {BT : ProverCoinCounts} [Fintype Q₂]
  [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃]
  {HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT}
  {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray} {shT : TableKey → Fx.S₂}
  {Relation : FullSizeMatrix → XF → Prop} {Tied TiedM : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)}

/-- **THE EXTRACTOR ANSWERS ON THE HONEST TABLE WITH ITS OWN SAMPLE**, where that table has no collision at the sample's point. -/
theorem extractor_answers {errors : (protocolAtFiles Z).RoundErrors}
    (within : errors.Within (filesAt Z).annT (offlinePlaces Z) (filesAt Z).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (sound : (protocolAtFiles Z).SoundInParts (relationAtFiles Z) errors)
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation (fun _ _ _ => ∅) Tied TiedM 0 0 0) (i : FullSizeMatrix)
    (x : XF) (hy : Relation i x) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed)
    (hc : ¬ (protocolAtFiles Z).hasCollisionAt ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e).1) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) ≠ none := by
  intro hx
  obtain ⟨c⟩ := (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).neCoin
  have small := lost_is_rarely_accepted within sound ⟨(protocolAtFiles Z).encodeIndex i r, ((protocolAtFiles Z).recOf i r e).2, x⟩
    ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) hc hx Unit
    ((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c)
  have all : {ρ : Rho (protocolAtFiles Z).offline.shape | ¬ (protocolAtFiles Z).offline.accept ((protocolAtFiles Z).recOf i r e) ((protocolAtFiles Z).encodeIndex i r)
      (((offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
        ((offlineClearing Z).cleared ρ)).1 = false} = Set.univ := by
    refine Set.eq_univ_of_forall fun ρ => ?_
    show ¬ _ = false
    rw [offline_accepts_own_run d i x r e hy c ρ]
    exact Bool.noConfusion
  rw [all, pr_univ] at small
  exact absurd small (not_le.2 (pow_lt_one₀ (zero_le _) (ENNReal.inv_lt_one.2 (by norm_num)) (by norm_num)))

end AtPublicFiles.OneProtocol

#print axioms AtPublicFiles.OneProtocol.offline_rounds_few
#print axioms AtPublicFiles.OneProtocol.offline_work_small
#print axioms AtPublicFiles.OneProtocol.lost_is_rarely_accepted
#print axioms AtPublicFiles.OneProtocol.extractor_answers

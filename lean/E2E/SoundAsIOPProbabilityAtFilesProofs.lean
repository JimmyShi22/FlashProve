-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SoundAsIOPProbabilityAtFilesProofs.lean: the proofs of the statements of
E2E/SoundAsIOPProbabilityAtFiles.lean.

CALLS ALONE. What is spent:
  four_wiringAtFiles: the laws of the wires at Z, at every Z: wiresOfFullD
    (Johnson/Flat/Dec/WiresAtSizes.lean) from the frame's own test on numbers, fit_theLay
    (Johnson/Goal/Conditions/NumbersAtThe.lean), and entryFitB_dsFull_140.
  clearingIsTheWires: wholeRunDraw_cleared, RoundsQueryLayout.cleared_clearing (Hiop/SoundAsIOPClearing.lean).
  clearedPasses: RoundsQueryLayout.pass_zero, there.
  clearedIsUniformOnPassing: RoundsQueryLayout.clearedIsUniformOnPassing, there.
  (verifiersAskTheWork is proved in E2E/SoundAsIOPWorkIsTheVerifiers.lean.)
  probabilityAtFiles: wholeRunAtFiles (E2E/SoundAsIOPAtFilesProofs.lean), wholeRunSound_probability
    (Hiop/SoundAsIOPSum.lean), RoundsQueryLayout.clearing_atMostToOne, sumOfProbabilities_timesByRound_le.
  mostWorkAtFiles_le: mostWork_offlineWires | linkWires | onlineWires (Johnson/Flat/Dec/WorkOfWires.lean), and the same test on
    numbers.
  mostWorkAtFiles_ge: le_mostWork_linkWires, there, and one evaluation by Lean's kernel on the link's written
    data (link_has_32).
  clearingIsNotTheIdentity: that, the laws of the wires, and RoundsQueryLayout.exists_zero_ne.
  probabilityAtFiles64: the two.
  roundsAtFiles_le: the compiled verifier's own count of queries holds one for each round of the three
    parts and eight more (tVT | tVL | tVB_wireOfFullD, Johnson/Flat/Dec/CountAtFrame.lean), and the test on
    numbers bounds it by 2^20.
  probabilityAtFiles44: these.
  conclusionFails_provers: by unfolding how the object is made (OnBytes.Flat.Files.withProvers).
The limits are those of E2E/SoundAsIOPProbabilityAtFiles.lean's head.
-/
import E2E.SoundAsIOPProbabilityAtFiles
import E2E.SoundAsIOPAtFilesProofs
import Johnson.Flat.Dec.WorkOfWires
import Johnson.Flat.Dec.CountAtFrame
import Johnson.Goal.Conditions.NumbersAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace Iop

/-- The whole run has the rounds of the three parts and five more. -/
theorem HolographicProtocol.length_wholeRunShape {Index Request : Type} (L : HolographicProtocol Index Request) (fill : L.Fill) :
    (L.wholeRunShape fill).length =
      L.offline.shape.length + L.link.shape.length + L.onlineBatch.loc.shape.length + 5 := by
  simp only [HolographicProtocol.wholeRunShape, HolographicProtocol.tableRounds, List.length_append, List.length_cons,
    List.length_nil]
  omega

end Iop

namespace OnBytes.Prover
open _root_.Run
open OnBytes.Maker
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice
open OnBytes.K.Arm (cntWhole)

section Frame
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (depthReqT : ℕ)

/-- **The rounds of the three parts, and five, are at most the compiled verifier's own count of
queries**, at any data of rounds. -/
theorem rounds_le_count :
    ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).offline.shape.length +
      ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).link.shape.length +
      ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).onlineBatch.loc.shape.length
        + 5 ≤ cntFrameFullD DK DP ds xs depthReq depthReqT := by
  have hT : 2 + (((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty).sh.length + 1) + (nOpenW (DK.at frS.P.T.a) *
        (maxDepthW (DK.at frS.P.T.a) + 1) + (depthReqT + 1))) =
      cntWhole (DK.at frS.P.T.a) depthReqT :=
    tVT_wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P 0 depthReqT
  have hB : 2 + (((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty).sh.length + 1) + (nOpenW (DP.at frS.P.T.a) *
        (maxDepthW (DP.at frS.P.T.a) + 1) + (depthReq + 1))) =
      cntWhole (DP.at frS.P.T.a) depthReq :=
    tVB_wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P 0 depthReqT
  have hL : (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec).shape.length = ds.length + 1 :=
    length_linkW _ _ _ _ _
  show (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).sh.length +
      (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec).shape.length +
      (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).sh.length + 5 ≤ _
  unfold cntFrameFullD cntEntry
  rw [hL, ← hT, ← hB]
  omega

end Frame

end OnBytes.Prover

namespace AtPublicFiles.AtFiles
open Prob Hiop
open _root_.Iop (wholeRunDraw_cleared wholeRunClearing_atMostToOne wholeRunSound_probability
  sumOfProbabilities_timesByRound_le wholeRunToOne_eachAtMost Err.EachAtMost.mono
  HolographicProtocol.length_wholeRunShape)
open TypedOracleCompiler.Iop (RoundsQueryLayout.cleared_clearing RoundsQueryLayout.pass_zero RoundsQueryLayout.clearing_atMostToOne
  RoundsQueryLayout.clearedToOne_eachAtMost RoundsQueryLayout.mostWork RoundsQueryLayout.exists_zero_ne
  RoundsQueryLayout.clearedIsUniformOnPassing)
open TypedOracleCompiler.Compile.Batch.Cms (Four wLC)
open OnBytes.Flat OnBytes.Maker OnBytes.Prover
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles asDescriptionFiles InScope readFiles)
open FlashProve (dataAtFiles fit_theLay)
open FlashProve (flashProveData protocolDataWellFormed allZeroDigest)

/-- **The laws of the wires at Z**, at every Z. -/
theorem four_wiringAtFiles (Z : PublicFiles) : Four (wiringAtFiles Z) :=
  have f := frameFitFullD_parts (fit_theLay Z)
  have e := entryFit_of_test entryFitB_dsFull_140
  wiresOfFullD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f.hk f.hE.bL e.wLk e.own e.dL f.wK f.dK f.wP f.dP

theorem clearingIsTheWires : Statements.clearingIsTheWires := fun Z P fill ρ =>
  (wholeRunDraw_cleared ((filesAt Z).withProvers P) fill (offlineClearing Z) (linkClearing Z)
    (onlineClearing Z) ρ).trans
    (congrArg (Prod.mk (((filesAt Z).withProvers P).wholeRunDraw fill ρ).1)
      (Prod.ext (RoundsQueryLayout.cleared_clearing _ _ _ _)
        (Prod.ext (RoundsQueryLayout.cleared_clearing _ _ _ _) (RoundsQueryLayout.cleared_clearing _ _ _ _))))

theorem clearedPasses : Statements.clearedPasses := fun Z =>
  have four := four_wiringAtFiles Z
  ⟨fun ρ => (congrArg _ (RoundsQueryLayout.cleared_clearing _ _ _ ρ)).trans
      (RoundsQueryLayout.pass_zero _ _ _ four.2.1.sh ρ),
    fun ρ => (congrArg _ (RoundsQueryLayout.cleared_clearing _ _ _ ρ)).trans
      (RoundsQueryLayout.pass_zero _ _ _ four.2.2.1.sh ρ),
    fun ρ => (congrArg _ (RoundsQueryLayout.cleared_clearing _ _ _ ρ)).trans
      (RoundsQueryLayout.pass_zero _ _ _ four.2.2.2.sh ρ)⟩

theorem clearedIsUniformOnPassing : Statements.clearedIsUniformOnPassing := fun Z =>
  have four := four_wiringAtFiles Z
  ⟨RoundsQueryLayout.clearedIsUniformOnPassing _ _ _ four.2.1.sh,
    RoundsQueryLayout.clearedIsUniformOnPassing _ _ _ four.2.2.1.sh,
    RoundsQueryLayout.clearedIsUniformOnPassing _ _ _ four.2.2.2.sh⟩

theorem probabilityAtFiles : Statements.probabilityAtFiles :=
  fun Z pp scope read live P fill β prover => by
    obtain ⟨errors, below, sound⟩ := wholeRunAtFiles Z pp scope read live P fill
    have four := four_wiringAtFiles Z
    have toOne := wholeRunClearing_atMostToOne ((filesAt Z).withProvers P) fill
      (offline := offlineClearing Z) (link := linkClearing Z) (online := onlineClearing Z)
      (RoundsQueryLayout.clearing_atMostToOne _ _ _ four.2.1.sh)
      (RoundsQueryLayout.clearing_atMostToOne _ _ _ four.2.2.1.sh)
      (RoundsQueryLayout.clearing_atMostToOne _ _ _ four.2.2.2.sh)
    refine (wholeRunSound_probability _ _ _ _ errors fill β prover (clearingAtFiles Z P fill) _
      toOne sound).trans ?_
    exact sumOfProbabilities_timesByRound_le _ _ _ (2 ^ mostWorkAtFiles Z) _
      (wholeRunToOne_eachAtMost _ fill Nat.one_le_two_pow
        (Err.EachAtMost.mono (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
          (RoundsQueryLayout.clearedToOne_eachAtMost _ _ _))
        (Err.EachAtMost.mono
          (Nat.pow_le_pow_right (by decide) ((le_max_left _ _).trans (le_max_right _ _)))
          (RoundsQueryLayout.clearedToOne_eachAtMost _ _ _))
        (Err.EachAtMost.mono
          (Nat.pow_le_pow_right (by decide) ((le_max_right _ _).trans (le_max_right _ _)))
          (RoundsQueryLayout.clearedToOne_eachAtMost _ _ _)))
      below

theorem mostWorkAtFiles_le : Statements.mostWorkAtFiles_le := fun Z =>
  have f := frameFitFullD_parts (fit_theLay Z)
  have e := entryFit_of_test entryFitB_dsFull_140
  max_le (mostWork_offlineWires _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((WholeD.workFit_iff _).1 f.wK))
    (max_le (mostWork_linkWires _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e.wLk)
      (mostWork_onlineWires _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((WholeD.workFit_iff _).1 f.wP)))

/-- Some round of the written link has 32 bits of work. By Lean's kernel. -/
theorem link_has_32 : dsFull.any (fun d => decide (d.entry.work = 32)) = true := by decide +kernel

/-- So the link's wires at Z declare a round of at least 32 bits. -/
theorem linkWires_ge (Z : PublicFiles) :
    32 ≤ RoundsQueryLayout.mostWork (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh := by
  obtain ⟨d, hd, e⟩ := List.any_eq_true.1 link_has_32
  have e' : d.entry.work = 32 := of_decide_eq_true e
  exact e'.ge.trans (le_mostWork_linkWires _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d hd)

theorem mostWorkAtFiles_ge : Statements.mostWorkAtFiles_ge := fun Z =>
  (linkWires_ge Z).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem clearingIsNotTheIdentity : Statements.clearingIsNotTheIdentity := fun Z =>
  let ⟨ρ, h⟩ := RoundsQueryLayout.exists_zero_ne _ _ _ (four_wiringAtFiles Z).2.2.1.sh
    (Nat.lt_of_lt_of_le (by decide) (linkWires_ge Z))
  ⟨ρ, fun e => h ((RoundsQueryLayout.cleared_clearing _ _ _ ρ).symm.trans e)⟩

/-- 2^w * 2^-128 ≤ 2^-64 where w ≤ 64. -/
theorem work_times_bound {w : ℕ} (h : w ≤ 64) :
    ((2 ^ w : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  calc ((2 ^ w : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128
      ≤ ((2 ^ 64 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 :=
        mul_le_mul' (Nat.cast_le.2 (Nat.pow_le_pow_right (by decide) h)) le_rfl
    _ = (2 : ℝ≥0∞)⁻¹ ^ 64 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (128 : ℕ) = 64 + 64 from rfl, pow_add, ← mul_assoc,
          ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

theorem probabilityAtFiles64 : Statements.probabilityAtFiles64 :=
  fun Z pp scope read live P fill β prover =>
    (probabilityAtFiles Z pp scope read live P fill β prover).trans
      (mul_le_mul' le_rfl (work_times_bound (mostWorkAtFiles_le Z)))

theorem roundsAtFiles_le : Statements.roundsAtFiles_le := fun Z P fill => by
  rw [HolographicProtocol.length_wholeRunShape]
  exact (rounds_le_count _ _ _ _ _ _ _ _ _ _ _ _ _ _ P _).trans
    (frameFitFullD_parts (fit_theLay Z)).hcnt

theorem probabilityAtFiles44 : Statements.probabilityAtFiles44 :=
  fun Z pp scope read live P fill β prover =>
    (probabilityAtFiles64 Z pp scope read live P fill β prover).trans <|
      calc ((((filesAt Z).withProvers P).wholeRunShape fill).length : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 64
          ≤ ((2 ^ 20 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 64 :=
            mul_le_mul' (Nat.cast_le.2 (roundsAtFiles_le Z P fill)) le_rfl
        _ = (2 : ℝ≥0∞)⁻¹ ^ 44 := by
            rw [Nat.cast_pow, Nat.cast_ofNat, show (64 : ℕ) = 20 + 44 from rfl, pow_add,
              ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow,
              one_mul]

section
/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] filesAt offlineClearing linkClearing onlineClearing relationAtFiles

theorem conclusionFails_provers : Statements.conclusionFails_provers :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl⟩

end

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.four_wiringAtFiles
#print axioms AtPublicFiles.AtFiles.clearingIsTheWires
#print axioms AtPublicFiles.AtFiles.clearedPasses
#print axioms AtPublicFiles.AtFiles.clearedIsUniformOnPassing
#print axioms AtPublicFiles.AtFiles.probabilityAtFiles
#print axioms AtPublicFiles.AtFiles.mostWorkAtFiles_le
#print axioms AtPublicFiles.AtFiles.mostWorkAtFiles_ge
#print axioms AtPublicFiles.AtFiles.clearingIsNotTheIdentity
#print axioms AtPublicFiles.AtFiles.probabilityAtFiles64
#print axioms AtPublicFiles.AtFiles.roundsAtFiles_le
#print axioms AtPublicFiles.AtFiles.probabilityAtFiles44
#print axioms AtPublicFiles.AtFiles.conclusionFails_provers

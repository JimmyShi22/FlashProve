-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/TopAtZBinding.lean: AT ONE SET OF PUBLIC FILES Z, from the two hypotheses at that Z
alone: the goal with the level, and the two statements that read openings of the commitment.
Johnson/Goal/Skeleton/TopAtZ.lean states the top on soundness at one Z (`sound_at`), with
`SoundUnderPolicyAtZ D eps Z pp`, `KeySoundAt Z`, `ProofSoundAt Z`. Here are, over these, the forms
at one Z of the other tops of Johnson/Goal/TopOfTwo.lean. NO NEW MATHEMATICS: each proof is its
elder's own text with "for all Z" taken off the front.
  General in the description:
    `soundAndBinding_of_atZ`          `soundAndBinding_of_record` (Ladder/PackageTies.lean)
    `soundAndBinding_of_atZ_within`   `soundAndBinding_of_record_within` (Ladder/PackageBits.lean)
    `soundUnderPolicyAtZ_reBound`     `soundUnderPolicyAt_reBound` (Goal/Conditions/ReBound.lean)
  At `atSecondHashFunction theDescription`:
    `g8bits_at`: the two halves of `G8bits theDescription`, the second at Z.
  At `theBound K` (Johnson/Goal/Conditions/BindsAtThe.lean):
    `soundUnderPolicyAtZ_bits_theBound`   `soundUnderPolicyAt_bits_theBound` (SoundBitsAtThe.lean)
    `g8bits_bound_at` · `soundAndBinding_level_at` · `soundOpened_level_at`
  At `theWide K W` (Johnson/Goal/Conditions/WideAtThe.lean):
    `soundUnderPolicyAtZ_bits_theWide`    `soundUnderPolicyAt_bits_theWide` (WideBitsAtThe.lean)
    `soundAndBinding_at` · `soundOpened_at`
  `…_of_at`: the forms with "for all Z" back from these: so Lean holds that each end is the body of
  its nearest form at Z.
Limits. `KeySoundAt Z` and `ProofSoundAt Z` are premises, each itself an assumption of soundness:
nothing here shows that they can be met. The two that read openings are stated of two stand-in
descriptions that keep `theDescription`'s verifier and add a committer, not of `theDescription`: the
limits of Johnson/Goal/TopOfThreeBinding.lean travel whole. The binding half is a theorem at every
Z and is called at Z.

-/
import Johnson.Goal.Skeleton.TopAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- Remove the default instance `Inst.Model.Scl.ref`: no statement below may pick it up silently. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF GF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/-! ## General in the description -/

/-- `soundAndBinding_of_record` (Ladder/PackageTies.lean) from the body at one Z. -/
theorem soundAndBinding_of_atZ (D : Description) (epsS : ℕ → ℕ → ℝ≥0∞) (epsB : ℕ → ℝ≥0∞) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (sound : SoundUnderPolicyAtZ D epsS Z pp) (binds : BindsAt D epsB)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    SoundAndBinding (systemOfRecord D Z (settingsOfRead pp)) (joinError epsS epsB) := by
  have h1 := sound.2 D.Form (D.prove Z (settingsOfRead pp)) (D.parse Z) honestBudget sound.1
  have hb := (binds Z pp scope read).2
  rw [exact] at h1
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) (D.prove Z (settingsOfRead pp)) id
    (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput
    (fun w p o hm => ((Policy.meetsPolicy_exact_iff w p o).1 hm).2)
  have e : (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id) =
      D.extractor Z (settingsOfRead pp) := by
    funext c q
    simp
  have h3 : SoundForWith (systemOfRecord D Z (settingsOfRead pp))
      (D.extractor Z (settingsOfRead pp))
      (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput (fun t => epsS t honestBudget) :=
    e ▸ h2
  exact soundAndBinding_of_le _ _ _ _ _ h3 hb (fun _ => le_max_left _ _) (fun _ => le_max_right _ _)

/-- `soundAndBinding_of_record_within` (Ladder/PackageBits.lean) from the body at one Z. -/
theorem soundAndBinding_of_atZ_within (D : Description) (epsS : ℕ → ℕ → ℝ≥0∞) (epsB : ℕ → ℝ≥0∞)
    (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (sound : SoundUnderPolicyAtZ D epsS Z pp)
    (binds : BindsAt D epsB) (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (n : ℕ) (hn : Parser.Within (D.parse Z) n) :
    SoundAndBinding (systemOfRecord D Z (settingsOfRead pp)) fun t => max (epsS t n) (epsB t) := by
  have h1 := sound.2 D.Form (D.prove Z (settingsOfRead pp)) (D.parse Z) n hn
  have hb := (binds Z pp scope read).2
  rw [exact] at h1
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) (D.prove Z (settingsOfRead pp)) id
    (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput
    (fun w p o hm => ((Policy.meetsPolicy_exact_iff w p o).1 hm).2)
  have e : (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id) =
      D.extractor Z (settingsOfRead pp) := by
    funext c q
    simp
  have h3 : SoundForWith (systemOfRecord D Z (settingsOfRead pp))
      (D.extractor Z (settingsOfRead pp))
      (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput (fun t => epsS t n) :=
    e ▸ h2
  exact soundAndBinding_of_le _ _ _ _ _ h3 hb (fun _ => le_max_left _ _) (fun _ => le_max_right _ _)

/-- `soundUnderPolicyAt_reBound` (Goal/Conditions/ReBound.lean) at one Z. Stated at letters, then
called, so that Lean does not open the values. -/
theorem soundUnderPolicyAtZ_reBound {D : Description} (Q : HonestTerms D) (b : PublicFiles → ℕ)
    (coins' : (Z : PublicFiles) → Q.Rand → DeterministicAlgorithm (Fin (b Z + 1))) (eps : ℕ → ℕ → ℝ≥0∞)
    (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (sound : SoundUnderPolicyAtZ (D.withTerms Q) eps Z pp) :
    SoundUnderPolicyAtZ ((D.reBound b).withTerms (Q.reBound b coins')) eps Z pp :=
  ⟨sound.1, fun Form prove parse n hn => sound.2 Form prove parse n hn⟩

/-! ## At the name -/

/-- **The two halves of `G8bits theDescription`, the second at Z.** -/
theorem g8bits_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (kS : KeySoundAt Z) (pS : ProofSoundAt Z) :
    VerifierWithin (atSecondHashFunction theDescription) ∧
      SoundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries Z pp :=
  ⟨verifierIsWithin, soundUnderPolicyAtZ_of_two Z pp scope hr kS pS⟩

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8 theCoding theKeyData
  theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate theProvers theNamed
  LPFD.Full.GF FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins) (W : WideCoins K)

/-! ## At `theBound K` -/

/-- `soundUnderPolicyAt_bits_theBound` (Goal/Conditions/SoundBitsAtThe.lean) at one Z. -/
theorem soundUnderPolicyAtZ_bits_theBound (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) : SoundUnderPolicyAtZ (theBound K o) soundnessErrorInQueries Z pp :=
  have e := entryFit_of_test entryFitB_dsFull_140
  soundUnderPolicyAtZ_of_toldO_or (flashProveDescription.withTerms (theTerms K)) soundnessErrorInQueries Z pp
    ((publicReadingFitAtDescriptionOfFields (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀)
      allZeroDigest [] Z (settingsOfRead pp) _ (claimThe Z) _ _ _ _ (phiThe Z (settingsOfRead pp))
      (fun M => VerifiableInference.OnPublicFiles.phiAt (valid_of_read hr) M)
      (fun d => compilerSoundnessConditions_layoutsByPublicReading (dataAtFiles flashProveData Z) allZeroDigest [] (parts_the Z).hk (parts_the Z).hE.bL e.wLk
        e.own e.dL (parts_the Z).wK (parts_the Z).dK (parts_the Z).wP (parts_the Z).dP
        (keySound_theLay Z allZeroDigest [] kS) (entrySound_theLay Z allZeroDigest [] (entrySound Z scope))
        (proofSound_theLay Z allZeroDigest [] pS) d)
      (meaning_the Z) (carries_the Z pp hr)).withTerms (theTerms K))
    (parseDec_honest (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀ Z)
    rfl
    fun t n => (lt_or_ge (soundnessErrorInQueries t n) 1).imp
      (fun hb => frame_le_bits _ t n _ (he2_the Z scope)
        (le_trans (Nat.add_le_add_right
          (verifierQueryCountBound_descriptionDataAtFiles (dataAtFiles flashProveData Z) allZeroDigest [] theQueries (fit_theLay Z)) 9)
          (by unfold theQueries; norm_num)) hb) id

/-- The two halves of `G8bits (theBound K)`, the second at Z. -/
theorem g8bits_bound_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (kS : KeySoundAt Z) (pS : ProofSoundAt Z) :
    VerifierWithin (atSecondHashFunction (theBound K)) ∧ SoundUnderPolicyAtZ (atSecondHashFunction (theBound K)) soundnessErrorInQueries Z pp :=
  ⟨verifierWithin_theBound K _, soundUnderPolicyAtZ_bits_theBound K _ Z pp scope hr kS pS⟩

/-- **`SoundAndBinding` at one Z, at `theBound K`, at `levelError`**: the body of
`NearestSoundAndBinding (theBound K) levelError` at Z. -/
theorem soundAndBinding_level_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) :
    SoundAndBinding (systemOfRecord (atSecondHashFunction (theBound K)) Z (settingsOfRead pp)) levelError :=
  soundAndBinding_of_atZ_within _ soundnessErrorInQueries bindingErrorInQueries Z pp
    (g8bits_bound_at K Z pp scope hr kS pS).2 (G9bits_at K) scope hr exact verifierQueryAllowance
    (parserWithin_of_verifierWithin (g8bits_bound_at K Z pp scope hr kS pS).1 Z scope)

/-- **`SoundOpened` at one Z, at `theBound K`, at twice `levelError`.** -/
theorem soundOpened_level_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) :
    SoundOpened (systemOfRecord (atSecondHashFunction (theBound K)) Z (settingsOfRead pp)) fun t =>
      2 * levelError t :=
  soundOpened_of_soundAndBinding _ _ (soundAndBinding_level_at K Z pp scope hr exact kS pS)

/-! ## At `theWide K W` -/

/-- `soundUnderPolicyAt_bits_theWide` (Goal/Conditions/WideBitsAtThe.lean) at one Z. -/
theorem soundUnderPolicyAtZ_bits_theWide (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (kS : KeySoundAt Z) (pS : ProofSoundAt Z) :
    SoundUnderPolicyAtZ ((flashProveDescription.reBound W.bound).withTerms (theWideTerms K W)) soundnessErrorInQueries Z pp :=
  soundUnderPolicyAtZ_reBound (theTerms K) W.bound _ soundnessErrorInQueries Z pp
    (soundUnderPolicyAtZ_bits_theBound K OnBytes.secondHashFunction Z pp scope hr kS pS)

/-- **`SoundAndBinding` at one Z, at `theWide K W`**: the body of its nearest form at Z. -/
theorem soundAndBinding_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) :
    SoundAndBinding (systemOfRecord (atSecondHashFunction (theWide K W)) Z (settingsOfRead pp))
      (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) :=
  soundAndBinding_of_atZ _ soundnessErrorInQueries _ Z pp (soundUnderPolicyAtZ_bits_theWide K W Z pp scope hr kS pS)
    (bindsAt_withTerms (theWideTerms K W) 8 2 fun Z pp _ h₂ => bindLaws_wide K W Z pp h₂) scope hr
    exact

/-- **`SoundOpened` at one Z, at `theWide K W`**, at twice that error. -/
theorem soundOpened_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) :
    SoundOpened (systemOfRecord (atSecondHashFunction (theWide K W)) Z (settingsOfRead pp)) fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t :=
  soundOpened_of_soundAndBinding _ _ (soundAndBinding_at K W Z pp scope hr exact kS pS)

/-! ## The forms with "for all Z", back: nothing is lost, and each end is its form's body at Z -/

section Back
variable (kS : ∀ Z, InScope Z = true → KeySoundAt Z) (pS : ∀ Z, InScope Z = true → ProofSoundAt Z)
include kS pS

theorem g8bits_of_at : G8bits theDescription :=
  ⟨verifierIsWithin, fun Z pp scope hr => (g8bits_at Z pp scope hr (kS Z scope) (pS Z scope)).2⟩

theorem g8bits_bound_of_at : G8bits (theBound K) :=
  ⟨verifierWithin_theBound K _,
    fun Z pp scope hr => (g8bits_bound_at K Z pp scope hr (kS Z scope) (pS Z scope)).2⟩

theorem top_soundAndBinding_level_of_at : NearestSoundAndBinding (theBound K) levelError :=
  fun Z pp scope hr exact =>
    soundAndBinding_level_at K Z pp scope hr exact (kS Z scope) (pS Z scope)

theorem top_soundOpened_level_of_at : NearestSoundOpened (theBound K) fun t => 2 * levelError t :=
  fun Z pp scope hr exact => soundOpened_level_at K Z pp scope hr exact (kS Z scope) (pS Z scope)

theorem top_soundAndBinding_of_at :
    NearestSoundAndBinding (theWide K W) (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) :=
  fun Z pp scope hr exact => soundAndBinding_at K W Z pp scope hr exact (kS Z scope) (pS Z scope)

theorem top_soundOpened_of_at :
    NearestSoundOpened (theWide K W) fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t :=
  fun Z pp scope hr exact => soundOpened_at K W Z pp scope hr exact (kS Z scope) (pS Z scope)

end Back

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.soundAndBinding_of_atZ
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_of_atZ_within
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_reBound
#print axioms VerifierAndGoals.AtTheName.g8bits_at
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_bits_theBound
#print axioms VerifierAndGoals.AtTheName.g8bits_bound_at
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_at
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_bits_theWide
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_at
#print axioms VerifierAndGoals.AtTheName.g8bits_of_at
#print axioms VerifierAndGoals.AtTheName.g8bits_bound_of_at
#print axioms VerifierAndGoals.AtTheName.top_soundAndBinding_level_of_at
#print axioms VerifierAndGoals.AtTheName.top_soundOpened_level_of_at
#print axioms VerifierAndGoals.AtTheName.top_soundAndBinding_of_at
#print axioms VerifierAndGoals.AtTheName.top_soundOpened_of_at

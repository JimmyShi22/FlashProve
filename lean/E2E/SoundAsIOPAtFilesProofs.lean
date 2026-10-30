-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SoundAsIOPAtFilesProofs.lean: the proofs of the statements of E2E/SoundAsIOPAtFiles.lean.

CALLS ALONE. What is spent:
  soundAsIOPAtFiles: VerifierAndGoals.AtTheName.keySound_holds (offline), FlashProve.entrySound (link),
    VerifierAndGoals.AtTheName.proofSoundAt_of_verify (online), OnBytes.Flat.Files.obj_noneColl,
    OnBytes.Flat.entryFull_record with OnBytes.Flat.samplePoint_small (the round of a sample's point),
    and Iop.soundInParts_iff_soundAtR.
  wholeRunAtFiles: that, and Iop.wholeRunSound_of_indexKnowledgeSoundIOP.
  relationMeans: VerifierAndGoals.AtTheName.meaning, VerifierAndGoals.AtTheName.carries.
  compilerPremises: indexKnowledgeSoundIOP_iff_premises (Johnson/Top/SoundAsIOPIsThePremise.lean), at the
    compiler's input rZ Z.
  soundOfVerifyThroughIOP: compilerPremises, and then the chain of VerifierAndGoals.AtTheName.sound_at
    (Johnson/Goal/Skeleton/TopAtZ.lean) to the letter, with the link's row too taken from the
    premise: soundUnderPolicyAtZ_numbers, sound_of_atZ.
  sound_of_verify_at_through_the_IOP: the statement of VerifierAndGoals.AtTheName.sound_of_verify_at, proved
    through SoundAsIOPAtFiles.
The limits are those of E2E/SoundAsIOPAtFiles.lean's head.
-/
import E2E.SoundAsIOPAtFiles
import E2E.SamplePointSmall
import Hiop.SoundAsIOPProofs
import Johnson.Top.SoundAsIOPIsThePremise

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop
open OnBytes.Flat (Files)
open VerifiableInference VerifiableInference.OnPublicFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles asDescriptionFiles InScope readFiles settingsOfRead systemOfRecord atSecondHashFunction theDescription)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open VerifierAndGoals.AtTheName (rZ bZ)

/-! ## No clause reads a prover -/

/-- Soundness in parts of the object of three protocols does not depend on the provers. -/
theorem soundInParts_provers {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P P' : F.Provers)
    (relation : C.I → C.X → Prop) (e : ℕ) (εT : Err F.key.shape) (εL : Err F.entry.shape)
    (εB : Err F.proof.shape) (h : (F.withProvers P).SoundInParts relation ⟨e, εT, εL, εB⟩) :
    (F.withProvers P').SoundInParts relation ⟨e, εT, εL, εB⟩ :=
  ⟨h.nothingAtCollision, h.samplePoint, h.offline, h.link, h.online⟩

/-- Nor does the bound on the errors. -/
theorem within_provers {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P P' : F.Provers) (e : ℕ)
    (εT : Err F.key.shape) (εL : Err F.entry.shape) (εB : Err F.proof.shape)
    (aT : RoundSplits F.key.shape) (nT : ℕ) (aL : RoundSplits F.entry.shape) (nL : ℕ) (bound : ℝ≥0∞)
    (h : HolographicProtocol.RoundErrors.Within (L := F.withProvers P) ⟨e, εT, εL, εB⟩ aT nT aL nL bound) :
    HolographicProtocol.RoundErrors.Within (L := F.withProvers P') ⟨e, εT, εL, εB⟩ aT nT aL nL bound :=
  ⟨h.samplePoint, h.offline, h.link, h.online⟩

/-- So soundness as an IOP at Z is one statement for all provers. -/
theorem soundAsIOPAtFiles_provers (Z : PublicFiles) (P P' : (filesAt Z).Provers)
    (h : SoundAsIOPAtFiles Z P) : SoundAsIOPAtFiles Z P' := by
  obtain ⟨⟨e, εT, εL, εB⟩, within, parts⟩ := h
  exact ⟨⟨e, εT, εL, εB⟩, within_provers (filesAt Z) P P' e εT εL εB _ _ _ _ _ within,
    soundInParts_provers (filesAt Z) P P' _ e εT εL εB parts⟩

/-! ## It holds -/

/-- The round of a sample's point at Z: every table has a collision at few points. -/
theorem collisions_few (Z : PublicFiles) (table : Fin (Cz Z).n → (Cz Z).Sg) :
    cnt (fun point => (Cz Z).coll table point) ≤
      OnBytes.Slice.recER OnBytes.Slice.recT OnBytes.Params.recordRadius OnBytes.Slice.recLg
        OnBytes.Slice.recS :=
  OnBytes.Flat.entryFull_record _ _ table

/-- And that count is at most 2^-128 of all points. -/
theorem collisions_share (Z : PublicFiles) :
    ((OnBytes.Slice.recER OnBytes.Slice.recT OnBytes.Params.recordRadius OnBytes.Slice.recLg
        OnBytes.Slice.recS : ℕ) : ℝ≥0∞) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 128 * (Fintype.card (Cz Z).Seed : ℝ≥0∞) :=
  OnBytes.Flat.samplePoint_small _ _

/-- At the placeholder provers. -/
theorem soundAsIOPAtFiles_silent (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    SoundAsIOPAtFiles Z (filesAt Z).fixedMessageProvers := by
  obtain ⟨εT, bT, sT⟩ := VerifierAndGoals.AtTheName.keySound_holds Z scope live
  obtain ⟨εL, bL, sL⟩ := FlashProve.entrySound Z scope live
  obtain ⟨wit, εB, bB, sB⟩ := VerifierAndGoals.AtTheName.proofSoundAt_of_verify Z pp scope read live
  refine ⟨⟨OnBytes.Slice.recER OnBytes.Slice.recT OnBytes.Params.recordRadius OnBytes.Slice.recLg
    OnBytes.Slice.recS, εT, εL, εB⟩, ⟨collisions_share Z, bT, bL, bB⟩, ?_⟩
  exact (soundInParts_iff_soundAtR _ _ _ _ _).2
    ⟨(filesAt Z).obj_noneColl _, collisions_few Z, sT, sL, sB⟩

theorem soundAsIOPAtFiles : Statements.soundAsIOPAtFiles :=
  fun Z pp scope read live P =>
    soundAsIOPAtFiles_provers Z _ P (soundAsIOPAtFiles_silent Z pp scope read live)

theorem soundAsIOPAtTheProtocol : Statements.soundAsIOPAtTheProtocol :=
  fun Z pp scope read live => soundAsIOPAtFiles Z pp scope read live _

theorem wholeRunAtFiles : Statements.wholeRunAtFiles :=
  fun Z pp scope read live P fill =>
    wholeRunSound_of_indexKnowledgeSoundIOP _ _ _ _ _ _ _ _ _ fill rfl (Nat.two_pow_pos _)
      (Nat.two_pow_pos _) Nat.one_pos (soundAsIOPAtFiles Z pp scope read live P)

/-! ## The compiler's theorem goes through it -/

theorem compilerPremises : Statements.compilerPremises := fun Z h =>
  have all := (indexKnowledgeSoundIOP_iff_premises (rZ Z) (bZ Z) () fun _ => rfl).1 h
  ⟨all.1, all.2.1, all.2.2.1, all.2.2.2.1⟩

end AtPublicFiles.AtFiles

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open AtPublicFiles.AtFiles (SoundAsIOPAtFiles filesAt)

theorem relationMeans : AtPublicFiles.AtFiles.Statements.relationMeans :=
  fun Z pp scope read matrix prompt output more request built holds =>
    carries Z pp scope read matrix prompt output
      (meaning Z scope matrix (prompt, output) more request built ⟨(), holds⟩)

theorem soundOfVerifyThroughIOP : AtPublicFiles.AtFiles.Statements.soundOfVerifyThroughIOP :=
  fun Z pp scope read exact t0 =>
    sound_of_atZ _ _ Z pp
      (soundUnderPolicyAtZ_numbers theC0 theM0 Z pp
        (thePhiO Z (settingsOfRead pp) (valid_of_read read))
        (thePsi Z (settingsOfRead pp) (valid_of_read read)) soundnessErrorInQueries
        (fun live => (AtPublicFiles.AtFiles.compilerPremises Z (t0 live)).2.1)
        (fun live => (AtPublicFiles.AtFiles.compilerPremises Z (t0 live)).2.2.1)
        (fun live => (AtPublicFiles.AtFiles.compilerPremises Z (t0 live)).2.2.2)
        (theClaim Z) (meaning Z scope) (carries Z pp scope read) (hext Z pp scope read)
        fun t n => (lt_or_ge (soundnessErrorInQueries t n) 1).imp (errorAtBits Z scope t n) id)
      exact _ _ _ 1 (theDescription_within _ Z)

/-- **The statement of sound_of_verify_at, to the letter, proved through soundness as an IOP.** -/
theorem sound_of_verify_at_through_the_IOP (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  soundOfVerifyThroughIOP Z pp scope read exact fun live =>
    AtPublicFiles.AtFiles.soundAsIOPAtFiles Z pp scope read live _

end VerifierAndGoals.AtTheName

#print axioms AtPublicFiles.AtFiles.soundAsIOPAtFiles
#print axioms AtPublicFiles.AtFiles.soundAsIOPAtTheProtocol
#print axioms AtPublicFiles.AtFiles.wholeRunAtFiles
#print axioms AtPublicFiles.AtFiles.compilerPremises
#print axioms VerifierAndGoals.AtTheName.relationMeans
#print axioms VerifierAndGoals.AtTheName.soundOfVerifyThroughIOP
#print axioms VerifierAndGoals.AtTheName.sound_of_verify_at_through_the_IOP

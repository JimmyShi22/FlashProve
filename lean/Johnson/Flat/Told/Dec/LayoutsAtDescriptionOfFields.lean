-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFields.lean: a twin, made by program, of a file that is not in this library,
  over DescriptionDataAtFiles (Johnson/Goal/Tie/DescriptionOnDecodedProof.lean) | DescriptionFields | descriptionOfFields (DescribeT.lean)
  (DescriptionDataAtFiles has the field dec behind runP; its types are the D-names at dsF
  xsF dec) and Johnson/Flat/Told/Dec/TAtLaws.lean.
The original is not in this library; the declared names are the original's.  All else, who
  reads each letter, and every limit: as the original's head says.
That head's sentences on this, word for word, since that file is not in this library
  (they are written of that file's statements, in its names):
  Who reads each letter. c₀ m₀: the fit's R alone. H: nothing here reads it but the description's
    type. No ∃.
  These three are what bars a hollow record: with D := Unit and a reading that asks nothing, «reads»
    fails at every description that asks the hash function and lays its answers into pair; with true
    digests typed as constants into m, «fits» fails at every (c, m) but one.
  No verifier is judged: the silly members have nothing to meet.
DescriptionDataAtFiles has a field G : FilesParameters XF RecFull: «S.G» stands where a variant
  that is not in this library has «(GF Zk)».
`fits_descriptionOfFields` hands `fitsD` the letter `(S Z).it`.
No soundness is claimed.
-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles
import Johnson.Flat.Told.Reads
import Johnson.PV.Fit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF sBG sTG saltG KF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) (c₀ : Digest) (m₀ :
                                                                            List (Dig 256))

/-- The told record, at the description's own input. -/
def layoutsByPublicReadingAtDescriptionOfFields (Z : PublicFiles) : LayoutsByPublicReading ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀) := (S
                                                                                    Z).layoutsByPublicReading c₀ m₀

/-- (1) **fits.** -/
theorem fits_descriptionOfFields (Z : PublicFiles) (c : Digest) (m : List (Dig 256)) (commitment : Commitment) (prompt
                           output : List Token)
    (proof : TypedProof ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).F Z) ((descriptionOfFields (fun Z => (S
                                          Z).toDescriptionFields) H).P Z)) :
    innerCompiledVerifier ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c m) commitment prompt output proof =
      innerCompiledVerifier ((layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z).at (c, m)) commitment prompt output proof :=
  LPFD.Full.fitsD (S Z).A (S Z).E (S Z).G (S Z).DK (S Z).DP (S Z).runK (S Z).runP (S Z).dec (S Z).P
      (S Z).hStar (S Z).it (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay (S Z).sR (S Z).hDK (S
                                       Z).hDP (S Z).hK (S Z).N (S Z).d₀ (c₀, m₀) (c, m) commitment prompt output proof

/-- (2) **reads**, at pair := Prod.mk. -/
theorem reads_descriptionOfFields (Z : PublicFiles) (hash : VerifiableInference.Hash) :
    (Fit.readBoth (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) Z c₀ m₀ (layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z)
        Prod.mk).evaluate hash =
      (layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z).Pub.det fun _ => hash :=
  Told.reads_pub8 Z hash

/-- (3) **hq₀**: the two readings ask at most eight times. -/
theorem readingsQueryBound_descriptionOfFields (Z : PublicFiles) :
    (Fit.readBoth (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) Z c₀ m₀ (layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z)
        Prod.mk).toRandomized.QueryBound 8 :=
  Told.within8_pub8 Z

end FlashProve

#print axioms FlashProve.layoutsByPublicReadingAtDescriptionOfFields
#print axioms FlashProve.fits_descriptionOfFields
#print axioms FlashProve.reads_descriptionOfFields
#print axioms FlashProve.readingsQueryBound_descriptionOfFields

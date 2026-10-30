-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/RowsAtTheRecord.lean: THE ROWS ON SOUNDNESS, STATED AT THE RECORD
`(dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0`. Definitions, and those of the rows that are theorems there.

Nine closed statements (namespace `VerifierAndGoals.AtTheName`), each at the letters' values of
Johnson/Goal/Description/Letters.lean and at every Z in scope. The first seven are written after
the premises of `G8_theDescription_numbers` (Johnson/Goal/Conditions/NumbersAtThe.lean), at these
values and at the error `VerifierAndGoals.soundnessErrorInQueries` (Ladder/Bits.lean: 16 / 2^128 for each query); no theorem of
this file says that they are these premises.
  `KeySound`, `EntrySound`, `ProofSound`: the three hypotheses on soundness (`CompilerSoundnessConditionStatements.keySound`,
    `entrySound`, `proofSound`), asked where `protocolDataWellFormed` says yes.
  `Meaning`: a witness of the named relation gives the claim.
  `Carries`: the claim gives weights that meet the files' policy.
  `Hext`: the extractor is the told record's, followed by the map from indices to weights.
  `ErrorAtBits`: the frame's error is at most `soundnessErrorInQueries`, WHEREVER `soundnessErrorInQueries` IS BELOW 1. Asked at all t
    and n it would be false: the frame's square term has the coefficient 50 where `soundnessErrorInQueries` has 1.
  `RoundErrorSmall`, `CountSmall`: two plain rows that give it (`errorAtBits_of_step`): the NAMED
    bound on a round's error is at most 2 / 2^128; the compiled verifier's own count is at most
    2^23 - 9.

Theorems at the record.
  `roundErrorSmall` (`eps_the`): by the named side's definition. It says nothing of the protocol:
    the weight lies in the three rows on soundness AT that number.
  `countSmall` (`count_the`): by the frame's own test on numbers, which fails closed.
  `errorAtBits`: so the row on the error is a theorem.
  `carries`: by `carriesPolicyO`.
  `input_W`, `queryBound_asks`, `readMore_built`: tools for whoever counts a description's queries.
So five are left here (Limits, 1): `KeySound`, `EntrySound`, `ProofSound`, `Meaning`, `Hext`.

No declaration of this file names `VerifierAndGoals.theDescription`. How the top rows follow from these at
that name is not in this file.

Limits. (1) THE FORM ALONE: of no row on soundness is it shown here that it holds. The three
decisions' seats in `flashProveData` are filled; the provers and the honest side are place-holders
(Johnson/Goal/Description/Description.lean's head). Elsewhere
in this library: `KeySound` is `keySound_holds` (KeyOpenHolds.lean, in this folder); `EntrySound` is
`FlashProve.entrySound` (EntrySits.lean); `ProofSound`'s row at each Z in scope whose files are
read is `proofSoundAt_of_verify` (Johnson/Goal/Skeleton/SoundOfVerifyMore.lean; of the verifier with
fourteen entry tests); `Meaning` and `Hext` are `VerifierAndGoals.AtTheName.meaning` and
`VerifierAndGoals.AtTheName.hext` (Johnson/Goal/TopOfThree.lean). The three rows on soundness ask their body
only where the live test says yes. That it says yes is proved at the library's written copies of the
public files (`theLive_zFull`, AtFullSide/Top/LiveAtFull.lean; `theLive_zGap` and, within four
bounds on the policy, `theLive_zAt`, LiveAtPolicies.lean beside it: a side library), not at the
release's files as bytes; and its yes is no sign that `verify` accepts any proof; `Meaning` and
`Hext` hold outright. `ProofSound` as typed here, at every Z in scope, is `proofSound_of_verify`
(Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean): files in scope are read. Of no verifier that runs
is it shown here that it is sound. (2) `ErrorAtBits` forces the named bound on a round's error to
about 3 / 2^128: that the rows are met together is not shown here; on the three rows on soundness
see (1). (3) Without "`protocolDataWellFormed` says yes at the release's files" the three rows on soundness ask
nothing.

-/
import Johnson.Goal.Conditions.NumbersAtThe
import Johnson.Goal.Description.Letters
import Ladder.BitsOfStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

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
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8 flashProveData

def KeySound : Prop :=
  ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))

def EntrySound : Prop :=
  ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))

def ProofSound : Prop :=
  ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))

def Meaning : Prop :=
  ∀ Z, InScope Z = true → ∀ i (x' : List Token × List Token) a x,
    ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).build x' a = some x →
    (∃ w, (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)).Rno i x w) →
      theClaim Z i x'.1 x'.2

def Carries : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
    ∀ i prompt output, theClaim Z i prompt output →
      ∃ w, thePhiO Z (settingsOfRead pp) (valid_of_read hr) i = some w ∧
        Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output

def Hext : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
    (dataAtFiles flashProveData Z).ext (settingsOfRead pp) = fun commitment queryLog =>
      (((dataAtFiles flashProveData Z).layoutsByPublicReading theC0 theM0).extractor commitment queryLog).bind
        (thePhiO Z (settingsOfRead pp) (valid_of_read hr))

def ErrorAtBits : Prop :=
  ∀ Z, InScope Z = true → ∀ t n, soundnessErrorInQueries t n < 1 →
    soundnessBoundOverTypedOracles ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).W
        (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)).εs (t + (8 + n)) 0 +
      epsCode (t + (8 + n)) ≤ soundnessErrorInQueries t n

/-! ## The row on the error, from two plain rows -/

/-- number_prices with number_eps_named: the named bound on a round's error is at most 2 / 2^128. -/
def RoundErrorSmall : Prop :=
  ∀ Z, InScope Z = true →
    (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)).εs ≤ 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹

/-- tVC_wireOfFullD with an evaluation: the compiled verifier's own count is at most 2^23 - 9. -/
def CountSmall : Prop :=
  ∀ Z, InScope Z = true → tVC ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).W + 9 ≤ 2 ^ 23

/-- **A round's error of at most 2 / 2^128 and a count of at most 2^23 - 9 give the row on the
error**: by `VerifierAndGoals.frame_le_bits` (Ladder/BitsOfStep.lean). -/
theorem errorAtBits_of_step (hR : RoundErrorSmall) (hV : CountSmall) : ErrorAtBits :=
  fun Z hZ t n hb => frame_le_bits _ t n _ (hR Z hZ) (hV Z hZ) hb

/-! ## The two plain rows at the name -/

/-- The compiled verifier's own count at the name, at every Z, c and m: at most 2^20, by the frame's
own test on numbers, which fails closed (`fit_theLay`), and `tVC_wireOfFullD`. -/
theorem count_the (Z : PublicFiles) (c : Digest) (m : List (Dig 256)) :
    tVC ((dataAtFiles flashProveData Z).inputFieldsAtReadings c m).W ≤ 2 ^ 20 := by
  have h := (frameFitFullD_parts (fit_theLay Z)).hcnt
  have e : tVC ((dataAtFiles flashProveData Z).inputFieldsAtReadings c m).W =
      cntFrameFullD (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP dsFull frD.xs
        (dataAtFiles flashProveData Z).G.c.first.binding.logLeaves
        (dataAtFiles flashProveData Z).G.k.oneTime.binding.logLeaves := tVC_wireOfFullD ..
  rw [e]
  exact h

theorem countSmall : CountSmall := fun Z _ => by
  have h := count_the Z theC0 theM0
  omega

/-- The wire of the built description's input is that of the T at the two readings: at a letter
L. -/
theorem input_W (L : FlashProve.DescriptionData) (Z : PublicFiles) (c : Digest) (m : List (Dig 256)) :
    tVC ((descriptionOfDataOnBytes L).input Z c m).queryLayout = tVC ((dataAtFiles L Z).inputFieldsAtReadings c m).W := rfl

/-- `VerifierAndGoals.askList` asks as often as the list is long. -/
theorem queryBound_asks : ∀ l : List BitString, (VerifierAndGoals.askList l).toRandomized.QueryBound l.length
  | [] => trivial
  | _ :: l => fun a => by
      have h := queryBound_andThen (VerifierAndGoals.askList l)
        (fun r => (DeterministicAlgorithm.done (a :: r) : DeterministicAlgorithm (List Digest)))
        l.length 0 (queryBound_asks l) fun _ => trivial
      rw [← Fit.andThen_eq] at h
      simpa using h

/-- The built description's further public reading: at a letter L. -/
theorem readMore_built (L : FlashProve.DescriptionData) (Z : PublicFiles) (c : Digest) :
    (descriptionOfDataOnBytes L).readMore Z c =
      VerifierAndGoals.askList (ssOf (par7 recordGround Z.pol Z.KL Z.lay) c) := rfl

end VerifierAndGoals.AtTheName

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD

/-- The NAMED bound on a round's error at the name is 1 / 2^128: BY DEFINITION of the named side. It
says nothing of the protocol: that every round's error is at most that number is what KeySound,
EntrySound and ProofSound say. (flashProveData is opened here.) -/
theorem eps_the (Z : PublicFiles) :
    (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)).εs = (2 : ENNReal)⁻¹ ^ 128 := rfl

theorem roundErrorSmall : RoundErrorSmall := fun Z _ => by
  rw [eps_the, ← ENNReal.inv_pow]
  exact le_mul_of_one_le_left (zero_le _) (by norm_num)

/-- **The row on the error is a theorem at the name.** -/
theorem errorAtBits : ErrorAtBits := errorAtBits_of_step roundErrorSmall countSmall

/-! ## Two rows more that are theorems at the name -/

/-- **`Carries` is a theorem at the name**: by `carriesPolicyO`
(Johnson/PV/DescribeO.lean). -/
theorem carries : Carries :=
  fun _ _ _ hr i prompt output ⟨lawful, h⟩ =>
    carriesPolicyO (ppAtFiles_of_read hr) lawful (valid_of_read hr) i prompt output h

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.carries
#print axioms VerifierAndGoals.AtTheName.errorAtBits
#print axioms VerifierAndGoals.AtTheName.errorAtBits_of_step
#print axioms VerifierAndGoals.AtTheName.roundErrorSmall
#print axioms VerifierAndGoals.AtTheName.countSmall
#print axioms VerifierAndGoals.AtTheName.count_the
#print axioms VerifierAndGoals.AtTheName.queryBound_asks

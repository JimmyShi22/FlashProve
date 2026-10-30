-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/DoorText.lean: THE GOALS' DESCRIPTION AS A FUNCTION OF WHAT IS LAID FOR THE PROOF
FILE, WRITTEN OUT. Ordinary definitions and theorems, with fifteen checks.

Why. The goals speak of `VerifierAndGoals.theDescription`. It takes the proof file's description through one
definition, `LPFD.Full.proofDataAndDecisionOfPublicFiles` ("the door" in this file; Unguarded.lean, limit 2, says the word of
`proofDataAndDecisionOrRefusalAt`, which only calls it). On the way, `VerifierAndGoals.theDescription` itself counted, lie 21
constants of the library: fifteen definitions, five theorems and one proof that Lean names itself
(gathered from Lean's own terms by a program, DoorMaker.lean [not in this library]). Here the twenty
that have a text are written once more, each with a letter `door` in the door's place and with these
twins in the others' places. IN THE TWENTY DECLARATIONS' TOKENS NOTHING ELSE IS TURNED: each text is
the library's, from the file that is named above it. Around them some lines differ: the docstrings
are left out, the opens are gathered by section, `attribute [local irreducible]` of Description.lean
is not repeated, and all stands in one `noncomputable section`. That each of the fifteen definitions
is still equal to the library's at the door is what the fifteen equations below say; the five
theorems' twins have no check here. So a reader can see what stands between the goals' description
and what is laid for the proof file, and that none of these twenty names the guard on the reply.
What lies beneath the names that they do name is not seen here.

Main names.
* `Door`: the door's type.
* `Text.theProofLaidAt door` … `Text.theDescription door`: the twins.
* `…_at`: for each of the fifteen definitions: the library's constant is its twin at
  `LPFD.Full.proofDataAndDecisionOfPublicFiles`. The first nine by `rfl`; the tenth, `theLay₀At_at`, by unfolding both sides
  once; the last five by unfolding and the equations before them. The last: `theDescription_at`.

Limits. The checks say that each of the library's fifteen definitions and its twin at the door are
equal; that the TEXTS are alike but for the letter is for the eye, or for a program. No theorem here
speaks of the guard. No goal of the release is named or stated. Nothing on soundness, completeness
or hiding.


-/
import Johnson.Goal.Description.Description

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace LPFGuard.Text

/-! ### Johnson/Goal/Description/ProofFold.lean, Live.lean, Gates.lean, Named.lean -/

section
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR)
open PV.EntryFive (dsF xsF)
open FlashProve (roundsDataFit fit3_iff emptyRoundsData)
open FlashProve

/-- The type of what is laid for the proof file: from o, a function in the place of the format's
second hash, and the bytes of the three public files, the data and the decision, or a refusal. -/
abbrev Door : Type :=
  VerifierAndGoals.SecondHashFunctionType → ByteArray → ByteArray → ByteArray →
    Except String (WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool))

variable (door : Door)

def theProofLaidAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) :
    Except String (WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)) :=
  door o Zk.pol Zk.lay Zk.KL

def theProofDataAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : WholeD :=
  match theProofLaidAt door o Zk with
  | .ok p => p.1
  | .error _ => FlashProve.emptyRoundsData

def theProofRunAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : XF × RecFull → PQ.View → PQ.View →
    PQ.View → Bool :=
  match theProofLaidAt door o Zk with
  | .ok p => p.2
  | .error _ => fun _ _ _ _ => false

theorem theProofDataAt_ok {o : VerifierAndGoals.SecondHashFunctionType} {Zk : OnBytes.K.Pub}
    {p : WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : theProofLaidAt door o Zk = .ok p) : theProofDataAt door o Zk = p.1 := by
  unfold theProofDataAt
  rw [h]

def theLiveAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : Bool :=
  match filesParametersOrRefusalAt o Zk with
  | .error _ => false
  | .ok G =>
    match keyDataAndDecisionOrRefusalAt o Zk with
    | .error _ => false
    | .ok K =>
      match theProofLaidAt door o Zk with
      | .error _ => false
      | .ok P => dataWellFormedAtFullSizeDepth G K.1 P.1

theorem theLiveAt_made (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : theLiveAt door o Zk = true) :
    ∃ K P, filesParametersOrRefusalAt o Zk = .ok (thePlanAt o Zk) ∧ keyDataAndDecisionOrRefusalAt o Zk = .ok K ∧
      theProofLaidAt door o Zk = .ok P ∧ dataWellFormedAtFullSizeDepth (thePlanAt o Zk) K.1 P.1 = true := by
  unfold theLiveAt at h
  cases hG : filesParametersOrRefusalAt o Zk with
  | error e => rw [hG] at h; cases h
  | ok G =>
    rw [hG] at h
    rw [thePlanAt_ok hG]
    cases hK : keyDataAndDecisionOrRefusalAt o Zk with
    | error e => rw [hK] at h; cases h
    | ok K =>
      rw [hK] at h
      cases hP : theProofLaidAt door o Zk with
      | error e => rw [hP] at h; cases h
      | ok P => rw [hP] at h; exact ⟨K, P, rfl, rfl, rfl, h⟩

theorem theLiveAt_of (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : theLiveAt door o Zk = true) :
    dataWellFormedAtFullSizeDepth (thePlanAt o Zk) (theKeyDataAt o Zk) (theProofDataAt door o Zk) = true := by
  obtain ⟨K, P, _, hK, hP, hl⟩ := theLiveAt_made door o Zk h
  rw [theKeyDataAt_ok hK, theProofDataAt_ok door hP]
  exact hl

theorem theLiveAt_frame (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : theLiveAt door o Zk = true) :
    sizeNumbersFitAtPlan KF theQueries (thePlanAt o Zk) (theKeyDataAt o Zk) (theProofDataAt door o Zk) =
      true := by
  have hl := theLiveAt_of door o Zk h
  simp only [dataWellFormedAtFullSizeDepth, dataWellFormedApartFromDepth, Bool.and_eq_true] at hl
  exact hl.2.1

theorem theLiveAt_fit (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : theLiveAt door o Zk = true) :
    roundsDataFit (theKeyDataAt o Zk) (theProofDataAt door o Zk) = true :=
  (fit3_iff _ _).2 (frameFitFullD_three (show sizeNumbersFitAtFullSize _ _ _ _ _ _ _ _ = true from
      theLiveAt_frame door o Zk h) frS.P.T.a)

def theKeyGateAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : RecFull → PQ.View → PQ.View → PQ.View →
    Bool :=
  gatedFileDecision (theLiveAt door o Zk) (theKeyRunAt o Zk)

def theProofGateAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : XF × RecFull → PQ.View → PQ.View →
    PQ.View → Bool :=
  gatedFileDecision (theLiveAt door o Zk) (theProofRunAt door o Zk)

def theLinkGateAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : RecFull × RecFull → PQ.View → Bool :=
  gatedLinkDecision (theLiveAt door o Zk) (linkDecisionAtFiles Zk)

def theProversAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) :
    (FsAtR (theClaims Zk) (theCoding Zk) G DK DP (theKeyGateAt door o Zk) (theProofGateAt door o Zk)
      (theLinkGateAt door o Zk)).Provers :=
  Files.fixedMessageProvers _

def theNamedAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) :
    NamedSideOfFullD (theClaims Zk) (theCoding Zk) DK DP (theKeyGateAt door o Zk)
      (theProofGateAt door o Zk)
      dsF xsF (theLinkGateAt door o Zk) G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G)
      (theProversAt door o Zk G DK DP) :=
  LPFD.Full.namedH (theClaims Zk) (theCoding Zk) G DK DP (theKeyGateAt door o Zk)
    (theProofGateAt door o Zk)
    (theLinkGateAt door o Zk) (theProversAt door o Zk G DK DP) G.z₀.1

/-! ### Lay0.lean -/

def theLay₀At (o : VerifierAndGoals.SecondHashFunctionType) : FlashProve.DescriptionData where
  A := theClaims
  E := theCoding
  DK := theKeyDataAt o
  DP := theProofDataAt door o
  runK := theKeyGateAt door o
  runP := theProofGateAt door o
  dec := theLinkGateAt door o
  G := thePlanAt o
  it := theItemAt o
  P := theProversAt door o
  N := theNamedAt door o
  ext := fun _ _ _ _ => none
  honest := theHonest
  hStar := fun _ _ _ _ _ => ByteArray.empty
  d₀ := fun _ => false
  f₀ := theForm0
  hf₀ := theForm0_aux
  live := theLiveAt door o
  hlive := theLiveAt_fit door o
  Gd := theDeadPlanAt o

end

/-! ### Extractor.lean, Lay.lean -/

section
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

variable (door : Door)

def starAt₀At (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : DescriptionDataAtFiles Zk :=
  dataAtFilesFromRounds (theLay₀At door o) Zk ((theLay₀At door o).filesParametersOrDefault Zk) ((theLay₀At door o).keyRoundsOrEmpty Zk)
    ((theLay₀At door o).proofRoundsOrEmpty Zk)
    ((theLay₀At door o).fit_of Zk)

def theExtractorAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (s : IntegerTransformer.Settings) :
    Commitment → QueryLog → Option (ModelWeights s) :=
  fun commitment queryLog =>
    (((starAt₀At door o Zk).layoutsByPublicReadingWithParameterBytes (fun _ => false) []
      (VerifierAndGoals.par7O o OnBytes.Tie.recordGround Zk.pol Zk.KL Zk.lay)).extractor commitment
        queryLog).bind fun M =>
      if hv : settingsAreValid s = true then phiO hv M else none

def theLayAt (o : VerifierAndGoals.SecondHashFunctionType) : FlashProve.DescriptionData :=
  { theLay₀At door o with ext := theExtractorAt door o }

end

/-! ### Description.lean -/

section
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Tie
open FlashProve FlashProve

variable (door : Door)

def theDescriptionO : SecondHashFunctionType → Description := fun o =>
  descriptionOfDataWithReading (fun Z c => readMoreAtO o recordGround Z c) (theLayAt door o)

def theDescription : SecondHashFunctionType → Description := theDescriptionO door

end

/-! ### The library's constant is its twin at the door -/

theorem theProofLaidAt_at : FlashProve.proofDataAndDecisionOrRefusalAt = theProofLaidAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl
theorem theProofDataAt_at : FlashProve.theProofDataAt = theProofDataAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl
theorem theProofRunAt_at : FlashProve.theProofRunAt = theProofRunAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl
theorem theLiveAt_at : FlashProve.protocolDataWellFormedAt = theLiveAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl
theorem theKeyGateAt_at : FlashProve.theKeyGateAt = theKeyGateAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl
theorem theProofGateAt_at : FlashProve.theProofGateAt = theProofGateAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl
theorem theLinkGateAt_at : FlashProve.theLinkGateAt = theLinkGateAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl
theorem theProversAt_at : FlashProve.theProversAt = theProversAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl
theorem theNamedAt_at : FlashProve.theNamedAt = theNamedAt LPFD.Full.proofDataAndDecisionOfPublicFiles := rfl

set_option maxHeartbeats 4000000 in
theorem theLay₀At_at : FlashProve.flashProveDataNoExtractorAtHash = theLay₀At LPFD.Full.proofDataAndDecisionOfPublicFiles := by
  funext o
  unfold FlashProve.flashProveDataNoExtractorAtHash theLay₀At
  congr 1

theorem starAt₀At_at : FlashProve.starAt₀At = starAt₀At LPFD.Full.proofDataAndDecisionOfPublicFiles := by
  funext o Zk
  have h : FlashProve.flashProveDataNoExtractorAtHash o = theLay₀At LPFD.Full.proofDataAndDecisionOfPublicFiles o := congrFun theLay₀At_at o
  unfold FlashProve.starAt₀At starAt₀At
  congr 1

theorem theExtractorAt_at : FlashProve.theExtractorAt = theExtractorAt LPFD.Full.proofDataAndDecisionOfPublicFiles := by
  funext o Zk s
  have h : FlashProve.starAt₀At o Zk = starAt₀At LPFD.Full.proofDataAndDecisionOfPublicFiles o Zk :=
    congrFun (congrFun starAt₀At_at o) Zk
  unfold FlashProve.theExtractorAt theExtractorAt
  funext commitment queryLog
  congr 1

theorem theLayAt_at : FlashProve.flashProveDataAtSecondHash = theLayAt LPFD.Full.proofDataAndDecisionOfPublicFiles := by
  funext o
  unfold FlashProve.flashProveDataAtSecondHash theLayAt
  rw [theLay₀At_at, theExtractorAt_at]

theorem theDescriptionO_at : VerifierAndGoals.theDescriptionO = theDescriptionO LPFD.Full.proofDataAndDecisionOfPublicFiles := by
  unfold VerifierAndGoals.theDescriptionO theDescriptionO
  rw [theLayAt_at]

/-- **The goals' description is the written function at the door.** -/
theorem theDescription_at : VerifierAndGoals.theDescription = theDescription LPFD.Full.proofDataAndDecisionOfPublicFiles := by
  unfold VerifierAndGoals.theDescription theDescription
  exact theDescriptionO_at

end LPFGuard.Text

#print axioms LPFGuard.Text.theProofLaidAt_at
#print axioms LPFGuard.Text.theProofDataAt_at
#print axioms LPFGuard.Text.theProofRunAt_at
#print axioms LPFGuard.Text.theLiveAt_at
#print axioms LPFGuard.Text.theKeyGateAt_at
#print axioms LPFGuard.Text.theProofGateAt_at
#print axioms LPFGuard.Text.theLinkGateAt_at
#print axioms LPFGuard.Text.theProversAt_at
#print axioms LPFGuard.Text.theNamedAt_at
#print axioms LPFGuard.Text.theLay₀At_at
#print axioms LPFGuard.Text.starAt₀At_at
#print axioms LPFGuard.Text.theExtractorAt_at
#print axioms LPFGuard.Text.theLayAt_at
#print axioms LPFGuard.Text.theDescriptionO_at
#print axioms LPFGuard.Text.theDescription_at

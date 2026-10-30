-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/FailsClosed.lean: THE SIBLING OF Johnson/Flat/FailsClosed.lean at the frame whose entry
file's rounds' data, stored openings and decision are letters too (Johnson/Flat/Dec/): the tests on
numbers that the frame's theorems ask of the THREE files' data, as ONE test, WHICH HAS CODE; data that
fail closed under it; and the three named hypotheses on soundness at a decision that never says yes.

Why a sibling. `frameFitFull` (Johnson/Flat/FailsClosed.lean) names the written rounds `frRds`, which have no
code: it is a Bool that cannot run, and a description whose data are closed by it cannot run. Here the
entry's rounds' data are the letter ds, and the test reads nothing written.

Main names (the full size; the small size is not here).
  `sizeNumbersFitAtFullSize K v depthReq depthReqT DK DP ds xs`: no round of the two whole files needs more than K
    blocks; the entry's four tests (`entryFitB`); work and depths of the two whole files; the count
    (`cntFrameFullD`) is at most v; K + 2 < 2^40 (a coding of the queries asks 2^49: `FrameFitFullD.hK`; the
    honest committer's count, which holds 2 (K + 2), is so kept far beneath 2^48). `FrameFitFullD`, `frameFitFullD_parts`: what its yes says.
  `frameFitFullD_hasCode`: a definition OUTSIDE the noncomputable section that calls the test: Lean
    compiles it, or this file is red.
  `FrameData`, `emptyData`, `closeFullByD Kof v depthReq depthReqT p`, `closeFullByD_fit`: as in the sibling.
  `linkW_never`: a link whose decision never says yes accepts nothing.
  `keySoundOfFullD_of_never`, `entrySoundOfFullD_of_never`, `proofSoundOfFullD_of_never`.

Limits: those of the sibling's head: A CASE SPLIT DOES A HYPOTHESIS's WORK; THE TEST's YES AT THE FILES OF
INTEREST IS AN EVALUATION AND IS NOT MADE HERE; THE THREE LAWS AT A DECISION THAT NEVER SAYS YES ARE TRUE
AND EMPTY: THEY COUNT FOR NOTHING BUT THE BRANCH THAT REFUSES.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.FailsClosed
import Johnson.Flat.Dec.CountAtFrame
import Johnson.Flat.Dec.EntrySound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.Flat
open Iop _root_.Run.PQ

/-- **A link whose decision never says yes accepts nothing.** -/
theorem linkW_never {Y : Type} (C : CK) (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO)
    (dec : Y → View → Bool) (never : ∀ x v, dec x v = false) (x : Y)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (τ : Tr (linkProtocolOfRoundData C ds a xs dec).shape) :
    (linkProtocolOfRoundData C ds a xs dec).accept x y τ = false := by
  show (_ && dec x _) = false
  rw [never, Bool.and_false]

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The test -/

/-- **The frame's tests on numbers at the full size, as one test, with code.** -/
def sizeNumbersFitAtFullSize (K v depthReq depthReqT : ℕ) (DK DP : WholeD)
    (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) : Bool :=
  decide (kThree .two DK [] DP ≤ K) && entryFitB K ds && DK.workFit && DK.depthFit &&
    DP.workFit && DP.depthFit && decide (cntFrameFullD DK DP ds xs depthReq depthReqT ≤ v) &&
    decide (K + 1 + 1 < 2 ^ 40)

/-- What its yes says, test by test. -/
structure FrameFitFullD (K v depthReq depthReqT : ℕ) (DK DP : WholeD)
    (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) : Prop where
  hk : kThree .two DK [] DP ≤ K
  hE : EntryFit K ds
  wK : DK.workFit = true
  dK : DK.depthFit = true
  wP : DP.workFit = true
  dP : DP.depthFit = true
  hcnt : cntFrameFullD DK DP ds xs depthReq depthReqT ≤ v
  hK40 : K + 1 + 1 < 2 ^ 40

/-- In the form in which a coding of the queries asks it. -/
theorem FrameFitFullD.hK {K v depthReq depthReqT : ℕ} {DK DP : WholeD}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    (h : FrameFitFullD K v depthReq depthReqT DK DP ds xs) : K + 1 + 1 < 2 ^ 49 :=
  h.hK40.trans (by norm_num)

theorem frameFitFullD_parts {K v depthReq depthReqT : ℕ} {DK DP : WholeD}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    (h : sizeNumbersFitAtFullSize K v depthReq depthReqT DK DP ds xs = true) :
    FrameFitFullD K v depthReq depthReqT DK DP ds xs := by
  unfold sizeNumbersFitAtFullSize at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, entryFit_of_test h2, h3, h4, h5, h6, h7, h8⟩

/-! ## Data that fail closed -/

/-- The data of the three files' rounds: the key file's, the proof file's, the entry file's with its
stored openings. -/
abbrev FrameData : Type :=
  WholeD × WholeD × List TypedOracleCompiler.Run.PQ.RD × List _root_.Run.PQ.XO

/-- No rounds at all. -/
def emptyData : FrameData := (emptyWhole, emptyWhole, [], [])

/-- **The data at which the frame stands**: p where the test says yes, and no rounds at all where it
does not. Kof: the wiring's number of blocks, as a function of the data. -/
def closeFullByD (Kof : FrameData → ℕ) (v depthReq depthReqT : ℕ) (p : FrameData) : FrameData :=
  if sizeNumbersFitAtFullSize (Kof p) v depthReq depthReqT p.1 p.2.1 p.2.2.1 p.2.2.2 then p else emptyData

theorem closeFullByD_of_fit {Kof : FrameData → ℕ} {v depthReq depthReqT : ℕ} {p : FrameData}
    (h : sizeNumbersFitAtFullSize (Kof p) v depthReq depthReqT p.1 p.2.1 p.2.2.1 p.2.2.2 = true) :
    closeFullByD Kof v depthReq depthReqT p = p := if_pos h

theorem closeFullByD_of_not {Kof : FrameData → ℕ} {v depthReq depthReqT : ℕ} {p : FrameData}
    (h : ¬ sizeNumbersFitAtFullSize (Kof p) v depthReq depthReqT p.1 p.2.1 p.2.2.1 p.2.2.2 = true) :
    closeFullByD Kof v depthReq depthReqT p = emptyData := if_neg h

/-- The test says yes where there are no rounds at all, under two premises on numbers. -/
theorem frameFitFullD_empty {K v depthReq depthReqT : ℕ} (hK2 : K + 1 + 1 < 2 ^ 40)
    (hv : 17 + depthReq + depthReqT ≤ v) :
    sizeNumbersFitAtFullSize K v depthReq depthReqT emptyWhole emptyWhole [] [] = true := by
  have hc : cntFrameFullD emptyWhole emptyWhole [] [] depthReq depthReqT =
      17 + depthReq + depthReqT := by
    show (2 + ((1 + (0 + (1 + (0 + (1 + 0)))) + 1) + (0 * _ + (depthReqT + 1)))) +
      (((0 + 1) + 1) + ((0 + 0) * _ + (0 + 1))) +
      (2 + ((1 + (0 + (1 + (0 + (1 + 0)))) + 1) + (0 * _ + (depthReq + 1)))) = _
    omega
  unfold sizeNumbersFitAtFullSize
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨Nat.zero_le _, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hc.le.trans hv⟩, hK2⟩

/-- **The test says yes at the closed data, whatever p is**, if it does where there are no rounds. -/
theorem closeFullByD_fit {Kof : FrameData → ℕ} {v depthReq depthReqT : ℕ}
    (h0 : sizeNumbersFitAtFullSize (Kof emptyData) v depthReq depthReqT emptyWhole emptyWhole [] [] = true)
    (p : FrameData) :
    sizeNumbersFitAtFullSize (Kof (closeFullByD Kof v depthReq depthReqT p)) v depthReq depthReqT
      (closeFullByD Kof v depthReq depthReqT p).1 (closeFullByD Kof v depthReq depthReqT p).2.1
      (closeFullByD Kof v depthReq depthReqT p).2.2.1
      (closeFullByD Kof v depthReq depthReqT p).2.2.2 = true := by
  by_cases h : sizeNumbersFitAtFullSize (Kof p) v depthReq depthReqT p.1 p.2.1 p.2.2.1 p.2.2.2 = true
  · rw [closeFullByD_of_fit h]
    exact h
  · rw [closeFullByD_of_not h]
    exact h0

/-! ## A decision that never says yes -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}

/-- True and empty: for the branch that refuses. -/
theorem keySoundOfFullD_of_never (never : ∀ r v₁ v₂ v₃, runK r v₁ v₂ v₃ = false)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T) :=
  ⟨Err.zero _, below_timesShared_zero _ _ _ _, fun x y _ =>
    Doomed.of_forall _ _ fun τ =>
      wholeIOR_never (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK never x y τ⟩

/-- True and empty: for the branch that refuses. -/
theorem entrySoundOfFullD_of_never (never : ∀ rr v, dec rr v = false)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) :=
  ⟨Err.zero _, below_timesShared_zero _ _ _ _, fun x y _ =>
    Doomed.of_forall _ _ fun τ => linkW_never (ckP .two) ds frS.P.T.a xs dec never x y τ⟩

/-- True and empty: for the branch that refuses. -/
theorem proofSoundOfFullD_of_never (never : ∀ x v₁ v₂ v₃, runP x v₁ v₂ v₃ = false)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T) :=
  ⟨fun _ _ _ => (), Err.timesShared _ _ (Err.zero _), below_timesShared_zero _ _ _ _, fun rec =>
    (sndBKT_laws _ _ _ _ _ _ _ _ _ _).2
      ⟨fun _ h => (by cases h), fun _ _ _ => false, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ h => (by cases h),
        fun y x τ _ hacc => (Bool.false_ne_true ((wholeIOR_never (DP.at frS.P.T.a) (front₀ rP)
          (join₀ rP) ByteArray.empty silP runP never (x, rec) y τ).symm.trans hacc)).elim,
        fun _ x => jointLaw_never _ _ _ x⟩⟩

end

end VerifiableInference.OnPublicFiles

end

/-- OUTSIDE THE NONCOMPUTABLE SECTION: Lean compiles this call of the test and of the closing, or the
file is red: so both have code. -/
def VerifiableInference.OnPublicFiles.frameFitFullD_hasCode : Bool :=
  VerifiableInference.OnPublicFiles.sizeNumbersFitAtFullSize 0 0 0 0
    (VerifiableInference.OnPublicFiles.closeFullByD (fun _ => 0) 0 0 0
      VerifiableInference.OnPublicFiles.emptyData).1
    VerifiableInference.OnPublicFiles.emptyWhole [] []

#print axioms VerifiableInference.OnPublicFiles.frameFitFullD_parts
#print axioms VerifiableInference.OnPublicFiles.frameFitFullD_empty
#print axioms VerifiableInference.OnPublicFiles.closeFullByD_fit
#print axioms VerifiableInference.OnPublicFiles.keySoundOfFullD_of_never
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_of_never
#print axioms VerifiableInference.OnPublicFiles.proofSoundOfFullD_of_never

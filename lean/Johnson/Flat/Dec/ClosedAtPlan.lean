-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Dec/ClosedAtPlan.lean: THE CLOSING IN THE SHAPE IN WHICH A DESCRIPTION OVER A PLAN LAYS IT: the plan's record G (`FilesParameters`,
OnBytes/Flat/FilesAt.lean), from which the two depths of request trees are read, and the two whole files' data fail closed TOGETHER; the
entry file's rounds stay pinned at the written ones (`dsFull`, `frD.xs`); the three decisions stand behind a gate. The full size.

Why. Johnson/Flat/Dec/ClosedAll.lean closes the depths as numbers. A description whose letters are all read off one record G of the plan
(the records at which dry runs are made, `early`, the depths) cannot lay a depth by itself: it lays another G.

Main names.
  `FilesParameters.noDepth G`: G with both binding trees' depth, and depthReq, 0; nothing else turns (`noDepth_first`, `noDepth_oneTime` := rfl).
  `sizeNumbersFitAtPlan KF v G DK DP`: THE TEST: `sizeNumbersFitAtFullSize` at K := KF DK DP, the depths G's own, the entry's written rounds. It has code.
  `gAt`, `dkAt`, `dpAt`: G, DK, DP where the test says yes; `G.noDepth`, `deadW`, `deadW` where it does not.
  `fit_at`: THE TEST SAYS YES AT THESE THREE, WHATEVER G, DK, DP ARE, under three premises ON NUMERALS AND KF ALONE: 140 ≤ KF deadW deadW;
    KF deadW deadW + 2 < 2^40; 13555 ≤ v.
  `three_at`: so the three tests that a coding of the queries asks hold there (kindsAndWorkBelow256 twice; K + 2 < 2^49).
  `tVC_at`: tVC of the frame's wire there is at most v, at every other letter.
  `compilerSoundnessConditionsAtFullSize_at`: there, at the three gated decisions: the fifteen of `CompilerSoundnessConditions` from the three premises on numerals, commitment, and
    keySound, entrySound, proofSound WHERE THE TEST SAYS YES.
  `at_live`: where the test says yes the three are G, DK, DP themselves and the gates are open.

Limits: those of ClosedAll.lean: THE CLOSING IS A CHANGE OF THE VERIFIER's TEXT; WHERE THE TEST SAYS NO THE VERIFIER REFUSES ALL AND THE THREE HYPOTHESES ON
SOUNDNESS HOLD FOR NOTHING. KF is a letter. NO VALUE OF THIS FRAME HAS RUN ON A REAL PROOF. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.ClosedAll
import Johnson.Flat.Dec.DeadAtWritten
import Johnson.Flat.Dec.FitGivesSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.Flat

/-- The plan's record with both binding trees' depth 0. -/
def FilesParameters.noDepth {X R : Type} (G : FilesParameters X R) : FilesParameters X R :=
  { G with
    k := { G.k with oneTime := { G.k.oneTime with
      binding := { G.k.oneTime.binding with logLeaves := 0 } } }
    c := { G.c with first := { G.c.first with
      binding := { G.c.first.binding with logLeaves := 0 } } }
    depthReq := 0 }

theorem FilesParameters.noDepth_first {X R : Type} (G : FilesParameters X R) :
    G.noDepth.c.first.binding.logLeaves = 0 := rfl

theorem FilesParameters.noDepth_oneTime {X R : Type} (G : FilesParameters X R) :
    G.noDepth.k.oneTime.binding.logLeaves = 0 := rfl

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section
variable {X R : Type} (KF : WholeD → WholeD → ℕ) (v : ℕ) (G : FilesParameters X R) (DK DP : WholeD)

/-- **The test.** -/
def sizeNumbersFitAtPlan : Bool :=
  sizeNumbersFitAtFullSize (KF DK DP) v G.c.first.binding.logLeaves G.k.oneTime.binding.logLeaves DK DP dsFull
    frD.xs

/-- The plan's record at which the frame stands. -/
def gAt : FilesParameters X R := if sizeNumbersFitAtPlan KF v G DK DP then G else G.noDepth

/-- The key file's data at which it stands. -/
def dkAt : WholeD := if sizeNumbersFitAtPlan KF v G DK DP then DK else deadW

/-- The proof file's. -/
def dpAt : WholeD := if sizeNumbersFitAtPlan KF v G DK DP then DP else deadW

theorem at_live (h : sizeNumbersFitAtPlan KF v G DK DP = true) :
    gAt KF v G DK DP = G ∧ dkAt KF v G DK DP = DK ∧ dpAt KF v G DK DP = DP :=
  ⟨if_pos h, if_pos h, if_pos h⟩

theorem at_dead (h : sizeNumbersFitAtPlan KF v G DK DP = false) :
    gAt KF v G DK DP = G.noDepth ∧ dkAt KF v G DK DP = deadW ∧ dpAt KF v G DK DP = deadW := by
  have n : ¬ (sizeNumbersFitAtPlan KF v G DK DP = true) := by rw [h]; exact Bool.false_ne_true
  exact ⟨if_neg n, if_neg n, if_neg n⟩

/-- **The test says yes at the three, whatever G, DK, DP are.** -/
theorem fit_at (h140 : 140 ≤ KF deadW deadW) (h40 : KF deadW deadW + 1 + 1 < 2 ^ 40)
    (hv : 13555 ≤ v) :
    sizeNumbersFitAtFullSize (KF (dkAt KF v G DK DP) (dpAt KF v G DK DP)) v
      (gAt KF v G DK DP).c.first.binding.logLeaves (gAt KF v G DK DP).k.oneTime.binding.logLeaves
      (dkAt KF v G DK DP) (dpAt KF v G DK DP) dsFull frD.xs = true := by
  cases h : sizeNumbersFitAtPlan KF v G DK DP with
  | true =>
    obtain ⟨e₁, e₂, e₃⟩ := at_live KF v G DK DP h
    rw [e₁, e₂, e₃]
    exact h
  | false =>
    obtain ⟨e₁, e₂, e₃⟩ := at_dead KF v G DK DP h
    rw [e₁, e₂, e₃]
    exact frameFitFullD_dead h140 h40 hv

/-- The three tests that a coding of the queries asks. -/
theorem three_at (h140 : 140 ≤ KF deadW deadW) (h40 : KF deadW deadW + 1 + 1 < 2 ^ 40)
    (hv : 13555 ≤ v) (a : ℕ) :
    OnBytes.Maker.Page.kindsAndWorkBelow256 ((dkAt KF v G DK DP).at a) = true ∧
      OnBytes.Maker.Page.kindsAndWorkBelow256 ((dpAt KF v G DK DP).at a) = true ∧
      KF (dkAt KF v G DK DP) (dpAt KF v G DK DP) + 1 + 1 < 2 ^ 49 :=
  frameFitFullD_three (fit_at KF v G DK DP h140 h40 hv) a

end

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
  (KF : WholeD → WholeD → ℕ) (v : ℕ) (G : FilesParameters X RecFull) (DK DP : WholeD)

/-- **The compiled verifier's own count of typed queries there is at most v.** -/
theorem tVC_at (h140 : 140 ≤ KF deadW deadW) (h40 : KF deadW deadW + 1 + 1 < 2 ^ 40)
    (hv : 13555 ≤ v) (Rs : (frS.toDecR frZ 402653181).RelationsAndEncoding A)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (early : X → X) (salt K : ℕ)
    (P : (threeProtocolsAtFullSize A Rs (dkAt KF v G DK DP) (dpAt KF v G DK DP) runK runP dsFull frD.xs dec rK rP
      (gAt KF v G DK DP).c.first.binding.logLeaves early salt).Provers) :
    tVC (wireOfFullD A Rs (dkAt KF v G DK DP) (dpAt KF v G DK DP) runK runP dsFull frD.xs dec rK rP
      (gAt KF v G DK DP).c.first.binding.logLeaves early salt P K
      (gAt KF v G DK DP).k.oneTime.binding.logLeaves) ≤ v := by
  rw [tVC_wireOfFullD]
  exact (frameFitFullD_parts (fit_at KF v G DK DP h140 h40 hv)).hcnt

/-- **The fifteen there, at the three gated decisions.** -/
theorem compilerSoundnessConditionsAtFullSize_at (h140 : 140 ≤ KF deadW deadW) (h40 : KF deadW deadW + 1 + 1 < 2 ^ 40)
    (hv : 13555 ≤ v) {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {early : X → X} {salt : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) (dkAt KF v G DK DP) (dpAt KF v G DK DP)
      (gatedFileDecision (sizeNumbersFitAtPlan KF v G DK DP) runK) (gatedFileDecision (sizeNumbersFitAtPlan KF v G DK DP) runP) dsFull frD.xs
      (gatedLinkDecision (sizeNumbersFitAtPlan KF v G DK DP) dec) rK rP (gAt KF v G DK DP).c.first.binding.logLeaves early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E (dkAt KF v G DK DP) (dpAt KF v G DK DP)
      (gatedFileDecision (sizeNumbersFitAtPlan KF v G DK DP) runK) (gatedFileDecision (sizeNumbersFitAtPlan KF v G DK DP) runP) dsFull frD.xs
      (gatedLinkDecision (sizeNumbersFitAtPlan KF v G DK DP) dec) rK rP (gAt KF v G DK DP).c.first.binding.logLeaves early salt
      (KF (dkAt KF v G DK DP) (dpAt KF v G DK DP)) P)
    (hT : T.depthReqT = (gAt KF v G DK DP).k.oneTime.binding.logLeaves)
    (kS : sizeNumbersFitAtPlan KF v G DK DP = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T))
    (eS : sizeNumbersFitAtPlan KF v G DK DP = true → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T))
    (pS : sizeNumbersFitAtPlan KF v G DK DP = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T))
    (cm : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataAtFullSize T)) : CompilerSoundnessConditions (soundnessAnalysisDataAtFullSize T) := by
  have hfit : sizeNumbersFitAtFullSize (KF (dkAt KF v G DK DP) (dpAt KF v G DK DP)) v
      (gAt KF v G DK DP).c.first.binding.logLeaves T.depthReqT (dkAt KF v G DK DP)
      (dpAt KF v G DK DP) dsFull frD.xs = true := by
    rw [hT]
    exact fit_at KF v G DK DP h140 h40 hv
  have hl : RemainingSoundnessConditionsAtFullSize T :=
    remainingSoundnessConditionsAtFullSize_live (sizeNumbersFitAtPlan KF v G DK DP) (fun h => gate3_dead h runK)
      (fun h => gate1_dead h dec) (fun h => gate3_dead h runP) kS eS pS cm
  exact compilerSoundnessConditionsAtFullSize_of_fit hfit hl

end

end VerifiableInference.OnPublicFiles

end

/-- OUTSIDE THE NONCOMPUTABLE SECTION: Lean compiles this definition, which calls the record's turn, or the file is red. (The
test itself reads `dsFull`, whose code is the library's matter.) -/
def OnBytes.Flat.noDepth_hasCode {X R : Type} (G : OnBytes.Flat.FilesParameters X R) : Nat :=
  G.noDepth.c.first.binding.logLeaves + G.noDepth.k.oneTime.binding.logLeaves

#print axioms VerifiableInference.OnPublicFiles.fit_at
#print axioms VerifiableInference.OnPublicFiles.three_at
#print axioms VerifiableInference.OnPublicFiles.tVC_at
#print axioms VerifiableInference.OnPublicFiles.compilerSoundnessConditionsAtFullSize_at

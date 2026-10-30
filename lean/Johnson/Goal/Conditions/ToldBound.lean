-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/ToldBound.lean: the two debts «bound» and «ceil» of G8 at D⋆ (G8_descriptionOfFields_of_remainingConditions |
  G8_descriptionOfFields_withTerms; G8_descriptionOfDataOnBytes | G8_theDescription), general in S : DescriptionDataAtFiles Zk: at eps :=
  epsFrame s v (Johnson/Flat/CountAtFrame.lean:193: a closed error in which no wiring stands) they
  follow from the frame's one test on numbers (sizeNumbersFitAtFullSize, Johnson/Flat/Dec/FailsClosed.lean) and
  one inequality on the named side's εs.
  roundError_descriptionDataAtFiles      (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀)).εs = S.N.εs := rfl: the stated round's error is the
    named side's letter
  **verifierQueryCountBound_descriptionDataAtFiles**  the compiled verifier's own count of typed queries at D⋆'s wiring is at most v,
    where the test says yes at S's letters and v (tVC_wireOfFullD; the test's clause hcnt)
  **errorBound_descriptionDataAtFiles**  soundnessBoundOverTypedOracles (S.inputFieldsAtReadings c₀ m₀).W εs (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤ epsFrame s v t
    n: «bound», to the letter, at one S (bound_of_numbers)
  frameError_le_ceiling     epsFrame s v t n ≤ ceiling up to the two budgets, at s ≤ 55 and v ≤ 2^63: «ceil», to
    the letter (ceil_of_numbers)
The premises. fit: the test's yes at (KF S.DK S.DP, v, S.G's two depths, S.DK, S.DP, the entry's
  written rounds): at the description's family it is fit_theLay
  (Johnson/Goal/Conditions/NumbersAtThe.lean), at every Z. has: a + s = 128. he: S.N.εs ≤ c · 2^-a.
  hc: c ≤ 5/4.
Who reads each letter. v: the test and the closed error. a s c: the closed error's level against εs.
  c₀ m₀: nobody but the types (the wiring and εs hang on neither: verifierQueryCountBound_descriptionDataAtFiles's right side names none).
  No ∃.
Does not show. The ceiling is one quarter: no security level (Ladder.lean's own head). That εs is
  a true bound on any round's error: that is keySound | entrySound | proofSound. The nine debts on
  numbers (hk … dP): not this file's. Nothing on soundness.
No soundness is claimed.
-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles
import Johnson.Flat.Dec.FailsClosed
import Johnson.Flat.Dec.CountAtFrame
import Johnson.Flat.CountAtFrame
import Ladder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- The stated bound on a round's error is the named side's letter. -/
theorem roundError_descriptionDataAtFiles : (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀)).εs = S.N.εs := rfl

/-- **The compiled verifier's own count at D⋆'s wiring is at most v, where the frame's test says yes.** -/
theorem verifierQueryCountBound_descriptionDataAtFiles (v : ℕ)
    (fit : sizeNumbersFitAtFullSize (KF S.DK S.DP) v S.G.c.first.binding.logLeaves S.G.k.oneTime.binding.logLeaves
      S.DK S.DP dsFull frD.xs = true) : tVC (S.inputFieldsAtReadings c₀ m₀).W ≤ v :=
  le_of_eq_of_le
    (tVC_wireOfFullD S.A (relationsAndEncodingOfClaims S.A S.E) S.DK S.DP S.runK S.runP dsFull frD.xs S.dec S.G.rec₀ S.G.z₀.2
      S.G.c.first.binding.logLeaves S.G.early (saltG S.G) S.P (KF S.DK S.DP) S.G.k.oneTime.binding.logLeaves)
    (frameFitFullD_parts fit).hcnt

/-- **«bound» at one S.** -/
theorem errorBound_descriptionDataAtFiles (v : ℕ)
    (fit : sizeNumbersFitAtFullSize (KF S.DK S.DP) v S.G.c.first.binding.logLeaves S.G.k.oneTime.binding.logLeaves
      S.DK S.DP dsFull frD.xs = true)
    (c : ℝ≥0∞) (a s : ℕ) (has : a + s = 128) (he : S.N.εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹)
    (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹) (t n : ℕ) :
    soundnessBoundOverTypedOracles (S.inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀)).εs (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤
      epsFrame s v t n :=
  bound_of_numbers (S.inputFieldsAtReadings c₀ m₀).W _ c a s v has he hc (verifierQueryCountBound_descriptionDataAtFiles S c₀ m₀ v fit) t n

/-- **«ceil».** -/
theorem frameError_le_ceiling (s v : ℕ) (hs : s ≤ 55) (hv : v ≤ 2 ^ 63) :
    ∀ t n, t ≤ queryBudget → n ≤ parserBudget → epsFrame s v t n ≤ ceiling :=
  fun t n ht hn => ceil_of_numbers s v hs hv t n ht hn

end FlashProve

#print axioms FlashProve.roundError_descriptionDataAtFiles
#print axioms FlashProve.verifierQueryCountBound_descriptionDataAtFiles
#print axioms FlashProve.errorBound_descriptionDataAtFiles
#print axioms FlashProve.frameError_le_ceiling

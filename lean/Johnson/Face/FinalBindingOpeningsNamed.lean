-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalBindingOpeningsNamed.lean: a guard on the lines on binding (FinalBindingStatement.lean, head,
item 4: at a small coinBound binding says next to nothing). An opening names one number up to coinBound;
its first two digits name the first table's encoding randomness and salts. Here: wherever the
committer's range divides coinBound + 1, EVERY pair of first two digits is named by a number up to
coinBound; and at theSettings (Johnson/CompletenessAndZeroKnowledge/TheSettings.lean), at public files in use, the first digit
runs through every encoding randomness of the first table.

 1. firstTwoDigits_le: (h.ri.n + 1) * (h.sl.n + 1) ≤ bound + 1.
 2. firstTwoDigits_named: at every a, b: a number n ≤ bound with firstRandomness h n = h.ri.e a and
    firstSalts h leaves n = cutS leaves (h.sl.e b) (CommitValue.lean).
 3. openingsNamed_atTheSettings: that at theHonestPartOf's own side and coinBound, at every reading
    (coinsRange_dvd_theCoinBound).
 4. everyRandomness_atTheSettings: at public files in use, at every reading, every encoding randomness r
    and every b: a number n ≤ coinBound whose first digit names r and whose second names b
    (theSettings_fit … .coins.ri: the list of encoding randomness holds each member once).
Limits. General lemmas on numbers and two instances. Nothing on binding itself. Of the salts it says that
every member of the side's list is named; that this list runs through all settings of the free bits
is SaltsLaw (Johnson/WholeKey/CoinLaws.lean), a law on distributions, which is not spent here. No number
is given for coinBound. Nothing on the later digits.
-/
import Johnson.Face.FinalBindingAtTheSettings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Johnson.Face
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.WholeKey OnBytes.FrontRoad
open _root_.Iop (HolographicProtocol RoundSplits)

section General
variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (h : HonestSide 256 L Bd aT aL)

/-- The first two lists' sizes lie under the range. -/
theorem firstTwo_le_coinsRange : (h.ri.n + 1) * (h.sl.n + 1) ≤ coinsRange h := by
  unfold coinsRange
  rw [← Nat.mul_assoc]
  exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _)
    (Nat.pow_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _)
      (Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _) Nat.one_pos)))))))

/-- **The first two lists' sizes lie under the bound.** -/
theorem firstTwoDigits_le {bound : ℕ} (dvd : coinsRange h ∣ bound + 1) :
    (h.ri.n + 1) * (h.sl.n + 1) ≤ bound + 1 :=
  (firstTwo_le_coinsRange h).trans (Nat.le_of_dvd (Nat.succ_pos _) dvd)

/-- **Every pair of first two digits is named by a number up to the bound.** -/
theorem firstTwoDigits_named {bound : ℕ} (dvd : coinsRange h ∣ bound + 1) (leaves : ℕ)
    (a : Fin (h.ri.n + 1)) (b : Fin (h.sl.n + 1)) :
    ∃ n, n ≤ bound ∧ firstRandomness h n = h.ri.e a ∧
      firstSalts h leaves n = cutS leaves (h.sl.e b) := by
  have e₁ : (a.val + (h.ri.n + 1) * b.val) % (h.ri.n + 1) = a.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
  have e₂ : (a.val + (h.ri.n + 1) * b.val) / (h.ri.n + 1) % (h.sl.n + 1) = b.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.succ_pos _), Nat.div_eq_of_lt a.isLt, Nat.zero_add,
      Nat.mod_eq_of_lt b.isLt]
  have lt : a.val + (h.ri.n + 1) * b.val < (h.ri.n + 1) * (h.sl.n + 1) := by
    calc a.val + (h.ri.n + 1) * b.val < (h.ri.n + 1) + (h.ri.n + 1) * b.val :=
          Nat.add_lt_add_right a.isLt _
      _ = (h.ri.n + 1) * (b.val + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ (h.ri.n + 1) * (h.sl.n + 1) := Nat.mul_le_mul_left _ b.isLt
  refine ⟨a.val + (h.ri.n + 1) * b.val,
    Nat.le_of_lt_succ (lt.trans_le (firstTwoDigits_le h dvd)), ?_, ?_⟩
  · exact congrArg h.ri.e (Fin.ext e₁)
  · exact congrArg (fun c => cutS leaves (h.sl.e c)) (Fin.ext e₂)

end General

open VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open IntegerTransformer (Settings)

variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
  (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers)
  (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout)

/-- The honest side at theSettings, at a reading. -/
abbrev theSideAt (reading : FlashReading files) :=
  (honestSide (flashLayout files settings fallbackInstance reading) provers
    (theSettings files settings fallbackInstance provers starts limits slotSalts reading)).side

/-- **At theSettings every pair of first two digits is named by a number up to theCoinBound**, at every
reading. -/
theorem openingsNamed_atTheSettings (reading : FlashReading files) (leaves : ℕ)
    (a : Fin ((theSideAt files settings fallbackInstance provers starts limits slotSalts reading).ri.n
      + 1))
    (b : Fin ((theSideAt files settings fallbackInstance provers starts limits slotSalts reading).sl.n
      + 1)) :
    ∃ n, n ≤ theCoinBound files settings fallbackInstance provers starts limits slotSalts ∧
      firstRandomness (theSideAt files settings fallbackInstance provers starts limits slotSalts
        reading) n =
        (theSideAt files settings fallbackInstance provers starts limits slotSalts reading).ri.e a ∧
      firstSalts (theSideAt files settings fallbackInstance provers starts limits slotSalts reading)
        leaves n =
        OnBytes.WholeKey.cutS leaves
          ((theSideAt files settings fallbackInstance provers starts limits slotSalts reading).sl.e
            b) :=
  firstTwoDigits_named _
    (coinsRange_dvd_theCoinBound files settings fallbackInstance provers starts limits slotSalts
      reading) leaves a b

/-- **At public files in use every encoding randomness of the first table is named**, beside every
member of the list of salts. -/
theorem everyRandomness_atTheSettings (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (h : starts.LengthsFit 256 256)
    (reading : FlashReading files)
    (slots : slotSalts.Fit (flashLayout files settings fallbackInstance reading)) (leaves : ℕ)
    (r : (FlashProtocol files).EncodingRandomness)
    (b : Fin ((theSideAt files settings fallbackInstance provers starts limits slotSalts reading).sl.n
      + 1)) :
    ∃ n, n ≤ theCoinBound files settings fallbackInstance provers starts limits slotSalts ∧
      firstRandomness (theSideAt files settings fallbackInstance provers starts limits slotSalts
        reading) n = r ∧
      firstSalts (theSideAt files settings fallbackInstance provers starts limits slotSalts reading)
        leaves n =
        OnBytes.WholeKey.cutS leaves
          ((theSideAt files settings fallbackInstance provers starts limits slotSalts reading).sl.e
            b) := by
  obtain ⟨a, ha⟩ := (theSettings_fit files settings fallbackInstance provers limits slotSalts scope
    live starts h reading slots).coins.ri.2 r
  obtain ⟨n, hn, e₁, e₂⟩ := openingsNamed_atTheSettings files settings fallbackInstance provers starts
    limits slotSalts reading leaves a b
  exact ⟨n, hn, e₁.trans ha, e₂⟩

end Johnson.Face

#print axioms Johnson.Face.firstTwoDigits_le
#print axioms Johnson.Face.firstTwoDigits_named
#print axioms Johnson.Face.openingsNamed_atTheSettings
#print axioms Johnson.Face.everyRandomness_atTheSettings

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WideDigits.lean: AT THE ONE CLOSED DESCRIPTION WITH THE NUMBER OF COINS A
LETTER (`theWide K W`, Johnson/Goal/Conditions/WideAtThe.lean): A VALUE OF THE LETTERS THAT LISTS
THE WHOLE SPACE OF THE COMMITTER'S COINS BY THE DIGITS OF A NUMBER: NO ENUMERATION IS PICKED BY
CHOICE. Definitions, statements and proofs.

Why. `K.onto` (Johnson/Goal/Conditions/WideOnto.lean) covers the coins by enumerations picked by
choice, so `theWideOpen` is a witness for the theorems' reach and no value for a description whose
running fields may use no choice (the head of Ladder.lean, 9). This file gives a K that lists
the coins by digits.

Main names (namespace `FlashProve`).
  `fieldRows v l`, `fieldRows_ok`: all tables of 2^v rows of l members of the base field
    (`enumFuns`, `enumZMod`, Johnson/Top/EnumDigits.lean).
  `riDigits Z`, `riDigits_ok`: all pads with tails: a pair of two such tables (`enumPair`). THAT
    THIS TERM HAS THE TYPE "an enumeration of the description's pads with tails" is checked by Lean
    where it is defined: it holds over `theCoding` := `codingCells`
    (Johnson/Goal/Description/Coding.lean).
  **`K.digits`**: K with ri := `riDigits` and sl := `saltsDigits` at the tree's depth and compilerParameters.sMT.
  `covers_digits`: it covers the coins at every Z (`TheCoins.Covers`,
    Johnson/Goal/Conditions/CoinsEnumeratedAt.lean). `digits_once`: each of its two enumerations
    lists every one of its values once.
  `Rw K W Z`: the compiler's input of `theWide K W` itself. `own_same`: AT EVERY K AND W its pads
    with tails, its tree's depth and its salts' length are those of `R₀ Z` (by definition).
  `coins_enumerated_own`: `coins_enumerated_of` with these three read at `Rw`: general in K.
  **`coins_enumerated_digits`**: so at `theWide K.digits (WideCoins.full K.digits toNat)`: for every
    r and all salts σ of compilerParameters.sMT bits at each of the tree's places THERE IS ρ WITH: AT EVERY HASH
    FUNCTION THE VALUE OF THE DESCRIPTION'S COMMITTER AT (w, ρ) IS THE VALUE OF THE COMMITTER WITH
    THE COINS (r, σ) FIXED.
  `digitCoins`, `digitWide`, `theWideDigits`: the closed description at
    `placeHolderNumberCoins.digits`: the randomness's type is the numbers, and the opener names the
    number outright.
  **`coins_enumerated_digits_closed`**, **`G9_digits`**, **`G9bits_digits`**: at it: no premise, no
    letter. `nearestSoundAndBinding_digits`: the row's form there, from the three hypotheses of
    `nearestSoundAndBinding_theWide`.

LEAN'S KERNEL AT THESE LENGTHS (seen; the cause is NOT found). A trial took r at `R₀ Z`, as
`coins_enumerated_at` does. Lean's elaborator passed it; the kernel ended in "deep recursion
detected" at the two statements. By trials: the one piece that fails is `fixedCommit (theWideTerms
K.digits (WideCoins.full K.digits toNat)) Z s w r σ` with r from `R₀ Z`: there the kernel has to see
that the two inputs have one type of pads. It passes with W a letter; with K a letter; with either
enumeration's length alone for the number of coins; it fails with their product, in the two
forms tried (A B - 1; A (B - 1) + (A - 1)). It passes with r taken at the description's own input:
so the statements here are typed.
WHOEVER STATES SOMETHING AT `theWideDigits`: read every part at ONE input, or prove it at K and W
in letters and apply it (so `own_same`).

Limits. Those of WideAtThe.lean and EnumDigits.lean. Besides:
- "NO CHOICE" IS SAID OF THE TWO ENUMERATIONS AND OF `WideCoins.full`, BY THEIR TEXT. The other
  fields of `theWideDigits` are `placeHolderNumberCoins`' and `descriptionOfDataOnBytes flashProveData`'s: not read here.
  THE PRINT at the foot: `fieldRows` and (Johnson/Top/EnumDigits.lean) `saltsDigits` show no
  `Classical.choice`; `riDigits` shows it: its TYPE names the description's type of pads.
- WRITTEN, NOT RUN: the numbers have more digits than a machine holds.
- At `theWideDigits` the sampler gives 0 and the provers hand over empty things: nothing on hiding,
  nothing on completeness. No generator is written: the number is the randomness itself.
- Salts of another length at a place that the tree reads are not covered.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.CoinsEnumeratedAt
import Johnson.Top.EnumDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice

/-- All tables of 2^v rows of l members of the base field, by digits. -/
def fieldRows (v l : ℕ) : _root_.Iop.Enum (Fin (2 ^ v) → Fin l → OnBytes.Slice.GF) :=
  enumFuns (2 ^ v) (enumFuns l (enumZMod Code.pGold))

theorem fieldRows_ok (v l : ℕ) : (fieldRows v l).OK :=
  enumFuns_ok _ _ (enumFuns_ok _ _ (enumZMod_ok Code.pGold))

/-- **All pads with tails, by digits.** -/
def riDigits (Z : PublicFiles) : _root_.Iop.Enum (R₀ Z).protocol.EncodingRandomness := enumPair (fieldRows _ _) (fieldRows _ _)

theorem riDigits_ok (Z : PublicFiles) : (riDigits Z).OK :=
  enumPair_ok _ _ (fieldRows_ok _ _) (fieldRows_ok _ _)

/- From here on Lean compares these by their names. -/
attribute [local irreducible] descriptionOfDataOnBytes riDigits fieldRows

/-- **K with the coins listed by digits.** -/
def TheCoins.digits (K : TheCoins) : TheCoins :=
  { K with
    ri := riDigits
    sl := fun Z => saltsDigits (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT }

variable (K : TheCoins)

/-- It covers the coins, at every Z. -/
theorem covers_digits (Z : PublicFiles) : K.digits.Covers Z :=
  ⟨(riDigits_ok Z).2, saltsDigits_covers (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT⟩

/-- Each of its two enumerations lists every one of its values once. -/
theorem digits_once (Z : PublicFiles) :
    Function.Injective (K.digits.ri Z).e ∧ Function.Injective (K.digits.sl Z).e :=
  ⟨(riDigits_ok Z).1, saltsDigits_once (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT⟩

/-- The compiler's input of `theWide K W` at which its honest side's terms are taken. It parts from
`R₀ Z` in the number of coins alone (`InnerCompilerInput.reBound`, Johnson/Goal/Conditions/ReBound.lean). -/
abbrev Rw (K : TheCoins) (W : WideCoins K) (Z : PublicFiles) : InnerCompilerInput :=
  (flashProveDescription.reBound W.bound).input Z ((theWideTerms K W).c₀ Z) ((theWideTerms K W).m₀ Z)

/-- **At every K and W**: its pads with tails, its tree's depth and its salts' length are those of
`R₀ Z`. -/
theorem own_same (K : TheCoins) (W : WideCoins K) (Z : PublicFiles) :
    (Rw K W Z).protocol.EncodingRandomness = (R₀ Z).protocol.EncodingRandomness ∧ (Rw K W Z).queryLayout.depth = (R₀ Z).queryLayout.depth ∧
      (Rw K W Z).compilerParameters.sMT = (R₀ Z).compilerParameters.sMT :=
  ⟨rfl, rfl, rfl⟩

/-- `coins_enumerated_of` (Johnson/Goal/Conditions/CoinsEnumeratedAt.lean) with the pads, the depth
and the salts' length read at the description's own input: general in K. -/
theorem coins_enumerated_own (toNat : K.Rand → ℕ) (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (hK : K.Covers Z)
    (onto : ∀ n, n < ((K.ri Z).n + 1) * ((K.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (w : ModelWeights (settingsOfRead pp)) (r : (Rw K (WideCoins.full K toNat) Z).protocol.EncodingRandomness)
    (σ : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (Rw K (WideCoins.full K toNat) Z).queryLayout.depth →
      (σ j).length = (Rw K (WideCoins.full K toNat) Z).compilerParameters.sMT) :
    ∃ ρ : K.Rand, ∀ hash : VerifiableInference.Hash,
      ((theWide K (WideCoins.full K toNat) o).commit Z (settingsOfRead pp) w ρ).evaluate hash =
        (fixedCommit (theWideTerms K (WideCoins.full K toNat)) Z (settingsOfRead pp) w r
          σ).evaluate hash :=
  coins_enumerated_of K toNat o Z pp hr hK onto w r σ hσ

/-- **EVERY SETTING OF COINS IS REACHED, AT THE DESCRIPTION'S OWN COMMITTER.** -/
theorem coins_enumerated_digits (toNat : K.digits.Rand → ℕ) (o : SecondHashFunctionType) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (onto : ∀ n, n < ((K.digits.ri Z).n + 1) * ((K.digits.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (w : ModelWeights (settingsOfRead pp))
    (r : (Rw K.digits (WideCoins.full K.digits toNat) Z).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (Rw K.digits (WideCoins.full K.digits toNat) Z).queryLayout.depth →
      (σ j).length = (Rw K.digits (WideCoins.full K.digits toNat) Z).compilerParameters.sMT) :
    ∃ ρ : K.digits.Rand, ∀ hash : VerifiableInference.Hash,
      ((theWide K.digits (WideCoins.full K.digits toNat) o).commit Z (settingsOfRead pp) w
        ρ).evaluate hash =
        (fixedCommit (theWideTerms K.digits (WideCoins.full K.digits toNat)) Z (settingsOfRead pp)
          w r σ).evaluate hash :=
  coins_enumerated_own K.digits toNat o Z pp hr (covers_digits K Z) onto w r σ hσ

/-! ## The closed value -/

/-- The closed value of the letters: `placeHolderNumberCoins` with the coins listed by digits. -/
def digitCoins : TheCoins := placeHolderNumberCoins.digits

/-- The number is the randomness itself. -/
def digitWide : WideCoins digitCoins := WideCoins.full digitCoins (fun n : ℕ => n)

/-- **The closed description at which the opener may pick any coins, and no enumeration is picked by
choice.** -/
def theWideDigits : SecondHashFunctionType → Description := theWide digitCoins digitWide

/-- **At it every setting of coins is reached: no premise, no letter.** -/
theorem coins_enumerated_digits_closed (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp))
    (r : (Rw digitCoins digitWide Z).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (Rw digitCoins digitWide Z).queryLayout.depth →
      (σ j).length = (Rw digitCoins digitWide Z).compilerParameters.sMT) :
    ∃ ρ : ℕ, ∀ hash : VerifiableInference.Hash,
      ((theWideDigits o).commit Z (settingsOfRead pp) w ρ).evaluate hash =
        (fixedCommit (theWideTerms digitCoins digitWide) Z (settingsOfRead pp) w r σ).evaluate
          hash :=
  coins_enumerated_digits placeHolderNumberCoins (fun n : ℕ => n) o Z pp hr
    (fun n _ => ⟨n, rfl⟩) w r σ hσ

/-- **THE STORED G9 AND G9bits AT THAT CLOSED DESCRIPTION.** -/
theorem G9_digits : G9 theWideDigits := G9_theWide digitCoins digitWide

theorem G9bits_digits : G9bits theWideDigits := G9bits_theWide digitCoins digitWide

/-- The row's form there, from three hypotheses, at a named error. -/
theorem nearestSoundAndBinding_digits
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundAndBinding theWideDigits
      (joinError (epsFrame 0 theQueries) fun t => epsBind honestBudget (t + 2)) :=
  nearestSoundAndBinding_theWide digitCoins digitWide kS eS pS

end FlashProve

#print axioms FlashProve.fieldRows
#print axioms FlashProve.riDigits
#print axioms FlashProve.own_same
#print axioms FlashProve.coins_enumerated_own
#print axioms FlashProve.covers_digits
#print axioms FlashProve.digits_once
#print axioms FlashProve.coins_enumerated_digits
#print axioms FlashProve.coins_enumerated_digits_closed
#print axioms FlashProve.G9_digits
#print axioms FlashProve.G9bits_digits
#print axioms FlashProve.nearestSoundAndBinding_digits

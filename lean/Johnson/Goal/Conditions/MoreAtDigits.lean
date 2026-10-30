-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/MoreAtDigits.lean: WHAT IS NOT TYPED AT `theWideDigits`
(Johnson/Goal/Conditions/WideDigits.lean): the four sizes that Lean had filled
in; the tree's depth, its number of leaves and the salts' lengths; the verifier's count; the
parser's equation; the goals on soundness at exact match. Statements and proofs: each first at
`theWide K W`, K and W letters, then applied. INSTANCES: nothing new is proved.

Main names (namespace `FlashProve`). THE THREE DEBTS, in every statement that names them:
`keySound`, `entrySound`, `proofSound` of the named side, each asked where `protocolDataWellFormed` says yes:
HYPOTHESES HERE; where they are proved, and how far: the head of Johnson/Goal/TopOfThree.lean, limit
(1).
  **`riDigits_sizes`**: `riDigits Z` is the pair of `fieldRows frS.P.v (frS.P.T.l - 402653181)`
    (the pads: 2^v rows; the entries from the cut on) and `fieldRows frS.P.v frS.P.T.r` (the tails):
    by definition: equal by unfolding. So no term of THAT enumeration is hidden.
  `depth_R₀`: the depth at which the salts are enumerated is `frS.P.T.a`: by definition.
  `n_R₀`, `n_depth`: the coding's words have 2^32 places, and that is 2 to the tree's depth: by
    definition.
  **`sMT_R₀`**: THE LENGTH OF THE TREE'S SALTS IS NO NUMERAL OF THE TERM: it is 256 + 8 times the
    salt of the plan that the public files make (`LPFD.Full.saltG (dataAtFiles flashProveData Z).G`): by
    definition. It is 576 just where that plan's salt is 40: a fact on Z's plan, not stated here.
  `sFS_R₀`: the other salts' length is 256: by definition.
  `K_R₀`: the wire's K is the frame's K and one more: by definition: no numeral of the term either.
  `verifierWithin_theWide`, `verifierWithin_digits`: `VerifierWithin` (Ladder/Bits.lean): no debt:
    BY THE GATE: where `protocolDataWellFormed` says no the term lays empty data and refuses all; that it says yes
    at the release's files is an evaluation's matter, typed nowhere here.
  `parse_theWide`, `readMore_theWide`; `parse_digits`, `readMore_digits`: the parser and the
    reading of the further public files are `descriptionOfDataOnBytes flashProveData`'s: at every K and W, and at the
    closed term: by definition.
  `G7_theWide`, `G7bits_theWide`: from the three debts, by the ties of Ladder/Ties.lean and
    Ladder/BitsTies.lean, which hold of every description.
  **`sound_digits`**: G7 ∧ G7bits at `theWideDigits`, from the three debts: ONE CONDITIONAL FACT,
    A COROLLARY OF `allFourGoals_atCoinsListedByDigits` (AllAtDigits.lean): G7 follows from G7bits, G7bits from its G8bits.

Limits. Those of AllAtDigits.lean, all; of them, said here too: what sits in the three seats of
`flashProveData` is told in their own files (Johnson/Goal/Description/KeyFold.lean, ProofFold.lean,
LinkDec.lean); where `protocolDataWellFormed` says no the verifier refuses all and everything here holds for
nothing.
G7' AND G7'bits ARE NOT STATED, ON PURPOSE. `theWide K W` is `fun _ => …`: it does not read the
function that stands in the second hash function's place. So G7'bits would follow from G7bits by
definition, G7' from that by a tie, and both would say no more than it: the head of Ladder.lean (9)
names just this road as worth nothing without a reading of the description's definitions, and says
that a description may not reach a hash function by name. AND `descriptionOfDataOnBytes flashProveData` NAMES THE SECOND
HASH FUNCTION: `flashProveData` is the lay at `OnBytes.secondHashFunction` (`theLayAt_older`,
Johnson/Goal/Description/Lay.lean), and its further public reading is `VerifierAndGoals.readMoreAt`, which
calls the planner's `publicOf`. The description that reads its argument is `VerifierAndGoals.theDescriptionO`
(Johnson/Goal/Description/AtSecondHashFunction.lean); binding over it: Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean.
NO ROW ON G7' OR G7'bits MAY BE COUNTED AT THIS TERM.
The four ties between a run of the programs' rehearsal and `verify` (`theBound_tie` and its three,
Johnson/Goal/Description/AtBound.lean) are that file's and are not carried here: `verify_digits`
(AllAtDigits.lean) is the step that they want. Nothing on completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.AllAtDigits
import Ladder.Ties
import Ladder.BitsTies

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

/-- **The four sizes.** -/
theorem riDigits_sizes (Z : PublicFiles) :
    riDigits Z = (enumPair (fieldRows frS.P.v (frS.P.T.l - 402653181))
      (fieldRows frS.P.v frS.P.T.r) : _root_.Iop.Enum (R₀ Z).protocol.EncodingRandomness) := rfl

/-- The depth at which the salts are enumerated. -/
theorem depth_R₀ (Z : PublicFiles) : (R₀ Z).queryLayout.depth = frS.P.T.a := rfl

/-- The number of places of a word of the coding. -/
theorem n_R₀ (Z : PublicFiles) : (R₀ Z).protocol.wordLength = 2 ^ 32 := rfl

/-- The tree has a leaf for each place of a word. -/
theorem n_depth (Z : PublicFiles) : (R₀ Z).protocol.wordLength = 2 ^ (R₀ Z).queryLayout.depth := rfl

/-- **The length of the tree's salts hangs on the plan that the public files make.** -/
theorem sMT_R₀ (Z : PublicFiles) : (R₀ Z).compilerParameters.sMT = 256 + 8 * LPFD.Full.saltG (dataAtFiles flashProveData Z).G := rfl

/-- The length of the other salts. -/
theorem sFS_R₀ (Z : PublicFiles) : (R₀ Z).compilerParameters.sFS = 256 := rfl

/-- The wire's K hangs on the frame that the public files make. -/
theorem K_R₀ (Z : PublicFiles) : (R₀ Z).queryLayout.K = (dataAtFiles flashProveData Z).toDescriptionFields.K + 1 := rfl

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF descriptionOfDataOnBytes
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins) (W : WideCoins K)

/-- The verifier's count, at every K and W. -/
theorem verifierWithin_theWide (o : SecondHashFunctionType) : VerifierWithin (theWide K W o) :=
  (verifierWithin_wide_iff (theTerms K) W.bound
    fun Z => coinsAnchor Z (K.shape Z) (W.gen Z)).2 (verifierWithin_theBound K o)

/-- The parser is `descriptionOfDataOnBytes flashProveData`'s. -/
theorem parse_theWide (o : SecondHashFunctionType) (Z : PublicFiles) : (theWide K W o).parse Z = flashProveDescription.parse Z := rfl

/-- The reading of the further public files is `descriptionOfDataOnBytes flashProveData`'s. -/
theorem readMore_theWide (o : SecondHashFunctionType) (Z : PublicFiles) : (theWide K W o).readMore Z = flashProveDescription.readMore Z := rfl

theorem G7_theWide
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G7 (theWide K W) := g7_of_g8 _ (G8_theWide K W kS eS pS)

theorem G7bits_theWide
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G7bits (theWide K W) := g7bits_of_g8bits _ (G8bits_theWide K W kS eS pS)

/-! ## At the closed term -/

theorem verifierWithin_digits (o : SecondHashFunctionType) : VerifierWithin (theWideDigits o) :=
  verifierWithin_theWide digitCoins digitWide o

/-- **THE TWO GOALS ON SOUNDNESS AT EXACT MATCH, AT THE ONE CLOSED TERM, FROM THE THREE DEBTS: A
COROLLARY OF `allFourGoals_atCoinsListedByDigits`.** -/
theorem sound_digits
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G7 theWideDigits ∧ G7bits theWideDigits :=
  ⟨G7_theWide digitCoins digitWide kS eS pS, G7bits_theWide digitCoins digitWide kS eS pS⟩

/- Lean compares these two names and does not unfold them. -/
attribute [local irreducible] digitCoins digitWide

theorem parse_digits (o : SecondHashFunctionType) (Z : PublicFiles) : (theWideDigits o).parse Z = flashProveDescription.parse Z :=
  parse_theWide digitCoins digitWide o Z

theorem readMore_digits (o : SecondHashFunctionType) (Z : PublicFiles) : (theWideDigits o).readMore Z = flashProveDescription.readMore Z :=
  readMore_theWide digitCoins digitWide o Z

/- The compiler's input of the closed term has R₀ Z's pads, depth and salts' length. -/
example (Z : PublicFiles) := own_same digitCoins digitWide Z

end FlashProve

#print axioms FlashProve.riDigits_sizes
#print axioms FlashProve.depth_R₀
#print axioms FlashProve.n_R₀
#print axioms FlashProve.n_depth
#print axioms FlashProve.sMT_R₀
#print axioms FlashProve.sFS_R₀
#print axioms FlashProve.K_R₀
#print axioms FlashProve.verifierWithin_theWide
#print axioms FlashProve.parse_theWide
#print axioms FlashProve.readMore_theWide
#print axioms FlashProve.G7_theWide
#print axioms FlashProve.G7bits_theWide
#print axioms FlashProve.verifierWithin_digits
#print axioms FlashProve.sound_digits
#print axioms FlashProve.parse_digits
#print axioms FlashProve.readMore_digits

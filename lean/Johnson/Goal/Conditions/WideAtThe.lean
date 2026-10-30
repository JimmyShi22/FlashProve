-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WideAtThe.lean: BINDING AT THE ONE CLOSED DESCRIPTION WITH THE NUMBER OF THE
COMMITTER'S COINS A LETTER: G9 (Ladder.lean), G9bits (Ladder/Bits.lean) and the row
`top_SoundAndBinding` in its form, of `theWide K W`. Definitions, statements and proofs. Nothing new
is shown: Johnson/Goal/Conditions/ReBound.lean is called at the closed term.

Why. At `descriptionOfDataOnBytes flashProveData` the letter `coinBound` is 0 (`bound_the`, by definition). So at `theBound K`
(Johnson/Goal/Conditions/BindsAtThe.lean), AT EVERY K, the told committer's number is 0: the
randomness and the generator reach nothing in the commitment, and the goals on opening-form binding
there speak of ONE setting of pads, tails and salts (the first members of K's two enumerations): AN
OPENER THAT PICKS ITS OWN COINS IS NOT IN THEM: too weak for a row on opening-form binding.
Here the number ranges over Fin (W.bound Z + 1).

Main names (namespace `FlashProve`).
  `bound_the`: (flashProveDescription.input Z allZeroDigest []).coinBound = 0: rfl.
  `WideCoins K`: bound (at every Z a number) and gen (from the randomness and the key's digest into
    Fin (bound Z + 1)).
  `theWide K W` := fun _ => (flashProveDescription.reBound W.bound).withTerms ((theTerms K).reBound W.bound …): the
    coins' algorithm is `coinsAnchor` at W.gen. `verify_theWide`: its verifier is `descriptionOfDataOnBytes
    flashProveData`'s: rfl.
  **`G9_theWide`**, **`G9bits_theWide`**: NO PREMISE; K and W under "for all".
  **`nearestSoundAndBinding_theWide`**, `nearestSoundOpened_theWide`: from kS, eS, pS where
    `protocolDataWellFormed` says yes, at `joinError (epsFrame 0 theQueries) fun t => epsBind honestBudget (t +
      2)`.

WHAT IS GAINED. K and W are fixed before the hash function is drawn, but ONE pair covers many
settings of coins INSIDE the probability.
  `WideCoins.full K toNat`: bound Z + 1 := the product of the two enumerations' lengths; the number
    is toNat of the randomness, reduced.
  **`full_reaches`**: where toNat reaches every number below that product (the premise onto: a
    finite type of randomness can meet it), EVERY PAIR (a, c) of places in K.ri and K.sl is named by
    some randomness: at every hash function the coins' algorithm gives the number a + (ri.n + 1) c.
  At that number the told scheme's committer is: the public reading, then `committerAtFixedCoins` at
    ((K.ri Z).e a, (K.sl Z).e c): `BindLaws.reaches` (ReBound.lean) at `bindLaws_the`.
So at `theWide K (WideCoins.full K toNat)` the opener of G9 and G9bits may pick ANY pair out of the
two enumerations. THE ERROR DOES NOT GROW WITH bound OR WITH THE ENUMERATIONS' LENGTHS.

Limits. Those of BindsAtThe.lean, RowAtBound.lean and ReBound.lean. Besides:
- WHETHER THE WHOLE SPACE OF COINS IS COVERED HANGS ON K's TWO ENUMERATIONS, which are letters: that
  K.ri lists all pads with tails, and K.sl all salts that the tree reads, is no premise and no
  conclusion: at short ones little is covered. The K that are built are the
  place-holder, whose enumerations have one member each, and its two kin
  (WideOnto.lean: placeHolderNumberCoins; WideDigits.lean: digitCoins).
- The step from the told scheme's committer to the system's (it asks the key's code besides) and to
  `D.commit` is by definition and is not restated.
- `theWide K W` is neither `theBound K` nor `VerifierAndGoals.theDescription`: it parts from the first in
  `coinBound` and the committer; its verifier, parser and extractor are the same terms.
- THE VERIFIER IS IDLE IN G9 AND G9bits. THE COMMITTER IS TIED TO NO PROGRAM. NOTHING ON HIDING OR
  COMPLETENESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.RowAtBound
import Johnson.Goal.Conditions.ReBound

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

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

/-- **At the description as it is laid the number of coins is 0.** -/
theorem bound_the (Z : PublicFiles) : (flashProveDescription.input Z allZeroDigest []).coinBound = 0 := rfl

/- From here on Lean compares the description by its name. -/
attribute [local irreducible] descriptionOfDataOnBytes

/-- The number of the committer's coins, and the generator into it. -/
structure WideCoins (K : TheCoins) where
  bound : PublicFiles → ℕ
  gen : (Z : PublicFiles) → K.Rand → Digest → Fin (bound Z + 1)

variable (K : TheCoins) (W : WideCoins K)

/-- The honest side's terms. -/
def theWideTerms : HonestTerms (flashProveDescription.reBound W.bound) :=
  (theTerms K).reBound W.bound fun Z => coinsAnchor Z (K.shape Z) (W.gen Z)

/-- **The description of which the goals below speak.** -/
def theWide : SecondHashFunctionType → Description := fun _ => (flashProveDescription.reBound W.bound).withTerms (theWideTerms K W)

/-- Its verifier is `descriptionOfDataOnBytes flashProveData`'s. -/
theorem verify_theWide (o : SecondHashFunctionType) (Z : PublicFiles) {Form : Type} (parse : Parser flashProveDescription Z Form) :
    verify (theWide K W o) Z parse = verify flashProveDescription Z parse :=
  (verify_withTerms (theWideTerms K W) Z parse).trans (verify_reBound flashProveDescription W.bound Z parse)

/-- The laws that opening-form binding (`BindsWith`) owes. -/
theorem bindLaws_wide (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) :
    BindLaws (theWideTerms K W) Z (settingsOfRead pp) 8 2 :=
  (bindLaws_the K hE_the Z pp hr).reBound (theTerms K) W.bound _
    (fun ρ => queryBound_coinsAnchor Z (K.shape Z) (W.gen Z) ρ) (bindLaws_the K hE_the Z pp
    hr).number

/-- **THE STORED G9: NO PREMISE.** -/
theorem G9_theWide : G9 (theWide K W) :=
  G9_withTerms (fun _ => flashProveDescription.reBound W.bound) (fun _ => theWideTerms K W) 8 2 (by
                       have h1 : honestBudget = 2 ^ 48 := rfl
                       rw [h1]
                       norm_num) fun Z pp _ h₂ => bindLaws_wide K W Z pp h₂

/-- **THE STORED G9bits: NO PREMISE.** -/
theorem G9bits_theWide : G9bits (theWide K W) :=
  G9bits_withTerms (fun _ => flashProveDescription.reBound W.bound) (fun _ => theWideTerms K W) 8 2 (by norm_num)
    fun Z pp _ h₂ => bindLaws_wide K W Z pp h₂

/-- **THE ROW's FORM, FROM THREE DEBTS, AT A NAMED ERROR.** -/
theorem nearestSoundAndBinding_theWide
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundAndBinding (theWide K W)
      (joinError (epsFrame 0 theQueries) fun t => epsBind honestBudget (t + 2)) :=
  nearestSoundAndBinding_withTerms (fun _ => flashProveDescription.reBound W.bound) (fun _ => theWideTerms K W) 8 2
    (epsFrame 0 theQueries)
    (soundUnderPolicyAt_reBound (theTerms K) W.bound _ (epsFrame 0 theQueries)
      (soundUnderPolicyAt_theBound K thePsi 1 128 0 rfl le_self_add he_the kS eS pS))
    fun Z pp _ h₂ => bindLaws_wide K W Z pp h₂

/-- Likewise `SoundOpened`, at twice that error. -/
theorem nearestSoundOpened_theWide
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundOpened (theWide K W) fun t =>
      2 * joinError (epsFrame 0 theQueries) (fun t => epsBind honestBudget (t + 2)) t :=
  nearestSoundOpened_of_at (theWide K W) (epsFrame 0 theQueries) _
    (soundUnderPolicyAt_reBound (theTerms K) W.bound _ (epsFrame 0 theQueries)
      (soundUnderPolicyAt_theBound K thePsi 1 128 0 rfl le_self_add he_the kS eS pS))
    (bindsAt_withTerms (theWideTerms K W) 8 2 fun Z pp _ h₂ => bindLaws_wide K W Z pp h₂)

/-! ## How far it reaches -/

/-- **The widest value**: as many numbers as there are pairs out of K's two enumerations; the number
is made of the randomness by toNat, whatever the key's digest is. -/
def WideCoins.full (toNat : K.Rand → ℕ) : WideCoins K where
  bound := fun Z => ((K.ri Z).n + 1) * ((K.sl Z).n + 1) - 1
  gen := fun Z ρ _ =>
    ⟨toNat ρ % (((K.ri Z).n + 1) * ((K.sl Z).n + 1) - 1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- **EVERY PAIR OUT OF THE TWO ENUMERATIONS IS NAMED BY SOME RANDOMNESS**, where toNat reaches
every number below the product of the two lengths (onto; a finite type of randomness can meet it):
there is ρ at which, at every hash function, the coins' algorithm gives the number
a + (ri.n + 1) c: the number at which the committer behind the public reading runs at
(ri.e a, sl.e c) (`commitBehind_reach`, Johnson/Top/ToldReach.lean). -/
theorem full_reaches (toNat : K.Rand → ℕ) (Z : PublicFiles)
    (onto : ∀ n, n < ((K.ri Z).n + 1) * ((K.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (a : Fin ((K.ri Z).n + 1)) (c : Fin ((K.sl Z).n + 1)) :
    ∃ ρ : K.Rand, ∀ hash : VerifiableInference.Hash,
      (((theWideTerms K (WideCoins.full K toNat)).coins Z ρ).evaluate hash).val =
        a.val + ((K.ri Z).n + 1) * c.val := by
  have h := (reach_pair (K.ri Z).n (K.sl Z).n a.val c.val a.isLt c.isLt).2.2
  obtain ⟨ρ, hρ⟩ := onto _ h
  refine ⟨ρ, fun hash => ?_⟩
  show toNat ρ % (((K.ri Z).n + 1) * ((K.sl Z).n + 1) - 1 + 1) = _
  rw [hρ, Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))),
    Nat.mod_eq_of_lt h]

end FlashProve

#print axioms FlashProve.full_reaches
#print axioms FlashProve.bound_the
#print axioms FlashProve.verify_theWide
#print axioms FlashProve.G9_theWide
#print axioms FlashProve.G9bits_theWide
#print axioms FlashProve.nearestSoundAndBinding_theWide
#print axioms FlashProve.nearestSoundOpened_theWide

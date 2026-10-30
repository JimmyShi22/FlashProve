-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WideOnto.lean: AT THE ONE CLOSED DESCRIPTION WITH THE NUMBER OF COINS A
LETTER (`theWide K W`, Johnson/Goal/Conditions/WideAtThe.lean): A VALUE OF THE LETTERS AT WHICH THE
OPENER OF THE GOALS ON BINDING MAY PICK ANY COINS: all pads with tails; all salts of the length that
the verifier asks, as far as the tree reads them. Definitions, statements and proofs.

Why. `G9_theWide` and `G9bits_theWide` hold at every K and W, and `full_reaches` shows that at
`WideCoins.full` every pair out of K's two enumerations is named by some randomness. Whether that is
the whole space of coins hangs on the two enumerations, which are letters.

Main names (namespace `FlashProve`).
  `K.onto`: K with ri := all members of the type of pads with tails (`enumAll`) and sl := all salts
    of compilerParameters.sMT bits at each of the first 2^depth places (`saltsAll`; Johnson/Top/ToldReachAll.lean).
  **`all_coins_reached`**: where toNat reaches every number below the product of the two lengths:
    for every r (pads with tails) and all salts σ of compilerParameters.sMT bits at each of the tree's 2^depth places
    there are ρ, a, c with: entry a of `K.onto`'s first enumeration is r; entry c of its second
    agrees with σ at all these places; and at every hash function the coins' algorithm of `theWide
    K.onto (WideCoins.full K.onto toNat)` gives at ρ the number a + (ri.n + 1) c: at which the told
    scheme's committer runs `committerAtFixedCoins` at these two entries (`BindLaws.reaches`,
    Johnson/Goal/Conditions/ReBound.lean), and the tree is the tree at σ (`committerTreeRoot_congr`).
  `G9_onto`, `G9bits_onto`: the two goals at that value: instances of `G9_theWide`,
    `G9bits_theWide`.
  `placeHolderNumberCoins`, `theWideOpen`, **`all_coins_reached_open`**, **`G9_open`**,
    **`G9bits_open`**: A CLOSED VALUE AT WHICH THE PREMISE IS MET: the randomness's type is the
    numbers, toNat the identity: the opener names the number outright. A place-holder in all its
    other fields.

SO AT THIS VALUE AN OPENER THAT PICKS ITS OWN PADS, TAILS AND SALTS (of the length that the verifier
asks) IS IN G9 AND G9bits, INSIDE THE PROBABILITY, AT THE SAME ERROR.

Limits. Those of WideAtThe.lean and ToldReachAll.lean. Besides:
- `K.onto`'s ENUMERATIONS ARE PICKED BY CHOICE: a witness for how far the theorems reach; NOT a
  committer that runs, and so not a value for a description whose running fields may use no choice
  (the head of Ladder.lean).
- Salts of another length at a place that the tree reads are not covered.
- At `theWideOpen` the randomness's type is the numbers and its sampler gives 0: nothing is drawn,
  so nothing on hiding. A finite type that reaches the numbers below the product meets the premise
  as well; none is built. That the number of a drawn randomness is uniform is a matter for a row on
  hiding.
- ONE TO ONE: each enumeration lists every value once, and each pair of places has one number below
  the product (`enumAll_once`, `saltsAll_once`, `pair_once`, Johnson/Top/ToldReachAll.lean): stated
  there, not joined here.
- That the key reads the salts through the tree alone is seen at `committerAtFixedCoins`'s text, not restated.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WideAtThe
import Johnson.Top.ToldReachAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-- The compiler's input at which the told record is taken. -/
abbrev R₀ (Z : PublicFiles) : InnerCompilerInput := flashProveDescription.input Z allZeroDigest []

/- From here on Lean compares the description by its name. -/
attribute [local irreducible] descriptionOfDataOnBytes

/-- **K with enumerations that cover the whole space of coins.** -/
def TheCoins.onto (K : TheCoins) : TheCoins :=
  { K with
    ri := fun Z => enumAll (R₀ Z).protocol.EncodingRandomness
    sl := fun Z => saltsAll (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT }

variable (K : TheCoins)

/-- **EVERY SETTING OF COINS IS NAMED BY SOME RANDOMNESS.** -/
theorem all_coins_reached (toNat : K.Rand → ℕ) (Z : PublicFiles)
    (onto : ∀ n, n < ((K.onto.ri Z).n + 1) * ((K.onto.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (r : (R₀ Z).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth →
      (σ j).length = (R₀ Z).compilerParameters.sMT) :
    ∃ (ρ : K.Rand) (a : Fin ((K.onto.ri Z).n + 1)) (c : Fin ((K.onto.sl Z).n + 1)),
      (K.onto.ri Z).e a = r ∧
      (∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (K.onto.sl Z).e c j = σ j) ∧
      ∀ hash : VerifiableInference.Hash,
        (((theWideTerms K.onto (WideCoins.full K.onto toNat)).coins Z ρ).evaluate hash).val =
          a.val + ((K.onto.ri Z).n + 1) * c.val := by
  obtain ⟨a, ha⟩ := enumAll_onto (R₀ Z).protocol.EncodingRandomness r
  obtain ⟨c, hc⟩ := saltsAll_covers (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT σ hσ
  obtain ⟨ρ, hρ⟩ := full_reaches K.onto toNat Z onto a c
  exact ⟨ρ, a, c, ha, hc, hρ⟩

/-- The stored G9 at that value. -/
theorem G9_onto (toNat : K.Rand → ℕ) : G9 (theWide K.onto (WideCoins.full K.onto toNat)) :=
  G9_theWide K.onto (WideCoins.full K.onto toNat)

/-- The stored G9bits at that value. -/
theorem G9bits_onto (toNat : K.Rand → ℕ) :
    G9bits (theWide K.onto (WideCoins.full K.onto toNat)) :=
  G9bits_theWide K.onto (WideCoins.full K.onto toNat)

/-! ## A closed value, so that the premise is met -/

/-- **A PLACE-HOLDER IN ALL BUT ONE FIELD**: `placeHolderCoins`
(Johnson/Goal/Conditions/PlaceHolderCoins.lean) with the numbers for the randomness's type: the
opener names a number. Its sampler gives 0; its provers hand over empty things. -/
def placeHolderNumberCoins : TheCoins :=
  { placeHolderCoins with
    Rand := ℕ
    sample := .done 0
    gen := fun _ _ _ => 0
    prove := fun _ _ _ _ _ _ => .done
      ⟨[], ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩ }

/-- The closed description at which the opener may pick any coins. -/
def theWideOpen : SecondHashFunctionType → Description :=
  theWide placeHolderNumberCoins.onto
    (WideCoins.full placeHolderNumberCoins.onto (fun n : ℕ => n))

/-- **At it every setting of coins is named by a number.** -/
theorem all_coins_reached_open (Z : PublicFiles) (r : (R₀ Z).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth →
      (σ j).length = (R₀ Z).compilerParameters.sMT) :
    ∃ (ρ : ℕ) (a : Fin ((placeHolderNumberCoins.onto.ri Z).n + 1))
      (c : Fin ((placeHolderNumberCoins.onto.sl Z).n + 1)),
      (placeHolderNumberCoins.onto.ri Z).e a = r ∧
      (∀ j, j < 2 ^ (R₀ Z).queryLayout.depth →
        (placeHolderNumberCoins.onto.sl Z).e c j = σ j) ∧
      ∀ hash : VerifiableInference.Hash,
        (((theWideTerms placeHolderNumberCoins.onto
          (WideCoins.full placeHolderNumberCoins.onto (fun n : ℕ => n))).coins Z ρ).evaluate
            hash).val = a.val + ((placeHolderNumberCoins.onto.ri Z).n + 1) * c.val :=
  all_coins_reached placeHolderNumberCoins (fun n : ℕ => n) Z (fun n _ => ⟨n, rfl⟩) r σ hσ

/-- **THE STORED G9 AND G9bits AT THAT CLOSED DESCRIPTION.** -/
theorem G9_open : G9 theWideOpen := G9_onto placeHolderNumberCoins fun n : ℕ => n

theorem G9bits_open : G9bits theWideOpen := G9bits_onto placeHolderNumberCoins fun n : ℕ => n

end FlashProve

#print axioms FlashProve.all_coins_reached_open
#print axioms FlashProve.G9_open
#print axioms FlashProve.G9bits_open
#print axioms FlashProve.all_coins_reached
#print axioms FlashProve.G9_onto
#print axioms FlashProve.G9bits_onto

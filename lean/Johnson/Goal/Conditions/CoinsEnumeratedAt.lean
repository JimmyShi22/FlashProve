-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/CoinsEnumeratedAt.lean: "EVERY SETTING OF COINS IS REACHED", AT THE
DESCRIPTION'S OWN COMMITTER AND AT THE GIVEN SALTS THEMSELVES. Statements and proofs.

Why. `coins_enumerated` (Johnson/Goal/Conditions/CoinsEnumerated.lean) ends at salts σ₁ that agree
with the given σ wherever the tree reads. That the two committers with the coins fixed have one
value is not stated there. Here it is, and the statement is made again
without σ₁; and general in K, so that it serves every K whose two enumerations cover the coins.

Main names.
  `fixedCommit_salts` (namespace `VerifierAndGoals.Fit`): general in D and Q: `fixedCommit Q Z s w r σ` and
    `fixedCommit Q Z s w r σ'` are one algorithm where σ and σ' agree at the tree's 2^depth places.
    Premise: `BindLaws` (of it: the public reading draws nothing).
  `K.Covers Z` (namespace `FlashProve`): K's first enumeration at Z is onto the pads with tails; its
    second has, for all salts of compilerParameters.sMT bits at each of the tree's 2^depth places, an entry that
    agrees with them at these places.
  **`coins_enumerated_of`**: at `theWide K (WideCoins.full K toNat)`, where K covers at Z and toNat
    reaches every number below the product of the two lengths; at every Z that the reader reads,
    all weights w, every r and all salts σ of compilerParameters.sMT bits at each of the tree's places: THERE IS ρ
    WITH: AT EVERY HASH FUNCTION THE VALUE OF THE DESCRIPTION'S COMMITTER AT (w, ρ) IS THE VALUE OF
    THE COMMITTER WITH THE COINS (r, σ) FIXED.
  `covers_onto`; **`coins_enumerated_at`**, **`coins_enumerated_at_open`**: so at `K.onto`, and at
    the closed `theWideOpen` (Johnson/Goal/Conditions/WideOnto.lean): no premise, no letter.

Limits. Those of WideOnto.lean at `K.onto` (its enumerations are picked by choice). Salts of another
length at a place that the tree reads are not covered. An equation between values of terms of this
library: nothing on any program. OF THE COMMITMENT ALONE: what the committer keeps for its prover
holds the salts whole, and differs.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.CoinsEnumerated
import Johnson.Top.ToldCommitSalts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom

variable {D : Description} {Q : HonestTerms D}

/-- **The committer with the coins fixed reads the salts at the tree's places alone.** -/
theorem fixedCommit_salts {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (w : ModelWeights s) (r : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness)
    (σ σ' : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout.depth → σ j = σ' j) :
    fixedCommit Q Z s w r σ = fixedCommit Q Z s w r σ' :=
  commit_systemOn_salts (Q.T Z) (Q.b₀ Z) (Q.proveT Z) (Q.back Z s) (modelNextToken s) h.noCoin w r
    σ σ' hσ

end VerifierAndGoals.Fit

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares the description by its name. -/
attribute [local irreducible] descriptionOfDataOnBytes

/-- **K's two enumerations cover the coins at Z.** -/
def TheCoins.Covers (K : TheCoins) (Z : PublicFiles) : Prop :=
  Function.Surjective (K.ri Z).e ∧
    ∀ σ : ℕ → Rom.Bits, (∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (σ j).length = (R₀ Z).compilerParameters.sMT) →
      ∃ c, ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (K.sl Z).e c j = σ j

variable (K : TheCoins)

/-- **EVERY SETTING OF COINS IS REACHED, AT THE DESCRIPTION'S OWN COMMITTER.** -/
theorem coins_enumerated_of (toNat : K.Rand → ℕ) (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (hK : K.Covers Z)
    (onto : ∀ n, n < ((K.ri Z).n + 1) * ((K.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (w : ModelWeights (settingsOfRead pp)) (r : (R₀ Z).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (σ j).length = (R₀ Z).compilerParameters.sMT) :
    ∃ ρ : K.Rand, ∀ hash : VerifiableInference.Hash,
      ((theWide K (WideCoins.full K toNat) o).commit Z (settingsOfRead pp) w ρ).evaluate hash =
        (fixedCommit (theWideTerms K (WideCoins.full K toNat)) Z (settingsOfRead pp) w r
          σ).evaluate hash := by
  obtain ⟨a, ha⟩ := hK.1 r
  obtain ⟨c, hc⟩ := hK.2 σ hσ
  obtain ⟨ρ, hρ⟩ := full_reaches K toNat Z onto a c
  refine ⟨ρ, fun hash => ?_⟩
  have laws := bindLaws_wide K (WideCoins.full K toNat) Z pp hr
  have key := commit_withTerms_reach laws w ρ hash a c (hρ hash)
  rw [← fixedCommit_salts laws w r ((K.sl Z).e c) σ hc, ← ha]
  exact key

/-- `K.onto` covers, at every Z. -/
theorem covers_onto (Z : PublicFiles) : K.onto.Covers Z :=
  ⟨enumAll_onto (R₀ Z).protocol.EncodingRandomness, saltsAll_covers (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT⟩

/-- So at `K.onto`. -/
theorem coins_enumerated_at (toNat : K.Rand → ℕ) (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp)
    (onto : ∀ n, n < ((K.onto.ri Z).n + 1) * ((K.onto.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (w : ModelWeights (settingsOfRead pp)) (r : (R₀ Z).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (σ j).length = (R₀ Z).compilerParameters.sMT) :
    ∃ ρ : K.Rand, ∀ hash : VerifiableInference.Hash,
      ((theWide K.onto (WideCoins.full K.onto toNat) o).commit Z (settingsOfRead pp) w
        ρ).evaluate hash =
        (fixedCommit (theWideTerms K.onto (WideCoins.full K.onto toNat)) Z (settingsOfRead pp) w r
          σ).evaluate hash :=
  coins_enumerated_of K.onto toNat o Z pp hr (covers_onto K Z) onto w r σ hσ

/-- **And at the closed description: no premise, no letter.** -/
theorem coins_enumerated_at_open (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (r : (R₀ Z).protocol.EncodingRandomness)
    (σ : ℕ → Rom.Bits) (hσ : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (σ j).length = (R₀ Z).compilerParameters.sMT) :
    ∃ ρ : ℕ, ∀ hash : VerifiableInference.Hash,
      ((theWideOpen o).commit Z (settingsOfRead pp) w ρ).evaluate hash =
        (fixedCommit (theWideTerms placeHolderNumberCoins.onto
          (WideCoins.full placeHolderNumberCoins.onto (fun n : ℕ => n))) Z (settingsOfRead pp) w r
          σ).evaluate hash :=
  coins_enumerated_at placeHolderNumberCoins (fun n : ℕ => n) o Z pp hr (fun n _ => ⟨n, rfl⟩) w r σ
    hσ

end FlashProve

#print axioms VerifierAndGoals.Fit.fixedCommit_salts
#print axioms FlashProve.coins_enumerated_of
#print axioms FlashProve.coins_enumerated_at
#print axioms FlashProve.coins_enumerated_at_open

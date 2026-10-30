-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/CoinsEnumerated.lean: "EVERY SETTING OF COINS IS REACHED", SAID OF THE TERM
OF WHICH THE GOALS ON BINDING SPEAK: THE DESCRIPTION'S OWN COMMITTER. Statements and proofs: one
general in the description, one at the closed description.

Why. That the opener of G9 and G9bits may pick any coins stood in three pieces: the coins'
algorithm's value (`full_reaches`, `all_coins_reached`), the told SCHEME's committer at that number
(`BindLaws.reaches`), the tree (`committerTreeRoot_congr`). No statement named `D.commit`.
Here they are joined.

Main names.
  `fixedCommit Q Z s w r σ` (namespace `VerifierAndGoals.Fit`): THE COMMITTER WITH THE COINS (r, σ) FIXED: the
    told system's committer where both enumerations have one member, r and σ, at the number 0.
  **`commit_withTerms_reach`**: general in D and Q: where the coins' algorithm gives, at ρ and a
    hash function, the number a + (ri.n + 1) c: the value of `(D.withTerms Q).commit Z s w ρ` at
    that hash function is the value of `fixedCommit` at ((Q.ri Z).e a, (Q.sl Z).e c). Premise:
    `BindLaws` (of it: the public reading draws nothing).
  **`coins_enumerated`** (namespace `FlashProve`): at `theWide K.onto (WideCoins.full K.onto toNat)`
    (Johnson/Goal/Conditions/WideOnto.lean), at every Z that the reader reads, all weights w, every
    r (pads with tails) and all salts σ of compilerParameters.sMT bits at each of the tree's 2^depth places: there
    are ρ and salts σ₁ that agree with σ at all these places, with: AT EVERY HASH FUNCTION the value
    of the description's committer at (w, ρ) is the value of the committer with the coins (r, σ₁)
    fixed.
  `coins_enumerated_open`: the same at the closed `theWideOpen`: no premise, no letter.

Limits. Those of WideOnto.lean, all: the enumerations are picked by choice; salts of another length
are not covered. σ₁ AND NOT σ: the two agree wherever the tree reads (`committerTreeRoot_congr`,
Johnson/Top/ToldReachAll.lean), and the salts enter the key through the tree alone (seen at
`committerAtFixedCoins`'s text); that the two fixed committers are one algorithm is not stated. An equation
between values of terms of this library: nothing on any program.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WideOnto
import Johnson.Top.ToldCommitAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom

variable {D : Description} (Q : HonestTerms D)

/-- **The committer with the coins (r, σ) fixed.** -/
def fixedCommit (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s)
    (r : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits) :
    DeterministicAlgorithm Commitment :=
  (((Q.T Z).withCommit (enumOne r) (enumOne σ) (Q.b₀ Z) (Q.proveT Z)).systemOn (Q.back Z s)
    (modelNextToken s)).commit w
      (⟨0, Nat.succ_pos _⟩ : Fin ((D.input Z (Q.c₀ Z) (Q.m₀ Z)).coinBound + 1))

variable {Q}

/-- **THE DESCRIPTION'S COMMITTER AT A RANDOMNESS THAT NAMES THE NUMBER OF A PAIR.** -/
theorem commit_withTerms_reach {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (w : ModelWeights s) (ρ : Q.Rand) (hash : Hash)
    (a : Fin ((Q.ri Z).n + 1)) (c : Fin ((Q.sl Z).n + 1))
    (hv : ((Q.coins Z ρ).evaluate hash).val = a.val + ((Q.ri Z).n + 1) * c.val) :
    ((D.withTerms Q).commit Z s w ρ).evaluate hash =
      (fixedCommit Q Z s w ((Q.ri Z).e a) ((Q.sl Z).e c)).evaluate hash := by
  have hn : a.val + ((Q.ri Z).n + 1) * c.val < (D.input Z (Q.c₀ Z) (Q.m₀ Z)).coinBound + 1 :=
    hv ▸ ((Q.coins Z ρ).evaluate hash).isLt
  have e : (Q.coins Z ρ).evaluate hash = ⟨a.val + ((Q.ri Z).n + 1) * c.val, hn⟩ := Fin.ext hv
  show ((Q.coins Z ρ).andThen fun n =>
    ((Q.told Z).systemOn (Q.back Z s) (modelNextToken s)).commit w n).evaluate hash = _
  rw [DeterministicAlgorithm.evaluate_andThen, e]
  exact congrArg (fun A : DeterministicAlgorithm Commitment => A.evaluate hash)
    (commit_systemOn_reach (Q.T Z) (Q.ri Z) (Q.sl Z) (Q.b₀ Z) (Q.proveT Z) (Q.back Z s)
      (modelNextToken s) h.noCoin w a c hn)

end VerifierAndGoals.Fit

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares the description by its name. -/
attribute [local irreducible] descriptionOfDataOnBytes

variable (K : TheCoins)

/-- **EVERY SETTING OF COINS IS REACHED, AT THE DESCRIPTION'S OWN COMMITTER.** -/
theorem coins_enumerated (toNat : K.Rand → ℕ) (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp)
    (onto : ∀ n, n < ((K.onto.ri Z).n + 1) * ((K.onto.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (w : ModelWeights (settingsOfRead pp)) (r : (R₀ Z).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits)
    (hσ : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (σ j).length = (R₀ Z).compilerParameters.sMT) :
    ∃ (ρ : K.Rand) (σ₁ : ℕ → Rom.Bits), (∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → σ₁ j = σ j) ∧
      ∀ hash : VerifiableInference.Hash,
        ((theWide K.onto (WideCoins.full K.onto toNat) o).commit Z (settingsOfRead pp) w
          ρ).evaluate hash =
        (fixedCommit (theWideTerms K.onto (WideCoins.full K.onto toNat)) Z (settingsOfRead pp) w r
          σ₁).evaluate hash := by
  obtain ⟨ρ, a, c, ha, hc, hv⟩ := all_coins_reached K toNat Z onto r σ hσ
  refine ⟨ρ, (K.onto.sl Z).e c, hc, fun hash => ?_⟩
  have key := commit_withTerms_reach
    (bindLaws_wide K.onto (WideCoins.full K.onto toNat) Z pp hr) w ρ hash a c (hv hash)
  rw [← ha]
  exact key

/-- The same at the closed description. -/
theorem coins_enumerated_open (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (r : (R₀ Z).protocol.EncodingRandomness)
    (σ : ℕ → Rom.Bits) (hσ : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (σ j).length = (R₀ Z).compilerParameters.sMT) :
    ∃ (ρ : ℕ) (σ₁ : ℕ → Rom.Bits), (∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → σ₁ j = σ j) ∧
      ∀ hash : VerifiableInference.Hash,
        ((theWideOpen o).commit Z (settingsOfRead pp) w ρ).evaluate hash =
        (fixedCommit (theWideTerms placeHolderNumberCoins.onto
          (WideCoins.full placeHolderNumberCoins.onto (fun n : ℕ => n))) Z (settingsOfRead pp) w r
          σ₁).evaluate hash :=
  coins_enumerated placeHolderNumberCoins (fun n : ℕ => n) o Z pp hr (fun n _ => ⟨n, rfl⟩) w r σ hσ

end FlashProve

#print axioms VerifierAndGoals.Fit.commit_withTerms_reach
#print axioms FlashProve.coins_enumerated
#print axioms FlashProve.coins_enumerated_open

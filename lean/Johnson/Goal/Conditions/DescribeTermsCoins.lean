-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/DescribeTermsCoins.lean: THE COINS' ALGORITHM OF
Johnson/Top/CoinsAnchor.lean LAID INTO THE HONEST SIDE'S TERMS OF
Johnson/Goal/Conditions/DescribeTerms.lean: the clause `coinsWithin` of `BindLaws` then holds at q
:= 2. A definition and a statement with its proof.

Main names (namespace `VerifierAndGoals.Fit`).
  `Q.withAnchorCoins S gen`: Q with `coins` := `coinsAnchor Z (S Z) (gen Z)`: the configuration's
    digest, the digest of the four items of the anchor's commit run, then gen.
  **`coinsWithin_withAnchorCoins`**: it asks at most 2 queries, at every Z and all randomness.

WHO READS EACH LETTER. S (at every Z the stored table's shape, as bytes): the second string. gen (at
every Z, from the randomness and the second answer to the told committer's number): the result
alone. Both under "for all". The other fields are Q's. No verifier reads anything here.

Limits. Those of the two files named above: gen and S are letters; the committer is tied to no
program; nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.DescribeTerms
import Johnson.Top.CoinsAnchor

set_option autoImplicit false

namespace VerifierAndGoals.Fit
open VerifiableInference

variable {D : Description} (Q : HonestTerms D) (S : PublicFiles → ByteArray)
  (gen : (Z : PublicFiles) → Q.Rand → Digest → Fin ((D.input Z (Q.c₀ Z) (Q.m₀ Z)).coinBound + 1))

/-- The terms with the coins' algorithm of the anchor's commit run. -/
noncomputable def HonestTerms.withAnchorCoins : HonestTerms D :=
  { Q with coins := fun Z => coinsAnchor Z (S Z) (gen Z) }

/-- **The coins' algorithm asks at most twice.** -/
theorem coinsWithin_withAnchorCoins (Z : PublicFiles) (ρ : Q.Rand) :
    ((Q.withAnchorCoins S gen).coins Z ρ).toRandomized.QueryBound 2 :=
  queryBound_coinsAnchor Z (S Z) (gen Z) ρ

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.coinsWithin_withAnchorCoins

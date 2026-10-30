-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CoinsThere.lean: kind K13: THE LIST OF COINS THAT `CoinsTie`
(ExchangeAtM3.lean of this folder) READS HAS AN ENTRY AT EVERY NUMBER AT WHICH IT IS READ.
`CoinsTie` writes "(coinsE c.2.1.2.1.1).getD j zeroE", at j below 2 * kCol + 1: a projection out of
the row's coins, an index and a default. Three statements with their proofs; no definition. General
in the reader, the filler, the plan and the types: no hypothesis, no `Script`, no book.
Main names:
  `k13_ownRun`: the masked sum's own run at the kind's shape has 2 * k + 1 coins.
  `k13_coins_length`: **the list has just 2 * kCol + 1 entries**, at every value of the row's coins.
  `k13_coin_there`: **so the default is not reached**: at each j below 2 * kCol + 1 the list has an
    entry, and getD returns it.

Limits. Counts and an index alone: nothing is said of any coin's value, of how the coins are drawn,
or of which entries of the book they are. That the book lends the row its coins at all (`lendRow`
returns) is a premise inside `CoinsTie`; LendRowOfFit.lean of this folder has a conditional law on
that return, at the chain number 0 and at `k13Place P`: none of its premises is shown there, nor
that these are the thread's chain number and the member's place, at which `CoinsTie` asks it.
Nothing outside this file calls these statements.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.Part.MaskedSum (ownSlots ownSlots_one_add Var)

variable {W₀ Rc Xi Tr X : Type}

/-- The masked sum's own run at kind K13's shape: one coin and two for each of the k variables. -/
theorem k13_ownRun (k : Nat) : ownRun (k13Shape k) = 2 * k + 1 := by
  show 0 + ownSlots (List.replicate k (Var.plain 3)) = 2 * k + 1
  rw [ownSlots_one_add, List.map_replicate, List.sum_replicate]
  show 0 + (1 + k * 2) = 2 * k + 1
  omega

/-- **The list of coins that `CoinsTie` reads has just 2 * kCol + 1 entries**, at every value of the
row's coins. -/
theorem k13_coins_length (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts) :
    (coinsE c.2.1.2.1.1).length = 2 * P.lin.kCol + 1 := by
  unfold coinsE
  rw [List.length_ofFn]
  exact k13_ownRun P.lin.kCol

/-- **So the default of `CoinsTie`'s "getD j zeroE" is not reached**: at each j below 2 * kCol + 1
the list has an entry, and getD returns it. -/
theorem k13_coin_there (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts)
    (j : Nat) (hj : j < 2 * P.lin.kCol + 1) :
    (coinsE c.2.1.2.1.1)[j]? = some ((coinsE c.2.1.2.1.1).getD j zeroE) := by
  have h : j < (coinsE c.2.1.2.1.1).length := by
    rw [k13_coins_length]
    exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_ownRun
#print axioms ProofFile.Honest.K13.k13_coins_length
#print axioms ProofFile.Honest.K13.k13_coin_there

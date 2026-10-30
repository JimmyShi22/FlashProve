-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/WithCoinsBind.lean: four lemmas on an algorithm run at a given number (`OComp.withCoins`,
ZKCP/CoinsFirst.lean), three of them where a part of it samples nothing.

  `OComp.DrawsNoCoin.mapO`                   a function of the result samples nothing more
  `OComp.withCoins_of_drawsNoCoin`           an algorithm that samples nothing is the same at every
                                             number
  `OComp.withCoins_bind_of_drawsNoCoin`      before a second part that samples nothing, the number
                                             goes to the first part
  `OComp.support_run_withCoins`              what an algorithm returns at a given number, it can
                                             return
-/
import ZKCP.CoinsFirst

set_option autoImplicit false

namespace ZKCP

namespace OComp

variable {lam : ℕ} {α β : Type}

/-- A function of the result samples nothing more. -/
theorem DrawsNoCoin.mapO (h : α → β) : ∀ c : OComp lam α, c.DrawsNoCoin → (c.mapO h).DrawsNoCoin
  | pure _, _ => trivial
  | query _ k, hc => fun r => DrawsNoCoin.mapO h (k r) (hc r)
  | sample _ _, hc => hc.elim

/-- An algorithm that samples nothing is the same at every number. -/
theorem withCoins_of_drawsNoCoin : ∀ (c : OComp lam α) (coins : ℕ), c.DrawsNoCoin →
    c.withCoins coins = c
  | pure _, _, _ => rfl
  | query q k, coins, h =>
      congrArg (query q) (funext fun r => withCoins_of_drawsNoCoin (k r) coins (h r))
  | sample _ _, _, h => h.elim

/-- Before a second part that samples nothing, the number goes to the first part. -/
theorem withCoins_bind_of_drawsNoCoin (g : α → OComp lam β) (hg : ∀ a, (g a).DrawsNoCoin) :
    ∀ (c : OComp lam α) (coins : ℕ), (c.bind g).withCoins coins = (c.withCoins coins).bind g
  | pure a, coins => withCoins_of_drawsNoCoin (g a) coins (hg a)
  | query q k, coins =>
      congrArg (query q) (funext fun r => withCoins_bind_of_drawsNoCoin g hg (k r) coins)
  | sample _ k, _ => withCoins_bind_of_drawsNoCoin g hg (k _) _

/-- What an algorithm returns at a given number, it can return. -/
theorem support_run_withCoins (f : Oracle lam) : ∀ (c : OComp lam α) (coins : ℕ),
    ((c.withCoins coins).run f).support ⊆ (c.run f).support
  | pure _, _ => fun _ h => h
  | query q k, coins => support_run_withCoins f (k (f q)) coins
  | sample _ k, _ => fun _ h =>
      (PMF.mem_support_bind_iff _ _ _).2
        ⟨_, PMF.mem_support_uniformOfFintype _, support_run_withCoins f (k _) _ h⟩

end OComp

end ZKCP

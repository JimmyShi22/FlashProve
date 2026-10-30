-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/WithCoins.lean: an algorithm over a family of oracles, run at a given number.

`OComp.withCoins` is `ZKCP.OComp.withCoins` (ZKCP/CoinsFirst.lean) for the algorithms of
Rom/OComp.lean: the random choices are read off one number, and nothing is sampled.
It makes no more queries (`OComp.QueryBound.withCoins`), and it can be applied before or after
  a first part that samples nothing         `OComp.withCoins_bind_of_noCoin`
  a function of the result                  `OComp.withCoins_bind_pure`
  the step to one oracle                    `withCoins_overOne` (Rom/Family.lean)
  the step to the trees of ZKCP/Defs.lean   `withCoins_ofRom` (Rom/Bridge.lean)
So a scheme over a family of oracles, run at a number and then brought to one oracle and to the
syntax of ZKCP/Defs.lean, is the scheme brought there and then run at that number
(`oneOf_overOneArg_atCoins`).
-/
import ZKCP.AtCoins
import ZKCP.SpecialAny
import Rom.NoCoinExits

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {lam : ℕ} {α β : Type}

/-- The algorithm with its random choices read off the number `coins`, and none sampled. Where the
algorithm samples from 0, …, n, this one takes the remainder of `coins` by n + 1 as the sample and
continues with the quotient as the number. -/
def OComp.withCoins : OComp S α → ℕ → OComp S α
  | .pure a, _ => .pure a
  | .query o q k, coins => .query o q fun r => (k r).withCoins coins
  | .sample n k, coins =>
      (k ⟨coins % (n + 1), Nat.mod_lt _ n.succ_pos⟩).withCoins (coins / (n + 1))

/-- `c.withCoins coins` samples nothing. -/
theorem OComp.noCoin_withCoins : ∀ (c : OComp S α) (coins : ℕ), (c.withCoins coins).NoCoin
  | .pure _, _ => trivial
  | .query _ _ k, coins => fun r => OComp.noCoin_withCoins (k r) coins
  | .sample _ k, _ => OComp.noCoin_withCoins (k _) _

/-- `c.withCoins coins` makes no more queries than c. -/
theorem OComp.QueryBound.withCoins : ∀ (c : OComp S α) (t coins : ℕ), c.QueryBound t →
    (c.withCoins coins).QueryBound t
  | .pure _, _, _, _ => trivial
  | .query _ _ _, 0, _, h => h.elim
  | .query _ _ k, t + 1, coins, h => fun r => OComp.QueryBound.withCoins (k r) t coins (h r)
  | .sample _ k, t, _, h => OComp.QueryBound.withCoins (k _) t _ (h _)

/-- After a first part that samples nothing, the number goes to the second part. -/
theorem OComp.withCoins_bind_of_noCoin (g : α → OComp S β) : ∀ (c : OComp S α) (coins : ℕ),
    c.NoCoin → (c.bind g).withCoins coins = c.bind fun a => (g a).withCoins coins
  | .pure _, _, _ => rfl
  | .query o q k, coins, h => congrArg (OComp.query o q)
      (funext fun r => OComp.withCoins_bind_of_noCoin g (k r) coins (h r))
  | .sample _ _, _, h => h.elim

/-- A function applied to the result can be applied before or after the number is given. -/
theorem OComp.withCoins_bind_pure (h : α → β) : ∀ (c : OComp S α) (coins : ℕ),
    (c.bind fun a => .pure (h a)).withCoins coins = (c.withCoins coins).bind fun a => .pure (h a)
  | .pure _, _ => rfl
  | .query o q k, coins => congrArg (OComp.query o q)
      (funext fun r => OComp.withCoins_bind_pure h (k r) coins)
  | .sample _ k, _ => OComp.withCoins_bind_pure h (k _) _

/-- The step to one oracle (`OComp.overOne`) can be taken before or after the number is given. -/
theorem withCoins_overOne (m : OracleCoding S lam) : ∀ (c : OComp S α) (coins : ℕ),
    (c.overOne m).withCoins coins = (c.withCoins coins).overOne m
  | .pure _, _ => rfl
  | .sample _ k, _ => withCoins_overOne m (k _) _
  | .query o q k, coins => by
      show ((askAll lam (m.blocks o) (m.code o q)).bind fun bs =>
          (k ((m.rng o).symm bs)).overOne m).withCoins coins
        = (askAll lam (m.blocks o) (m.code o q)).bind fun bs =>
          ((k ((m.rng o).symm bs)).withCoins coins).overOne m
      rw [OComp.withCoins_bind_of_noCoin _ _ _ (noCoin_askAll _ _)]
      exact congrArg _ (funext fun bs => withCoins_overOne m (k _) coins)

/-- The step to the trees of ZKCP/Defs.lean (`ofRom`) can be taken before or after the number is
given. -/
theorem withCoins_ofRom : ∀ (c : OComp (rom lam) α) (coins : ℕ),
    (ofRom c).withCoins coins = ofRom (c.withCoins coins)
  | .pure _, _ => rfl
  | .query _ q k, coins => congrArg (ZKCP.OComp.query q)
      (funext fun r => withCoins_ofRom (k r) coins)
  | .sample _ k, _ => withCoins_ofRom (k _) _

end Rom

namespace ZKCP

open Rom (OSpec OracleCoding ofRom schemeOverOneHashFunction withCoins_ofRom withCoins_overOne)

variable {S : OSpec} {lam : ℕ} {I X W IVK ISK Pf : Type}

/-- The scheme G over a family of oracles with its committer run at the given number: the committer
samples nothing. The prover and the verifier are G's. -/
def Gen.Arg.atCoins (G : Gen.Arg S I X W IVK ISK Pf) (coins : ℕ) : Gen.Arg S I X W IVK ISK Pf where
  C := fun i => (G.C i).withCoins coins
  P := G.P
  V := G.V

/-- Run at a number and then brought to one oracle and to the syntax of ZKCP/Defs.lean, or brought
there and then run at the number: the same scheme. -/
theorem oneOf_overOneArg_atCoins (m : OracleCoding S lam) (G : Gen.Arg S I X W IVK ISK Pf) (coins : ℕ) :
    SpecialAny.oneOf (schemeOverOneHashFunction m (G.atCoins coins))
      = (SpecialAny.oneOf (schemeOverOneHashFunction m G)).atCoins coins :=
  congrArg
    (fun C => Arg.mk C (SpecialAny.oneOf (schemeOverOneHashFunction m G)).P (SpecialAny.oneOf (schemeOverOneHashFunction m G)).V)
    (funext fun i => by rw [withCoins_ofRom, withCoins_overOne] :
      (fun i => ofRom (((G.C i).withCoins coins).overOne m))
        = fun i => (ofRom ((G.C i).overOne m)).withCoins coins)

end ZKCP

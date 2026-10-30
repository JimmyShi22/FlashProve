-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/CoinsFirst.lean: a randomized algorithm is "sample one number, then compute".

An algorithm of ZKCP/Defs.lean (`OComp`) may sample at any step. Here all its random choices are
read off one number, which is sampled before the first step.
  `withCoins`            the algorithm at a given number; it samples nothing
                         (`drawsNoCoin_withCoins`)
  `resultWithCoins`      its result under a given hash function (`run_withCoins`)
  `CoinsSuffice`         a number sampled uniformly below `range` holds enough random choices
  `CoinsSuffice.run_eq`  then, for `range` above 0, under every hash function, the algorithm's
                         output distribution is that of "sample a number below `range`, then
                         compute"
  `coinRange`            a range that is enough for one algorithm (`coinsSuffice_coinRange`)
  `coinBound`            one bound for finitely many algorithms (`coinsSuffice_coinBound`)
The queries stay the same, in the same order (`withTrace_withCoins`, `QueryBound.withCoins`).
For infinitely many algorithms there need not be one range: no range above 0 is enough for "sample
from 0, …, i" for every i (no theorem here says so).
Words: a hash function is an `Oracle`, the query log is the `Trace` that `withTrace` returns,
"samples nothing" is `DrawsNoCoin`.
Limit: the number holds every random choice of a run, so its range is far larger than that of a seed
that a program would keep. Nothing here is about a program that expands a seed.
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import ZKCP.ManyOfOne
import Prob.LawKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace ZKCP
namespace OComp

variable {lam : ℕ} {α β : Type}

/-! ## 1. Definitions -/

/-- The algorithm with its random choices read off the number `coins`, and none sampled. Where the
algorithm samples from 0, …, n, this one takes the remainder of `coins` by n + 1 as the sample and
continues with the quotient as the number. -/
def withCoins : OComp lam α → ℕ → OComp lam α
  | pure a, _ => .pure a
  | query q k, coins => .query q fun r => (k r).withCoins coins
  | sample n k, coins =>
      (k ⟨coins % (n + 1), Nat.mod_lt _ n.succ_pos⟩).withCoins (coins / (n + 1))

/-- The result of `withCoins` under the hash function f. -/
def resultWithCoins (f : Oracle lam) : OComp lam α → ℕ → α
  | pure a, _ => a
  | query q k, coins => (k (f q)).resultWithCoins f coins
  | sample n k, coins =>
      (k ⟨coins % (n + 1), Nat.mod_lt _ n.succ_pos⟩).resultWithCoins f (coins / (n + 1))

/-- A number sampled uniformly from 0, …, range - 1 holds enough random choices for the algorithm:
wherever it samples from 0, …, n, the range that is left is a multiple of n + 1, and the quotient is
the range that is left afterwards. Range 0 meets this for every algorithm (no theorem here says so)
and means nothing: `CoinsSuffice.run_eq` and all that uses it take a range above 0. -/
def CoinsSuffice : OComp lam α → ℕ → Prop
  | pure _, _ => True
  | query _ k, range => ∀ r, (k r).CoinsSuffice range
  | sample n k, range => (n + 1) ∣ range ∧ ∀ r, (k r).CoinsSuffice (range / (n + 1))

/-- A range that is enough for the algorithm: 1 at a result; at a query the least common multiple of
the continuations' ranges; at a sample from 0, …, n that multiple times n + 1. If the product of
the n + 1 is the same along all paths, it is that product (no theorem here says so). -/
def coinRange : OComp lam α → ℕ
  | pure _ => 1
  | query _ k => Finset.univ.lcm fun r => (k r).coinRange
  | sample n k => (n + 1) * Finset.univ.lcm fun r => (k r).coinRange

end OComp

/-- The largest number sampled, for finitely many algorithms at once: a number sampled from 0, …,
`coinBound C` holds enough random choices for each `C i`. It is the least common multiple of their
ranges, minus 1. -/
def coinBound {lam : ℕ} {α ι : Type} [Finite ι] (C : ι → OComp lam α) : ℕ :=
  letI := Fintype.ofFinite ι
  (Finset.univ.lcm fun i => (C i).coinRange) - 1

namespace OComp

variable {lam : ℕ} {α β : Type}

/-! ## 2. At a given number the algorithm samples nothing and asks the same queries -/

/-- `c.withCoins coins` samples nothing. -/
theorem drawsNoCoin_withCoins : ∀ (c : OComp lam α) (coins : ℕ), (c.withCoins coins).DrawsNoCoin
  | pure _, _ => trivial
  | query _ k, coins => fun r => drawsNoCoin_withCoins (k r) coins
  | sample _ k, _ => drawsNoCoin_withCoins (k _) _

/-- Under a given hash function `c.withCoins coins` has one result. -/
theorem run_withCoins (f : Oracle lam) : ∀ (c : OComp lam α) (coins : ℕ),
    (c.withCoins coins).run f = PMF.pure (c.resultWithCoins f coins)
  | pure _, _ => rfl
  | query q k, coins => run_withCoins f (k (f q)) coins
  | sample _ k, _ => run_withCoins f (k _) _

/-- `c.withCoins coins` makes no more queries than c. -/
theorem QueryBound.withCoins : ∀ (c : OComp lam α) (t coins : ℕ), c.QueryBound t →
    (c.withCoins coins).QueryBound t
  | pure _, _, _, _ => trivial
  | query _ _, 0, _, h => h.elim
  | query _ k, t + 1, coins, h => fun r => QueryBound.withCoins (k r) t coins (h r)
  | sample _ k, t, _, h => QueryBound.withCoins (k _) t _ (h _)

/-- A function applied to the result can be applied before or after the number is given. -/
theorem withCoins_mapO (h : α → β) : ∀ (c : OComp lam α) (coins : ℕ),
    (c.mapO h).withCoins coins = (c.withCoins coins).mapO h
  | pure _, _ => rfl
  | query q k, coins => congrArg (query q) (funext fun r => withCoins_mapO h (k r) coins)
  | sample _ k, _ => withCoins_mapO h (k _) _

/-- The query log of `c.withCoins coins` is the query log of c at that number. -/
theorem withTrace_withCoins : ∀ (c : OComp lam α) (coins : ℕ),
    (c.withCoins coins).withTrace = c.withTrace.withCoins coins
  | pure _, _ => rfl
  | query q k, coins => by
      show query q (fun r => ((k r).withCoins coins).withTrace.mapO
          fun out => (out.1, (q, r) :: out.2))
        = query q fun r =>
          ((k r).withTrace.mapO fun out => (out.1, (q, r) :: out.2)).withCoins coins
      exact congrArg _ (funext fun r => by rw [withCoins_mapO, withTrace_withCoins (k r) coins])
  | sample _ k, _ => withTrace_withCoins (k _) _

/-! ## 3. Which ranges are enough -/

/-- A multiple of a range that is enough is enough. -/
theorem CoinsSuffice.of_dvd : ∀ (c : OComp lam α) (range range' : ℕ), c.CoinsSuffice range →
    range ∣ range' → c.CoinsSuffice range'
  | pure _, _, _, _, _ => trivial
  | query _ k, range, range', h, hd => fun r => CoinsSuffice.of_dvd (k r) range range' (h r) hd
  | sample n k, range, range', h, hd =>
      ⟨Nat.dvd_trans h.1 hd, fun r => CoinsSuffice.of_dvd (k r) _ _ (h.2 r) (by
        obtain ⟨u, rfl⟩ := h.1
        obtain ⟨v, rfl⟩ := hd
        rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ n.succ_pos,
          Nat.mul_div_cancel_left _ n.succ_pos]
        exact Nat.dvd_mul_right u v)⟩

/-- A range that is enough for c is enough for `c.mapO h`. -/
theorem CoinsSuffice.mapO (h : α → β) : ∀ (c : OComp lam α) (range : ℕ), c.CoinsSuffice range →
    (c.mapO h).CoinsSuffice range
  | pure _, _, _ => trivial
  | query _ k, range, hc => fun r => CoinsSuffice.mapO h (k r) range (hc r)
  | sample _ k, _, hc => ⟨hc.1, fun r => CoinsSuffice.mapO h (k r) _ (hc.2 r)⟩

/-- A range that is enough for c is enough for `c.withTrace`. -/
theorem CoinsSuffice.withTrace : ∀ (c : OComp lam α) (range : ℕ), c.CoinsSuffice range →
    c.withTrace.CoinsSuffice range
  | pure _, _, _ => trivial
  | query _ k, range, hc => fun r =>
      CoinsSuffice.mapO _ _ range (CoinsSuffice.withTrace (k r) range (hc r))
  | sample _ k, _, hc => ⟨hc.1, fun r => CoinsSuffice.withTrace (k r) _ (hc.2 r)⟩

/-- The least common multiple of finitely many positive numbers is positive. -/
theorem lcm_univ_pos {ι : Type} [Fintype ι] (g : ι → ℕ) (h : ∀ i, 0 < g i) :
    0 < Finset.univ.lcm g :=
  Nat.pos_of_dvd_of_pos (Finset.lcm_dvd fun _ hi => Finset.dvd_prod_of_mem g hi)
    (Finset.prod_pos fun i _ => h i)

/-- `coinRange` is above 0. -/
theorem coinRange_pos : ∀ c : OComp lam α, 0 < c.coinRange
  | pure _ => Nat.one_pos
  | query _ k => by
      show 0 < Finset.univ.lcm fun r => (k r).coinRange
      exact lcm_univ_pos _ fun r => coinRange_pos (k r)
  | sample n k => by
      show 0 < (n + 1) * Finset.univ.lcm fun r => (k r).coinRange
      exact Nat.mul_pos n.succ_pos (lcm_univ_pos _ fun r => coinRange_pos (k r))

/-- Every algorithm has a range above 0 that is enough (`coinRange_pos`). -/
theorem coinsSuffice_coinRange : ∀ c : OComp lam α, c.CoinsSuffice c.coinRange
  | pure _ => trivial
  | query _ k => fun r => by
      show (k r).CoinsSuffice (Finset.univ.lcm fun r => (k r).coinRange)
      exact CoinsSuffice.of_dvd (k r) _ _ (coinsSuffice_coinRange (k r))
        (Finset.dvd_lcm (f := fun r => (k r).coinRange) (Finset.mem_univ r))
  | sample n k => ⟨Nat.dvd_mul_right _ _, fun r => by
      show (k r).CoinsSuffice ((n + 1) * (Finset.univ.lcm fun r => (k r).coinRange) / (n + 1))
      rw [Nat.mul_div_cancel_left _ n.succ_pos]
      exact CoinsSuffice.of_dvd (k r) _ _ (coinsSuffice_coinRange (k r))
        (Finset.dvd_lcm (f := fun r => (k r).coinRange) (Finset.mem_univ r))⟩

end OComp

/-- Finitely many algorithms have one range that is enough for each. -/
theorem coinsSuffice_coinBound {lam : ℕ} {α ι : Type} [Finite ι] (C : ι → OComp lam α) (i : ι) :
    (C i).CoinsSuffice (coinBound C + 1) := by
  letI := Fintype.ofFinite ι
  have hpos : 0 < Finset.univ.lcm fun i => (C i).coinRange :=
    OComp.lcm_univ_pos _ fun i => (C i).coinRange_pos
  have hb : coinBound C + 1 = Finset.univ.lcm fun i => (C i).coinRange := Nat.sub_add_cancel hpos
  rw [hb]
  exact OComp.CoinsSuffice.of_dvd (C i) _ _ (C i).coinsSuffice_coinRange
    (Finset.dvd_lcm (f := fun i => (C i).coinRange) (Finset.mem_univ i))

namespace OComp

variable {lam : ℕ} {α β : Type}

/-! ## 4. Sample one number, then compute -/

/-- For `rest` above 0, the remainder by n + 1 and the quotient of a uniform number below
`(n + 1) * rest` are uniform and independent. -/
theorem map_uniform_mul {γ : Type} (n rest : ℕ) [Nonempty (Fin rest)]
    [Nonempty (Fin ((n + 1) * rest))] (g : Fin (n + 1) → ℕ → γ) :
    ((PMF.uniformOfFintype (Fin ((n + 1) * rest))).map fun coins =>
        g ⟨coins.val % (n + 1), Nat.mod_lt _ n.succ_pos⟩ (coins.val / (n + 1)))
      = (PMF.uniformOfFintype (Fin (n + 1))).bind fun r =>
          (PMF.uniformOfFintype (Fin rest)).map fun coins => g r coins.val := by
  let e : Fin (n + 1) × Fin rest ≃ Fin ((n + 1) * rest) :=
    (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm rest (n + 1))))
  have hv : ∀ (r : Fin (n + 1)) (s : Fin rest), (e (r, s)).val = r.val + (n + 1) * s.val :=
    fun _ _ => rfl
  have he : (PMF.uniformOfFintype (Fin (n + 1) × Fin rest)).map e
      = PMF.uniformOfFintype (Fin ((n + 1) * rest)) := Prob.map_unif_equiv e
  rw [← he, PMF.map_comp, Prob.map_unif_prod]
  refine congrArg _ (funext fun r =>
    congrArg (fun F => (PMF.uniformOfFintype (Fin rest)).map F) (funext fun s => ?_))
  show g ⟨(e (r, s)).val % (n + 1), Nat.mod_lt _ n.succ_pos⟩ ((e (r, s)).val / (n + 1))
    = g r s.val
  have h1 : (e (r, s)).val % (n + 1) = r.val := by
    rw [hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  have h2 : (e (r, s)).val / (n + 1) = s.val := by
    rw [hv, Nat.add_mul_div_left _ _ n.succ_pos, Nat.div_eq_of_lt r.isLt, Nat.zero_add]
  exact congrArg₂ g (Fin.ext h1) h2

/-- Sample one number, then compute. If `range` is above 0 and is enough for the algorithm, then
under every hash function its output has the distribution of its result at a number sampled
uniformly below `range`. -/
theorem CoinsSuffice.run_eq (f : Oracle lam) (c : OComp lam α) :
    ∀ (range : ℕ) [Nonempty (Fin range)], c.CoinsSuffice range →
      c.run f = (PMF.uniformOfFintype (Fin range)).map fun coins =>
        c.resultWithCoins f coins.val := by
  induction c with
  | pure a =>
      intro range _ _
      exact (PMF.map_const _ a).symm
  | query q k ih =>
      intro range _ h
      exact ih (f q) range (h (f q))
  | sample n k ih =>
      intro range hne h
      have h' : (n + 1) ∣ range ∧ ∀ r, (k r).CoinsSuffice (range / (n + 1)) := h
      obtain ⟨⟨rest, rfl⟩, h2⟩ := h'
      rw [Nat.mul_div_cancel_left _ n.succ_pos] at h2
      have hpos : 0 < rest := by
        rcases Nat.eq_zero_or_pos rest with h0 | h0
        · subst h0
          exact hne.elim fun x => absurd x.isLt (by simp)
        · exact h0
      haveI : Nonempty (Fin rest) := ⟨⟨0, hpos⟩⟩
      refine Eq.trans ?_
        (map_uniform_mul n rest fun r coins => (k r).resultWithCoins f coins).symm
      show ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).run f) = _
      exact congrArg _ (funext fun r => ih r rest (h2 r))

/-- `CoinsSuffice.run_eq` as an equation between the output distributions of two algorithms. If
`bound + 1` is enough for c, then under every hash function "sample a number from 0, …, bound, then
run c at that number" has the output distribution of c. -/
theorem CoinsSuffice.run_sample (f : Oracle lam) (c : OComp lam α) (bound : ℕ)
    (h : c.CoinsSuffice (bound + 1)) :
    (sample bound fun coins => c.withCoins coins.val).run f = c.run f := by
  rw [CoinsSuffice.run_eq f c (bound + 1) h]
  show ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun coins => (c.withCoins coins.val).run f)
    = (PMF.uniformOfFintype (Fin (bound + 1))).bind fun coins =>
        PMF.pure (c.resultWithCoins f coins.val)
  exact congrArg _ (funext fun coins => run_withCoins f c coins.val)

end OComp
end ZKCP

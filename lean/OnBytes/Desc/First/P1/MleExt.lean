--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/MleExt.lean: THE ORDER OF THE BITS: THE ALGEBRA. Tables that are indexed by
ROUNDS against the library's extension, which is indexed by COORDINATES. Over a field; no text of a
verifier. Definitions, statements and proofs.

The matter. `mle n A rs` and `tot ws F` (OnBytes/Desc/First/P1/SumMle.lean) take tables on lists of
bits whose FIRST bit belongs to the variable that the FIRST ROUND sums. The library's extension of a
vector v of length 2 ^ g at a point pt is `Blocks.ext g v pt`, the sum over X below 2 ^ g of
`Blocks.eqN g 0 pt X * v X` (Blocks/Ext.lean, Blocks/Basic.lean); there coordinate k of the point
goes with bit g - 1 - k of the index X (`eqN_bits`). A sumcheck may bind its variables in any order:
let round j run in the variable order[j], and let that variable's coordinate of a point be number mu
- 1 - order[j]. Then round j goes with BIT order[j] of the index.

`idxOf order b`: the index whose bit order[j] is b[j].
`tot_eqN`: THE CORE. For an order that is a permutation of 0, .., mu - 1, any point pt and any
vector f: the sum of the table b ↦ f (idxOf order b), under the two-point weights (1 - pt (mu - 1 -
v), pt (mu - 1 - v)) in the order of the rounds, is the sum over X below 2 ^ mu of eqN mu 0 pt X * f
X.
`mle_ext_at`: the extension of the table b ↦ v (idxOf order b), at the point's coordinates taken in
the order of the rounds, is `Blocks.ext mu v pt`.

How. Both sides are brought to a sum over the subsets t of a set s of variables (`subSum`): the
product over s of w u or 1 - w u, as u lies in t or not, times f at the sum of 2 ^ u over t. One
variable more splits that sum in two (`subSum_insert`). By it the sum under the rounds' weights is
`subSum` at the set of the order's variables, WHATEVER THE ORDER (`tot_subSum`); and `subSum` at 0,
.., mu - 1 is the sum over the numbers below 2 ^ mu, by their bits (`subSum_range`).

Limits. That a given protocol's order is a permutation is its caller's to show. Nothing is said of a
run, of soundness or of probabilities.
-/
import OnBytes.Desc.First.P1.SumMle
import Blocks.Ext
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1

variable {K : Type} [Field K]

/-! ### The index of a list of bits -/

/-- The index whose bit order[j] is b[j]. -/
def idxOf : List ℕ → List Bool → ℕ
  | v :: order, x :: b => (if x then 2 ^ v else 0) + idxOf order b
  | _, _ => 0

theorem idxOf_cons (v : ℕ) (order : List ℕ) (x : Bool) (b : List Bool) :
    idxOf (v :: order) (x :: b) = (if x then 2 ^ v else 0) + idxOf order b := rfl

/-! ### Sums over the subsets of a set of variables -/

/-- The sum over the subsets t of s: the product over s of w u or 1 - w u, as u lies in t or not,
times f at the number whose bits are t. -/
def subSum (w : ℕ → K) (s : Finset ℕ) (f : ℕ → K) : K :=
  ∑ t ∈ s.powerset, (∏ u ∈ s, (if u ∈ t then w u else 1 - w u)) * f (∑ u ∈ t, 2 ^ u)

/-- One variable more. -/
theorem subSum_insert (w : ℕ → K) {s : Finset ℕ} {v : ℕ} (hv : v ∉ s) (f : ℕ → K) :
    subSum w (insert v s) f =
      (1 - w v) * subSum w s f + w v * subSum w s (fun X => f (2 ^ v + X)) := by
  unfold subSum
  rw [Finset.sum_powerset_insert hv, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    have hvt : v ∉ t := fun h => hv (Finset.mem_powerset.mp ht h)
    rw [Finset.prod_insert hv, if_neg hvt]
    ring
  · refine Finset.sum_congr rfl fun t ht => ?_
    have hvt : v ∉ t := fun h => hv (Finset.mem_powerset.mp ht h)
    have hq : ∏ u ∈ s, (if u ∈ insert v t then w u else 1 - w u) =
        ∏ u ∈ s, (if u ∈ t then w u else 1 - w u) := by
      refine Finset.prod_congr rfl fun u hu => ?_
      have huv : u ≠ v := fun h => hv (h ▸ hu)
      simp only [Finset.mem_insert, huv, false_or]
    rw [Finset.prod_insert hv, if_pos (Finset.mem_insert_self v t), Finset.sum_insert hvt, hq]
    ring

/-- The sum under the rounds' weights, whatever the order of the variables. -/
theorem tot_subSum (w : ℕ → K) : ∀ (vs : List ℕ), vs.Nodup → ∀ f : ℕ → K,
    tot (vs.map fun v => (1 - w v, w v)) (fun b => f (idxOf vs b)) = subSum w vs.toFinset f
  | [], _, f => by simp [tot, idxOf, subSum]
  | v :: vs, hnd, f => by
    have hv : v ∉ vs := (List.nodup_cons.mp hnd).1
    have hn : vs.Nodup := (List.nodup_cons.mp hnd).2
    have hv' : v ∉ vs.toFinset := by simpa using hv
    rw [List.toFinset_cons, subSum_insert w hv', ← tot_subSum w vs hn f,
      ← tot_subSum w vs hn (fun X => f (2 ^ v + X))]
    simp [tot, idxOf_cons]

/-- At the variables 0, .., mu - 1 the subsets are the numbers below 2 ^ mu, by their bits. -/
theorem subSum_range (w : ℕ → K) : ∀ (mu : ℕ) (f : ℕ → K),
    subSum w (Finset.range mu) f =
      ∑ X ∈ Finset.range (2 ^ mu),
        (∏ u ∈ Finset.range mu, (if X.testBit u then w u else 1 - w u)) * f X
  | 0, f => by simp [subSum]
  | mu + 1, f => by
    have h2 : 2 ^ (mu + 1) = 2 ^ mu + 2 ^ mu := by rw [pow_succ, Nat.mul_two]
    have hL : subSum w (Finset.range (mu + 1)) f =
        (1 - w mu) * subSum w (Finset.range mu) f +
          w mu * subSum w (Finset.range mu) (fun X => f (2 ^ mu + X)) := by
      rw [Finset.range_add_one]
      exact subSum_insert w (by simp) f
    rw [hL, subSum_range w mu f, subSum_range w mu (fun X => f (2 ^ mu + X)), h2,
      Finset.sum_range_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun X hX => ?_
      have hX' : X < 2 ^ mu := Finset.mem_range.mp hX
      rw [Finset.prod_range_succ, Nat.testBit_lt_two_pow hX']
      simp only [Bool.false_eq_true, if_false]
      ring
    · refine Finset.sum_congr rfl fun X hX => ?_
      have hX' : X < 2 ^ mu := Finset.mem_range.mp hX
      have hq : ∏ u ∈ Finset.range mu, (if (2 ^ mu + X).testBit u then w u else 1 - w u) =
          ∏ u ∈ Finset.range mu, (if X.testBit u then w u else 1 - w u) := by
        refine Finset.prod_congr rfl fun u hu => ?_
        rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hu) X]
      rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hX', hq]
      simp only [Bool.not_false, if_true]
      ring

/-! ### The library's equality polynomial, by the bits from below -/

/-- Coordinate k of the point goes with bit mu - 1 - k of the index. -/
theorem eqN_bits (mu : ℕ) (pt : ℕ → K) (X : ℕ) :
    Blocks.eqN mu 0 pt X =
      ∏ u ∈ Finset.range mu, (if X.testBit u then pt (mu - 1 - u) else 1 - pt (mu - 1 - u)) := by
  unfold Blocks.eqN
  refine (Finset.prod_range_reflect _ mu).symm.trans (Finset.prod_congr rfl fun u hu => ?_)
  have hu' : u < mu := Finset.mem_range.mp hu
  have e : mu - 1 - (mu - 1 - u) = u := by omega
  show (if X.testBit (mu - 1 - (mu - 1 - u)) then pt (0 + (mu - 1 - u))
    else 1 - pt (0 + (mu - 1 - u))) = _
  rw [e, Nat.zero_add]

/-- **THE CORE.** -/
theorem tot_eqN (mu : ℕ) {order : List ℕ} (hp : order.Perm (List.range mu)) (pt f : ℕ → K) :
    tot (order.map fun v => (1 - pt (mu - 1 - v), pt (mu - 1 - v))) (fun b => f (idxOf order b)) =
      ∑ X ∈ Finset.range (2 ^ mu), Blocks.eqN mu 0 pt X * f X := by
  have hnd : order.Nodup := (List.Perm.nodup_iff hp).mpr List.nodup_range
  rw [tot_subSum (fun u => pt (mu - 1 - u)) order hnd f, List.toFinset_eq_of_perm _ _ hp,
    List.toFinset_range, subSum_range]
  exact Finset.sum_congr rfl fun X _ => by rw [eqN_bits]

/-! ### An extension as a sum under two-point weights -/

theorem mle_eq_tot : ∀ (rs : List K) (A : List Bool → K),
    mle rs.length A rs = tot (rs.map fun r => (1 - r, r)) A
  | [], _ => rfl
  | r :: rs, A => by
    simp only [List.length_cons, mle, List.map_cons, tot]
    rw [mle_eq_tot rs, mle_eq_tot rs]

/-- **The extension at a point's coordinates, taken in the order of the rounds.** -/
theorem mle_ext_at (mu : ℕ) {order : List ℕ} (hp : order.Perm (List.range mu)) (pt v : ℕ → K) :
    mle mu (fun b => v (idxOf order b)) (order.map fun u => pt (mu - 1 - u)) =
      Blocks.ext mu v pt := by
  have hlen : order.length = mu := by rw [hp.length_eq, List.length_range]
  have h2 := mle_eq_tot (order.map fun u => pt (mu - 1 - u)) (fun b => v (idxOf order b))
  rw [List.length_map, hlen] at h2
  rw [h2, List.map_map]
  exact tot_eqN mu hp pt v

end OnBytes.Desc.First.P1

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/HandedIn.lean: WHAT THE TWO
LEDGERS HAND TO THE LOOKUPS LIES INSIDE THE TWO MASK TABLES, FROM ONE PUBLIC INEQUALITY A LEDGER: so
the promise's clause "the statement has the tables for each of the n lookups" (Fits in PromL,
PromKeyD.lean) follows from plain facts on the statement and two inequalities on public numbers.

The closed form of what a ledger hands out (takes_eq, Johnson/Top/H/Hands/HandsCore.lean: n takings
from a ledger with R real rows among 2 ^ k give the real numbers of the next n ranks) is carried
along the lookups: lookup i is handed the real numbers of the ranks from r + (what the lookups
before it take) on, r the rank of the ledger's count in front of the first link.

Main names:
  sumTo f i: f 0 + .. + f (i - 1). sumTo_mono.
  behind_rank: the ledger behind i lookups: its rows, its logarithm, its count's rank.
  handed_eq: THE CLOSED FORM of the entries handed to lookup i. handed_lt: they lie below 2 ^ k * c
    where all n lookups' ranks lie below R * c.
  fits_handed: Fits for each of the n lookups.
  promL_fresh: THE PROMISE IN FRONT OF THE FIRST LINK, AT TWO FRESH LEDGERS: PromL 0 from plain
    facts on the record and one inequality a ledger: what the n lookups take together of a
    message's mask entries is at most (its mask rows) * 2 ^ (the logarithm of a mask row's entries).

Limits. The two inequalities, the ledgers' rows and logarithms, TablesFit, the index-mask message's
being there and the two mask tables' sizes are premises. That the record behind the two sendings has
promL_fresh's facts is not shown here.

-/
import Johnson.RunOne.Law.PromKeyD
import Johnson.RunOne.Law.FitsKeyD
import Johnson.Top.H.Hands.HandsCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.HandedIn
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.G4 (takesOf realBelow)
open Fo.Hands (realAt takes_eq realAt_lt fresh_bounds)
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.FitsKeyD
open Johnson.RunOne.Law.PromKeyD

/-- f 0 + .. + f (i - 1). -/
def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => sumTo f i + f i

theorem sumTo_mono (f : ℕ → ℕ) {i : ℕ} : ∀ {n : ℕ}, i ≤ n → sumTo f i ≤ sumTo f n
  | 0, h => by
    obtain rfl : i = 0 := Nat.le_zero.1 h
    exact Nat.le_refl _
  | n + 1, h => by
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact Nat.le_refl _
    · exact Nat.le_trans (sumTo_mono f (Nat.le_of_lt_succ h')) (Nat.le_add_right _ _)

variable {R k : ℕ} (h1 : 0 < R) (h2 : R ≤ 2 ^ k) (cnt : ℕ → ℕ) (l : Ledger) (e1 : l.rows = R)
  (e2 : l.logRows = k)

include h1 h2 e1 e2

/-- The ledger behind i lookups: its rows, its logarithm, the rank of its count. -/
theorem behind_rank : ∀ i : ℕ, (ledBehind cnt l i).rows = R ∧ (ledBehind cnt l i).logRows = k ∧
    realBelow R k (ledBehind cnt l i).next = realBelow R k l.next + sumTo cnt i
  | 0 => ⟨e1, e2, rfl⟩
  | i + 1 => by
    obtain ⟨a, b, c⟩ := behind_rank i
    obtain ⟨-, a', b', c'⟩ := takes_eq h1 h2 (cnt i) (ledBehind cnt l i) a b
    refine ⟨a', b', ?_⟩
    show realBelow R k (takesOf (ledBehind cnt l i) (cnt i)).2.next =
      realBelow R k l.next + (sumTo cnt i + cnt i)
    rw [c', c, Nat.add_assoc]

/-- **The closed form of the entries handed to lookup i.** -/
theorem handed_eq (i : ℕ) : handed cnt l i =
    (List.range (cnt i)).map fun t => realAt R k (realBelow R k l.next + sumTo cnt i + t) := by
  obtain ⟨a, b, c⟩ := behind_rank h1 h2 cnt l e1 e2 i
  unfold handed
  rw [(takes_eq h1 h2 (cnt i) (ledBehind cnt l i) a b).1, c]

/-- **They lie inside**, where all n lookups' ranks lie below R * c. -/
theorem handed_lt {c n i : ℕ} (hn : realBelow R k l.next + sumTo cnt n ≤ R * c) (hi : i < n) :
    ∀ j ∈ handed cnt l i, j < 2 ^ k * c := by
  intro j hj
  rw [handed_eq h1 h2 cnt l e1 e2 i] at hj
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hj
  have ht' := List.mem_range.1 ht
  have hm : sumTo cnt (i + 1) ≤ sumTo cnt n := sumTo_mono cnt hi
  have es : sumTo cnt (i + 1) = sumTo cnt i + cnt i := rfl
  exact realAt_lt h1 h2 (by omega)

omit h1 h2 e1 e2

/-- **Fits for each of the n lookups, from plain facts and one public inequality a ledger.** -/
theorem fits_handed {one : OneTime} {id : ℕ} {m : Wf.Matrix} {L : ℕ → WfLookup} {idxN n : ℕ}
    {lo lk : Ledger} {S : Statement} {RO kO cO RK kK cK : ℕ}
    (hT : TablesFit S one.ranges one.codes) (hi : idxN < S.oracles.size)
    (o1 : 0 < RO) (o2 : RO ≤ 2 ^ kO) (o3 : lo.rows = RO) (o4 : lo.logRows = kO)
    (k1 : 0 < RK) (k2 : RK ≤ 2 ^ kK) (k3 : lk.rows = RK) (k4 : lk.logRows = kK)
    (tO : 2 ^ kO * cO ≤ Means.tableSize S one.ranges.messageId .mask)
    (tK : 2 ^ kK * cK ≤ Means.tableSize S idxN .mask)
    (hO : realBelow RO kO lo.next + sumTo (cntO id m L) n ≤ RO * cO)
    (hK : realBelow RK kK lk.next + sumTo (cntK id m L) n ≤ RK * cK) :
    ∀ q < n, Fits one id m (L q) (handed (cntO id m L) lo q) (handed (cntK id m L) lk q) idxN S :=
  fun q hq => fits_of_lists hT hi
    (fun j hj => Nat.lt_of_lt_of_le (handed_lt o1 o2 _ lo o3 o4 hO hq j hj) tO)
    (fun j hj => Nat.lt_of_lt_of_le (handed_lt k1 k2 _ lk k3 k4 hK hq j hj) tK)

/-- **The promise in front of the first link, at two fresh ledgers.** rO, rK: the two messages' mask
rows. eO, eK: the logarithms of a mask row's entries. -/
theorem promL_fresh {one : OneTime} {id : ℕ} {m : Wf.Matrix} {L : ℕ → WfLookup} {idxN n : ℕ}
    {lo lk : Ledger} {Ex : FirstState → Prop} {s : FirstState} {rO eO rK eK : ℕ} (h1 : s.idx = idxN)
    (h2 : ledAt s.d.st one.ranges.messageId = some lo) (h3 : ledAt s.d.st idxN = some lk)
    (hT : TablesFit s.d.st one.ranges one.codes) (hi : idxN < s.d.st.oracles.size)
    (pO : 0 < rO) (o0 : lo.next = 0) (o1 : lo.rows = max rO 1) (o2 : lo.logRows = ceilLog2 rO)
    (pK : 0 < rK) (k0 : lk.next = 0) (k1 : lk.rows = max rK 1) (k2 : lk.logRows = ceilLog2 rK)
    (tO : Means.tableSize s.d.st one.ranges.messageId .mask = 2 ^ (eO + ceilLog2 rO))
    (tK : Means.tableSize s.d.st idxN .mask = 2 ^ (eK + ceilLog2 rK))
    (hO : sumTo (cntO id m L) n ≤ rO * 2 ^ eO) (hK : sumTo (cntK id m L) n ≤ rK * 2 ^ eK)
    (hE : Ex s) : PromL one id m L idxN n lo lk Ex 0 s := by
  obtain ⟨a1, a2, a3⟩ := fresh_bounds pO
  obtain ⟨b1, b2, b3⟩ := fresh_bounds pK
  refine promL_zero h1 h2 h3 (fits_handed (cO := 2 ^ eO) (cK := 2 ^ eK) hT hi a2 a3 o1 o2 b2 b3 k1
    k2 ?_ ?_ ?_ ?_) hE
  · rw [tO, Nat.pow_add, Nat.mul_comm]
  · rw [tK, Nat.pow_add, Nat.mul_comm]
  · rw [o0, a1]
    show 0 + _ ≤ _
    rw [Nat.zero_add]
    exact hO
  · rw [k0, b1]
    show 0 + _ ≤ _
    rw [Nat.zero_add]
    exact hK

end Johnson.RunOne.Law.HandedIn

#print axioms Johnson.RunOne.Law.HandedIn.behind_rank
#print axioms Johnson.RunOne.Law.HandedIn.handed_eq
#print axioms Johnson.RunOne.Law.HandedIn.handed_lt
#print axioms Johnson.RunOne.Law.HandedIn.fits_handed
#print axioms Johnson.RunOne.Law.HandedIn.promL_fresh

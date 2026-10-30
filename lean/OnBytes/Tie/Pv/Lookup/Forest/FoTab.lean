-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTab.lean.
The lookup of a sub-proof: the joined table at the leaves' point.

The row of the leaves' sumcheck holds the extension of (lambda - 1 - the joined table's row) at the
rows' coordinates. The flat form of the lookup's verifier (TwV.rowEnd) sums it over all 2^d rows.
The byte-level verifier (OnBytes/Model/Look.lean) computes a closed form: each call's table at the
last k coordinates of the row's point, then the calls joined under the weights of the call's
number.

States:
  exL, tableK, joinedK, tTK, leavesAK: plain forms, in a commutative ring and on lists, fold for
    fold, of Array.extract and of the byte-level verifier's Forest.tableAt, Forest.joinedTableAt
    and the values tT, leavesA. No statement of this file compares them with these routines: that
    is table_val, joined_val, tT_val, leavesA_val (OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean).
  tableK_eq: a call's table at a point is the weighted sum of its rows, for the range table and for
    a written table.
  tab_ext: the sum over all rows is leavesAK at the reversed point. The point is given by coordinate
    in three parts (plane | the call's number | the row), each the lowest bit first.
Premises: on public numbers: 1 ≤ NC, as many calls as NC, k_c ≤ kT for each call, kT < 64; on the
point: its three parts have 5, cK and kT coordinates (in tableK_eq: k coordinates, and k < 64).

-/
import Cb.Pv.Lookup.Forest.FoEq
import OnBytes.Tie.Pv.Lookup.Forest.FoV
import Mathlib.Data.List.GetD

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes.Model

section
variable {K : Type} [CommRing K]

/-- Array.extract's twin -/
def exL (l : List K) (a b : ℕ) : List K := (l.drop a).take (b - a)

/-- Forest.tableAt's twin -/
def tableK (c : Call) (u : List K) : K :=
  match c.tau with
  | none => (List.range c.k).foldl (fun s i => s + ((2 ^ (c.k - 1 - i) : ℕ) : K) * u.getD i 0) 0
  | some rows =>
    (List.range (eqTabK u).length).foldl
      (fun s t => s + (((rows.getD t 0).toNat : ℕ) : K) * (eqTabK u).getD t 0) 0

/-- Forest.joinedTableAt's twin -/
def joinedK (h : Sh) (θ : K) (tT zc : List K) : K :=
  (List.range (2 ^ h.cK)).foldl
    (fun s c => s + (eqTabK zc).getD c 0 *
      (tT.getD (min c (h.NC - 1)) 0 + ((min c (h.NC - 1) : ℕ) : K) * θ)) 0

def tTK (h : Sh) (zb0 : List K) : List K :=
  h.calls.toList.map fun k => tableK k (exL zb0 (h.kT - k.k) h.kT)

def leavesAK (h : Sh) (θ α : K) (zb0 : List K) : K :=
  α - 1 - joinedK h θ (tTK h zb0) (exL zb0 h.kT (h.kT + h.cK))

theorem foldl_sum (f : ℕ → K) : ∀ n, (List.range n).foldl (fun s i => s + f i) 0 = ∑ i ∈ range n, f
    i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_sum f n, Finset.sum_range_succ]
    rfl

theorem bin_rev : ∀ y : List K,
    ∑ i ∈ range y.length, ((2 ^ (y.length - 1 - i) : ℕ) : K) * y.reverse.getD i 0 = binK y
  | [] => rfl
  | x :: xs => by
    show ∑ i ∈ range (xs.length + 1), ((2 ^ (xs.length + 1 - 1 - i) : ℕ) : K) * (x ::
        xs).reverse.getD i 0 =
      x + 2 * binK xs
    rw [Finset.sum_range_succ, ← bin_rev xs, Finset.mul_sum, List.reverse_cons]
    have hl : xs.reverse.length = xs.length := List.length_reverse
    have e0 : (xs.reverse ++ [x]).getD xs.length 0 = x := by
      rw [List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self]
      rfl
    rw [e0, Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < xs.length := Finset.mem_range.mp hi
    rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi')]
    have e1 : xs.length - i = (xs.length - 1 - i) + 1 := by omega
    rw [e1, pow_succ']
    push_cast
    ring

theorem tableK_eq (c : Call) (y : List K) (hy : y.length = c.k) (hk : c.k < 64) :
    tableK c y.reverse = ∑ s ∈ range (2 ^ c.k), eqN y s * (((c.tauAt s).toNat : ℕ) : K) := by
  unfold tableK Call.tauAt
  cases c.tau with
  | none =>
    show (List.range c.k).foldl (fun s i => s + ((2 ^ (c.k - 1 - i) : ℕ) : K) * y.reverse.getD i 0)
        0 =
      ∑ s ∈ range (2 ^ c.k), eqN y s * (((s.toUInt64).toNat : ℕ) : K)
    rw [foldl_sum, ← hy, bin_rev, ← eqN_bin]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s < 2 ^ 64 :=
      lt_trans (Finset.mem_range.mp hs) (Nat.pow_lt_pow_right (by norm_num) (by rw [hy]; exact hk))
    have e : (s.toUInt64).toNat = s := by
      show (UInt64.ofNat s).toNat = s
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt hs'
    rw [e]
  | some rows =>
    show (List.range (eqTabK y.reverse).length).foldl
        (fun s t => s + (((rows.getD t 0).toNat : ℕ) : K) * (eqTabK y.reverse).getD t 0) 0 =
      ∑ s ∈ range (2 ^ c.k), eqN y s * (((rows.getD s 0).toNat : ℕ) : K)
    rw [foldl_sum, eqTabK_len, List.length_reverse, hy]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [eqTabK_get, List.length_reverse, hy, if_pos (Finset.mem_range.mp hs), List.reverse_reverse,
        mul_comm]

omit [CommRing K] in
theorem exL_left (A B : List K) (a : ℕ) (ha : a ≤ A.length) : exL (A ++ B) a A.length = A.drop a :=
    by
  unfold exL
  rw [List.drop_append_of_le_length ha]
  have : A.length - a = (A.drop a).length := by rw [List.length_drop]
  rw [this, List.take_left']
  rfl

omit [CommRing K] in
theorem exL_mid (A B C : List K) : exL (A ++ (B ++ C)) A.length (A.length + B.length) = B := by
  unfold exL
  rw [List.drop_left', Nat.add_sub_cancel_left, List.take_left']
  · rfl
  · rfl

/-- The sum over all rows is leavesAK at the reversed point. -/
theorem tab_ext (h : Sh) (h1 : 1 ≤ h.NC) (hs : h.calls.size = h.NC) (hk : ∀ c < h.NC, kOf h c ≤
    h.kT)
    (h64 : h.kT < 64) (θ lam : K) (xp xc xt : List K) (hp : xp.length = FoNums.w)
    (hc : xc.length = h.cK) (ht : xt.length = h.kT) :
    ((List.range (2 ^ h.d)).map fun r =>
        eqN ((xp ++ (xc ++ xt)).drop FoNums.w) r * (lam - 1 - tabF h θ r)).sum =
      leavesAK h θ lam (xp ++ (xc ++ xt)).reverse := by
  have hz : (xp ++ (xc ++ xt)).reverse = xt.reverse ++ (xc.reverse ++ xp.reverse) := by
    rw [List.reverse_append, List.reverse_append, List.append_assoc]
  have hzc : exL (xt.reverse ++ (xc.reverse ++ xp.reverse)) h.kT (h.kT + h.cK) = xc.reverse := by
    have := exL_mid xt.reverse xc.reverse xp.reverse
    rwa [List.length_reverse, List.length_reverse, ht, hc] at this
  -- a call's table at its coordinates
  have hT : ∀ c < h.NC, (tTK h (xt.reverse ++ (xc.reverse ++ xp.reverse))).getD c 0 =
      ∑ s ∈ range (2 ^ kOf h c), eqN (xt.take (kOf h c)) s * ((tauN h c s : ℕ) : K) := by
    intro c hcN
    have hcs : c < h.calls.size := by rw [hs]; exact hcN
    have hget : h.calls[c]? = some h.calls[c] := Array.getElem?_eq_getElem hcs
    have hkc : kOf h c = h.calls[c].k := by unfold kOf; rw [hget]; rfl
    have htau : ∀ s, tauN h c s = (h.calls[c].tauAt s).toNat := by
      intro s
      unfold tauN
      rw [Array.getD_eq_getD_getElem?, hget]
      rfl
    have hle : h.calls[c].k ≤ h.kT := hkc ▸ hk c hcN
    unfold tTK
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, Array.length_toList]; exact hcs),
        List.getElem_map,
      Array.getElem_toList]
    have hex : exL (xt.reverse ++ (xc.reverse ++ xp.reverse)) (h.kT - h.calls[c].k) h.kT =
        (xt.take h.calls[c].k).reverse := by
      have := exL_left xt.reverse (xc.reverse ++ xp.reverse) (h.kT - h.calls[c].k)
        (by rw [List.length_reverse, ht]; omega)
      rw [List.length_reverse, ht] at this
      rw [this, List.drop_reverse, ht]
      congr 2
      omega
    rw [hex, tableK_eq _ _ (by rw [List.length_take, ht]; omega) (lt_of_le_of_lt hle h64), hkc]
    exact Finset.sum_congr rfl fun s _ => by rw [htau]
  rw [hz]
  unfold leavesAK joinedK
  rw [hzc, foldl_sum, lsum, ← hp, List.drop_left']
  swap
  · rfl
  have hd : h.d = xc.length + xt.length := by rw [hc, ht]; exact Nat.add_comm _ _
  have hsplit := eqN_split xc xt fun c t =>
    lam - 1 - (((tauN h (min c (h.NC - 1)) (t % 2 ^ kOf h (min c (h.NC - 1))) : ℕ) : K) +
      ((min c (h.NC - 1) : ℕ) : K) * θ)
  rw [hd]
  have e0 : ∀ r, eqN (xc ++ xt) r * (lam - 1 - tabF h θ r) =
      eqN (xc ++ xt) r * (lam - 1 -
        (((tauN h (min (r % 2 ^ xc.length) (h.NC - 1))
            (r / 2 ^ xc.length % 2 ^ kOf h (min (r % 2 ^ xc.length) (h.NC - 1))) : ℕ) : K) +
          ((min (r % 2 ^ xc.length) (h.NC - 1) : ℕ) : K) * θ)) := by
    intro r
    rw [hc]
    rfl
  rw [Finset.sum_congr rfl fun r _ => e0 r, hsplit, hc]
  have hin : ∀ c, ∑ j ∈ range (2 ^ xt.length), eqN xt j *
        (lam - 1 - (((tauN h (min c (h.NC - 1)) (j % 2 ^ kOf h (min c (h.NC - 1))) : ℕ) : K) +
          ((min c (h.NC - 1) : ℕ) : K) * θ)) =
      lam - 1 - ((tTK h (xt.reverse ++ (xc.reverse ++ xp.reverse))).getD (min c (h.NC - 1)) 0 +
        ((min c (h.NC - 1) : ℕ) : K) * θ) := by
    intro c
    have hcN : min c (h.NC - 1) < h.NC := lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
    rw [hT _ hcN, ← eqN_low xt _ (by rw [ht]; exact hk _ hcN) fun s => ((tauN h (min c (h.NC - 1)) s
        : ℕ) : K)]
    have : ∀ j, eqN xt j * (lam - 1 - (((tauN h (min c (h.NC - 1)) (j % 2 ^ kOf h (min c (h.NC -
        1))) : ℕ) : K) +
          ((min c (h.NC - 1) : ℕ) : K) * θ)) =
        eqN xt j * (lam - 1 - ((min c (h.NC - 1) : ℕ) : K) * θ) -
          eqN xt j * ((tauN h (min c (h.NC - 1)) (j % 2 ^ kOf h (min c (h.NC - 1))) : ℕ) : K) := fun
              j => by ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, ← Finset.sum_mul, eqN_total]
    ring
  rw [Finset.sum_congr rfl fun c _ => by rw [hin c]]
  have hout : ∀ c ∈ range (2 ^ h.cK), (eqTabK xc.reverse).getD c 0 = eqN xc c := by
    intro c hcm
    rw [eqTabK_get, List.length_reverse, hc, if_pos (Finset.mem_range.mp hcm), List.reverse_reverse]
  have hR : ∑ c ∈ range (2 ^ h.cK), (eqTabK xc.reverse).getD c 0 *
        ((tTK h (xt.reverse ++ (xc.reverse ++ xp.reverse))).getD (min c (h.NC - 1)) 0 +
          ((min c (h.NC - 1) : ℕ) : K) * θ) =
      ∑ c ∈ range (2 ^ h.cK), eqN xc c *
        ((tTK h (xt.reverse ++ (xc.reverse ++ xp.reverse))).getD (min c (h.NC - 1)) 0 +
          ((min c (h.NC - 1) : ℕ) : K) * θ) := Finset.sum_congr rfl fun c hcm => by rw [hout c hcm]
  rw [hR]
  have : ∀ c, eqN xc c * (lam - 1 - ((tTK h (xt.reverse ++ (xc.reverse ++ xp.reverse))).getD (min c
      (h.NC - 1)) 0 +
        ((min c (h.NC - 1) : ℕ) : K) * θ)) =
      eqN xc c * (lam - 1) - eqN xc c * ((tTK h (xt.reverse ++ (xc.reverse ++ xp.reverse))).getD
          (min c (h.NC - 1)) 0 +
        ((min c (h.NC - 1) : ℕ) : K) * θ) := fun c => by ring
  rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hc,
      eqN_total, one_mul]

end
end Fo

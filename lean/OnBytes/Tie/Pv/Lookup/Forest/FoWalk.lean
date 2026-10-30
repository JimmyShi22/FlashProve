-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoWalk.lean.
The ledger of a lookup's mask entries against the verifier's slots.

The verifier numbers the scalars that a sub-proof sends: each has a slot. A sumcheck that begins at
slot f takes one slot for the sum of its hiding polynomial, one for each scalar of each
round, and one for each value that it shows. When its row is made, the coefficients of the hiding
polynomial are read under the slots from f on IN THE ORDER OF THE VERIFIER's WALK
(by variable, then by degree upwards from 1; the last variable with its constant first), which is
not the order in which the scalars were sent.
The flat function of the lookup names the same entries by (round, power), constant, shown value,
and places them by `TwNums`' `slotCoef`, `slotConst`, `slotShown`.
This file states that the two agree. All is stated over a commutative ring K, on plain data.

Main names:
  `hide_walk`: the value of the flat function's form of the hiding polynomial (`TwV.hide`), with
    its places by `slotCoef` and `slotConst` from f on, is the sum over k of
    (entry k of the walk) times (what stands under slot f + k). The walk is `OnBytes.PscTie.walkK`
    at the pairs (degree + 1, challenge). Premises, here and in `walk_length`: there is at least one
    round, and as many challenges as rounds.
  `walk_length`: the walk has 1 + (sum of the degrees) entries.
  `shown_slot`: shown value number a stands under slot f + (length of the walk) + a.
  `firstOf_succ`, `first_tie`, `first_key`, `first_tab`, `first_end`, `first_bit`, `first_all`: the
    first slot of each sumcheck of a sub-proof's lookup, step by step, in the verifier's own counts
    `sumcheckSlots` and `layerSlots`; up to the end of the last there are `Forest.elems h` slots.

Limits: places and counts alone. That the verifier's routines take these slots in a run is not
  stated here. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoLedger
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRows
import OnBytes.Tie.Pv.Psc.FlatTie

set_option autoImplicit false

namespace Cb.Fo.Walk
open TwV TwNums TwNums.Sizes OnBytes.Model OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K]

theorem sumFrom_append {α : Type} (g : ℕ → α → K) : ∀ (a b : List α) (s : ℕ),
    sumFrom g s (a ++ b) = sumFrom g s a + sumFrom g (s + a.length) b
  | [], b, s => by simp [sumFrom]
  | x :: a, b, s => by
    show g s x + sumFrom g (s + 1) (a ++ b) = g s x + sumFrom g (s + 1) a + sumFrom g
        (s + (a.length + 1)) b
    rw [sumFrom_append g a b (s + 1), show s + 1 + a.length = s + (a.length + 1) by
        omega, add_assoc]

theorem sumFrom_range (c : ℕ → K) (ν : ℕ → K) : ∀ (n s : ℕ),
    sumFrom (fun j x => x * ν j) s ((List.range n).map c) =
        ((List.range n).map fun t => c t * ν (s + t)).sum
  | 0, _ => rfl
  | n + 1, s => by
    rw [List.range_succ, List.map_append, List.map_append, sumFrom_append, List.sum_append,
        sumFrom_range c ν n s]
    simp [sumFrom]

theorem valS_range {P : Type} (p : ℕ → P) (c : ℕ → K) (μ : P → K) (n : ℕ) :
    valS ((List.range n).map fun t => (p t, c t)) μ =
        ((List.range n).map fun t => c t * μ (p t)).sum := by
  unfold valS
  rw [List.map_map]
  rfl

/-- the pairs (number of coefficients, challenge) of the verifier's walk -/
def pairs (dg : List ℕ) (xs : List K) : List (ℕ × K) := (dg.map (· + 1)).zip xs

/-- The rounds from number r0 on, whose first slot is f. -/
theorem hideGo_walk {P : Type} (pw : ℕ → ℕ → P) (c0 : P) (μ : P → K) (ν : ℕ → K) : ∀ (dg : List ℕ)
    (xs : List K) (r0 f : ℕ),
    dg ≠ [] → xs.length = dg.length →
    (∀ r t, r < dg.length → t < dg.getD r 0 → μ (pw (r0 + r) t) = ν (slotCoef dg f r t)) → μ c0 = ν
        (slotConst dg f) →
    valS (hideGo pw r0 dg xs) μ + μ c0 = sumFrom (fun j x => x * ν j) f (walkK (pairs dg xs))
  | [], _, _, _, h, _, _, _ => absurd rfl h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | [n], [x], r0, f, _, _, hp, hc => by
    show valS (((List.range n).map fun t => (pw r0 t, x ^ (t + 1))) ++ []) μ + μ c0 =
      sumFrom (fun j x => x * ν j) f ((List.range (n + 1)).map fun t => x ^ t)
    rw [List.append_nil, valS_range, sumFrom_range, List.range_succ_eq_map, List.map_cons,
        List.sum_cons, List.map_map, hc, add_comm]
    refine congrArg₂ (· + ·) (by
        simp [slotConst]) (congrArg List.sum (List.map_congr_left fun t ht => ?_))
    have := hp 0 t (by simp) (by simpa using List.mem_range.mp ht)
    rw [Nat.add_zero] at this
    rw [this]
    show x ^ (t + 1) * ν (f + 0 + (if 0 + 1 = 1 then 1 else 0) + t) = x ^ (t + 1) * ν (f + (t + 1))
    rw [if_pos rfl, show f + 0 + 1 + t = f + (t + 1) by omega]
  | [_], _ :: _ :: _, _, _, _, h, _, _ => by simp at h
  | n :: m :: dg, [_], _, _, _, h, _, _ => by simp at h
  | n :: m :: dg, x :: y :: xs, r0, f, _, hl, hp, hc => by
    have ih :=
      hideGo_walk pw c0 μ ν (m :: dg) (y :: xs) (r0 + 1) (f + n) (by simp) (by simpa using hl)
      (fun r t hr ht => by
        have := hp (r + 1) t (by simpa using hr) (by simpa using ht)
        rw [show r0 + 1 + r = r0 + (r + 1) by omega, this]
        unfold slotCoef
        simp only [List.take_succ_cons, List.sum_cons, List.length_cons]
        congr 1
        split_ifs <;> omega)
      (by
        rw [hc]
        unfold slotConst
        rw [List.dropLast_cons₂, List.sum_cons, Nat.add_assoc])
    show valS (((List.range n).map fun t => (pw r0 t, x ^ (t + 1))) ++ hideGo pw (r0 + 1) (m :: dg)
        (y :: xs)) μ + μ c0 =
      sumFrom (fun j x => x * ν j) f (((List.range (n + 1 - 1)).map fun t => x ^ (t + 1)) ++ walkK
          (pairs (m :: dg) (y :: xs)))
    rw [valS_append, add_assoc, ih, sumFrom_append, valS_range, Nat.add_sub_cancel, sumFrom_range,
        List.length_map, List.length_range]
    refine congrArg (· + _) (congrArg List.sum (List.map_congr_left fun t ht => ?_))
    have := hp 0 t (by simp) (by simpa using List.mem_range.mp ht)
    rw [Nat.add_zero] at this
    rw [this]
    unfold slotCoef
    simp

/-- **The flat function's form of the hiding polynomial reads the slots in the order of the
verifier's walk.** -/
theorem hide_walk {P : Type} (L : Led P) (μ : P → K) (ν : ℕ → K) (dg : List ℕ) (xs : List K) (f : ℕ)
    (hne : dg ≠ []) (hl : xs.length = dg.length)
    (hp : ∀ r t, r < dg.length → t < dg.getD r 0 → μ (L.pw r t) = ν (slotCoef dg f r t))
        (hc : μ L.c0 = ν (slotConst dg f)) :
    valS (hide L dg xs) μ = sumFrom (fun j x => x * ν j) f (walkK (pairs dg xs)) := by
  unfold hide
  rw [valS_append, ← hideGo_walk L.pw L.c0 μ ν dg xs 0 f hne hl
      (fun r t hr ht => by rw [Nat.zero_add]; exact hp r t hr ht) hc]
  simp [valS]

theorem walk_length : ∀ (dg : List ℕ) (xs : List K), dg ≠ [] → xs.length = dg.length →
    (walkK (pairs dg xs)).length = 1 + dg.sum
  | [], _, h, _ => absurd rfl h
  | _ :: _, [], _, h => by simp at h
  | [n], [x], _, _ => by
    show ((List.range (n + 1)).map fun t => x ^ t).length = _
    simp
    omega
  | [_], _ :: _ :: _, _, h => by simp at h
  | n :: m :: dg, [_], _, h => by simp at h
  | n :: m :: dg, x :: y :: xs, _, hl => by
    show (((List.range (n + 1 - 1)).map fun t => x ^ (t + 1)) ++ walkK
        (pairs (m :: dg) (y :: xs))).length = _
    rw [List.length_append, walk_length (m :: dg) (y :: xs) (by simp) (by simpa using hl)]
    simp
    omega

end

/-- Shown value number a stands behind the walk. -/
theorem shown_slot (dg : List ℕ) (f a : ℕ) : slotShown dg f a = f + (1 + dg.sum) + a := by
  unfold slotShown
  omega

/-! ## The first slot of each sumcheck -/

theorem firstOf_succ (S : Sizes) (i : ℕ) (hi : i < S.scs.length) :
    S.firstOf (i + 1) = S.firstOf i + (S.scs.getD i ⟨[], false, 0⟩).masks := by
  unfold Sizes.firstOf
  rw [List.take_add_one, List.map_append, List.sum_append, List.getD_eq_getElem _ _ hi,
    List.getElem?_eq_getElem hi]
  simp

theorem getD_map_range (g : ℕ → Sc) (n i : ℕ) (hi : i < n) (d : Sc) :
    ((List.range n).map g).getD i d = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem scs_length (S : Sizes) : S.scs.length = S.n + 1 + S.v + S.d + 2 := by
  simp [Sizes.scs]
  omega

theorem scs_tie (S : Sizes) (j : ℕ) (hj : j < S.n + 1) (d : Sc) : S.scs.getD (S.iTie j) d = S.scTie
    j := by
  unfold Sizes.scs Sizes.iTie
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append _ _ _ _ (by simpa using hj), getD_map_range _ _ _ hj]

theorem scs_key (S : Sizes) (l : ℕ) (hl : l < S.v) (d : Sc) : S.scs.getD (S.iKey l) d = S.scKey l :=
  by
  unfold Sizes.scs Sizes.iKey
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp), getD_map_range _ _ _ (by simpa using hl)]
  simp

theorem scs_tab (S : Sizes) (l : ℕ) (hl : l < S.d) (d : Sc) : S.scs.getD (S.iTab l) d = S.scTab l :=
  by
  unfold Sizes.scs Sizes.iTab
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp),
    getD_map_range _ _ _ (by simpa using hl)]
  simp

theorem scs_end (S : Sizes) (d : Sc) : S.scs.getD S.iEnd d = S.scEnd := by
  unfold Sizes.scs Sizes.iEnd
  have hlen : ((List.range (S.n + 1)).map S.scTie ++ (List.range S.v).map S.scKey ++
      (List.range S.d).map S.scTab).length = S.n + 1 + S.v + S.d := by
    simp
    omega
  rw [List.getD_append_right _ _ _ _ (le_of_eq hlen), hlen, Nat.sub_self]
  rfl

theorem scs_bit (S : Sizes) (d : Sc) : S.scs.getD S.iBit d = S.scBit := by
  unfold Sizes.scs Sizes.iBit
  have hlen : ((List.range (S.n + 1)).map S.scTie ++ (List.range S.v).map S.scKey ++
      (List.range S.d).map S.scTab).length = S.n + 1 + S.v + S.d := by
    simp
    omega
  rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
    show S.n + 1 + S.v + S.d + 1 - (S.n + 1 + S.v + S.d) = 1 by omega]
  rfl

section Forest
variable (h : Forest.Shape)

theorem first_tie0 : (FoNums.S h).fTie 0 = 0 := rfl

theorem first_tie (j : ℕ) (hj : j < 31) : (FoNums.S h).fTie (j + 1) =
    (FoNums.S h).fTie j + sumcheckSlots .eq2 0 (if j = 0 then 3 else 2) 3 := by
  have e := firstOf_succ (FoNums.S h) j (by rw [scs_length]; show j < 30 + 1 + _ + _ + 2; omega)
  rw [show j = (FoNums.S h).iTie j from rfl, scs_tie (FoNums.S h) j hj] at e
  refine e.trans (congrArg₂ (· + ·) rfl ?_)
  show 1 + [3].sum + (if j = 0 then 3 else 2) = 1 + 0 * 2 + 3 + (if j = 0 then 3 else 2)
  simp

theorem first_key0 : (FoNums.S h).fKey 0 = (FoNums.S h).fTie 31 := rfl

theorem first_key (l : ℕ) (hl : l < h.v) : (FoNums.S h).fKey (l + 1) = (FoNums.S h).fKey l +
    layerSlots l := by
  have e := firstOf_succ (FoNums.S h) ((FoNums.S h).iKey l)
    (by rw [scs_length]; show 30 + 1 + l < 30 + 1 + h.v + _ + 2; omega)
  rw [scs_key (FoNums.S h) l hl] at e
  refine e.trans (congrArg₂ (· + ·) rfl ?_)
  show 1 + (List.replicate l 2 ++ [2]).sum + 2 = 1 + l * 2 + 2 + 2
  simp
  omega

theorem first_tab0 : (FoNums.S h).fTab 0 = (FoNums.S h).fKey h.v := rfl

theorem first_tab (l : ℕ) (hl : l < h.d) : (FoNums.S h).fTab (l + 1) = (FoNums.S h).fTab l +
    layerSlots (5 + l) := by
  have e := firstOf_succ (FoNums.S h) ((FoNums.S h).iTab l)
    (by rw [scs_length]; show 30 + 1 + h.v + l < 30 + 1 + h.v + h.d + 2; omega)
  rw [scs_tab (FoNums.S h) l hl] at e
  refine e.trans (congrArg₂ (· + ·) rfl ?_)
  show 1 + (List.replicate (5 + l) 2 ++ [2]).sum + 2 = 1 + (5 + l) * 2 + 2 + 2
  simp
  omega

theorem first_end : (FoNums.S h).fEnd = (FoNums.S h).fTab h.d := rfl

theorem first_bit : (FoNums.S h).fBit = (FoNums.S h).fEnd + (1 + 2 * h.d + 5) := by
  have e := firstOf_succ (FoNums.S h) (FoNums.S h).iEnd
    (by rw [scs_length]; show 30 + 1 + h.v + h.d < 30 + 1 + h.v + h.d + 2; omega)
  rw [scs_end] at e
  refine e.trans (congrArg₂ (· + ·) rfl ?_)
  show 1 + ((List.range (5 + h.d)).reverse.map fun t => if t < 5 then 1 else 2).sum + 0 = _
  rw [List.map_reverse, List.sum_reverse, FoLedger.end_sum]
  omega

/-- Up to the end of the last sumcheck there are as many slots as the verifier counts. -/
theorem first_all : (FoNums.S h).fBit + sumcheckSlots .eq2 (5 + h.d) 1 2 = Forest.elems h := by
  have e := firstOf_succ (FoNums.S h) (FoNums.S h).iBit
    (by rw [scs_length]; show 30 + 1 + h.v + h.d + 1 < 30 + 1 + h.v + h.d + 2; omega)
  rw [scs_bit] at e
  have e2 : (FoNums.S h).firstOf ((FoNums.S h).iBit + 1) = FoNums.nMasks h := by
    unfold Sizes.firstOf FoNums.nMasks Sizes.nMasks
    rw [List.take_of_length_le (by
      rw [scs_length]
      show 30 + 1 + h.v + h.d + 2 ≤ 30 + 1 + h.v + h.d + 1 + 1
      omega)]
  rw [← FoLedger.elems_eq, ← e2, e]
  refine congrArg₂ (· + ·) rfl ?_
  show 1 + (5 + h.d) * 2 + 2 + 1 = 1 + (List.replicate (5 + h.d) 2 ++ [2]).sum + 1
  simp
  omega

end Forest

end Cb.Fo.Walk

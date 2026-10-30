-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPts.lean.
The arrays of points of the sub-proofs' lookup, as lists.

The program (OnBytes/Model/Look.lean) holds a point as an array whose place 0 belongs to the top
bit. The flat verifier (Cb/Pv/Lookup/Out/TwV.lean) holds a point by coordinate, coordinate t
belonging to bit t. So each array is a point
read backwards. This file defines the arrays off a trace (rhoK, rhoT, rhoTab, zx, zy, zk, zb0, zb1
and the split of zb) for any commutative ring and proves closed forms in the challenges: behind a
level that binds from
the highest variable down, the array is the challenges in the order of the rounds; behind the last
key level, place i holds the challenge of round rnd k rK i, if rK + 9 ≤ k. forest_points gathers
them for one shape, under: 10 ≤ h.dT; N's orders oK, oE, oB are FoNums.ordK h, ordE h, ordB h; the
trace's key side has h.v levels. (Its premise h.v = h.dT + h.rK holds by definition.) The last
lemmas give the same arrays by coordinates of the point, for points of the named lengths.
Not claimed: that these lists are the arrays that the program computes on a run. That is compared at
recorded runs, not proved here. In forest_points the clause on rhoT restates its definition.

-/
import Cb.Pv.Lookup.Out.TwV
import OnBytes.Tie.Pv.Lookup.Port.E3OrdPort
import OnBytes.Tie.Pv.Lookup.Port.FoNums
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace Fo
open TwV

/-! ### lists alone -/

theorem idxOf_of_getD {L : List ℕ} (hn : L.Nodup) {j a : ℕ} (hj : j < L.length) (h : L.getD j 0 = a)
    : L.idxOf a = j := by
  rw [List.getD_eq_getElem _ _ hj] at h
  rw [← h]
  exact hn.idxOf_getElem j hj

theorem reverse_map_range {α : Type} (k : ℕ) (f : ℕ → α) :
    ((List.range k).map f).reverse = (List.range k).map fun i => f (k - 1 - i) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
      List.length_range]

section
variable {K : Type} [CommRing K]

theorem back_byVar (L : List ℕ) (k : ℕ) (hL : L.Perm (List.range k)) (r : ℕ → ℕ)
    (hr : ∀ i < k, r i < k ∧ L.getD (r i) 0 = k - 1 - i) (xs : List K) :
    (byVar L xs).reverse = (List.range k).map fun i => xs.getD (r i) 0 := by
  have hlen : L.length = k := by rw [hL.length_eq, List.length_range]
  have hn : L.Nodup := hL.symm.nodup List.nodup_range
  unfold byVar
  rw [hlen, reverse_map_range]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < k := List.mem_range.mp hi
  rw [idxOf_of_getD hn (by rw [hlen]; exact (hr i hi').1) (hr i hi').2]

theorem default_at (k i : ℕ) (hi : i < k) : (E3.defaultList k).getD i 0 = k - 1 - i := by
  unfold E3.defaultList
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_reverse, List.getElem_range,
      List.length_range]

theorem back_default (k : ℕ) (xs : List K) :
    (byVar (OnBytes.Model.orderDefault k) xs).reverse = (List.range k).map fun i => xs.getD i 0 :=
  back_byVar (E3.defaultList k) k (E3.defaultList_perm k) id (fun i hi => ⟨hi, default_at k i hi⟩)
      xs

end

/-! ### the forest's last order -/

/-- which round's challenge stands at place i of the array behind the last key level's sumcheck (k
variables, rK of them the tree's number's) -/
def rnd (k rK i : ℕ) : ℕ :=
  if i < k - rK - 9 then i + 9
  else if i < k - rK then 6 - 3 * ((i - (k - rK - 9)) / 3) + (i - (k - rK - 9)) % 3
  else i

theorem last_low {mu rK t : ℕ} (h : rK + 9 ≤ mu) (ht : t < rK) : (E3.lastList mu rK).getD (mu - rK +
    t) 0 = rK - 1 - t := by
  unfold E3.lastList
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  have e : mu - rK + t -
      ([2, 1, 0, 5, 4, 3, 8, 7, 6].map (rK + ·) ++
        ((List.range (mu - (rK + 9))).map (rK + 9 + ·)).reverse).length = t := by
    simp; omega
  rw [e, List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_reverse, List.getElem_range,
    List.length_range]

theorem last_mid {mu rK j : ℕ} (h9 : 9 ≤ j) (hj : j < mu - rK) : (E3.lastList mu rK).getD j 0 = mu +
    8 - j := by
  unfold E3.lastList
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
  have e : j - ([2, 1, 0, 5, 4, 3, 8, 7, 6].map (rK + ·)).length = j - 9 := by simp
  rw [e, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse, List.getElem_map,
    List.getElem_range]
  simp only [List.length_map, List.length_range]
  omega

theorem last_nine {mu rK j : ℕ} (hj : j < 9) : (E3.lastList mu rK).getD j 0 = rK + 3 * (j / 3) + (2
    - j % 3) := by
  unfold E3.lastList
  rw [List.append_assoc, List.getD_append _ _ _ _ (by simpa using hj)]
  interval_cases j <;> simp

theorem rnd_at {k rK : ℕ} (h : rK + 9 ≤ k) (i : ℕ) (hi : i < k) :
    rnd k rK i < k ∧ (E3.lastList k rK).getD (rnd k rK i) 0 = k - 1 - i := by
  unfold rnd
  split_ifs with h1 h2
  · refine ⟨by omega, ?_⟩
    rw [last_mid (by omega) (by omega)]
    omega
  · have h3 : i - (k - rK - 9) < 9 := by omega
    generalize hq : i - (k - rK - 9) = q at h3 ⊢
    have hj : 6 - 3 * (q / 3) + q % 3 < 9 := by omega
    refine ⟨by omega, ?_⟩
    rw [last_nine hj]
    interval_cases q <;> omega
  · refine ⟨hi, ?_⟩
    have e : i = k - rK + (i - (k - rK)) := by omega
    rw [e, last_low h (by omega)]
    omega

section
variable {K : Type} [CommRing K]

theorem back_forest {k rK : ℕ} (h : rK + 9 ≤ k) (xs : List K) :
    (byVar (OnBytes.Model.Forest.orderForestRange k rK) xs).reverse = (List.range k).map fun i =>
        xs.getD (rnd k rK i) 0 :=
  back_byVar (E3.lastList k rK) k (E3.lastList_perm h) (rnd k rK) (rnd_at h) xs

theorem place_list (m : ℕ) : (List.range m).map (FoNums.placeOf m) = OnBytes.Model.orderDefault m :=
    by
  unfold OnBytes.Model.orderDefault FoNums.placeOf
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_range]

theorem back_place (m : ℕ) (xs : List K) :
    (byVar ((List.range m).map (FoNums.placeOf m)) xs).reverse = (List.range m).map fun i => xs.getD
        i 0 := by
  rw [place_list]; exact back_default m xs

theorem rho_top (o : ℕ → List ℕ) (p0 : List K) (s : Sc K × K) (rest : List (Sc K × K)) :
    (pntTop o p0 (s :: rest)).reverse = s.2 :: (byVar (o rest.length) s.1.xs).reverse := by
  show (byVar (o rest.length) s.1.xs ++ [s.2]).reverse = _
  rw [List.reverse_append]
  rfl

/-! ### the program's arrays, off a trace -/

/-- keys.rho behind the key levels done (Look.lean:383-386) -/
def rhoK {P : Type} (N : Nums P K) (t : Trace K) : List K := (pntTop N.oK [] t.keys.reverse).reverse
/-- t.rhoT: the planes' point, reversed on receipt (Look.lean:247) -/
def rhoT (t : Trace K) : List K := t.join.reverse
/-- table.rho behind the table levels done (Look.lean:390-392) -/
def rhoTab {P : Type} (N : Nums P K) (t : Trace K) : List K := (pntTop N.oT t.join
    t.tabl.reverse).reverse
/-- Look.lean:387-388 -/
def zx (dT : ℕ) (rho : List K) : List K := rho.take dT
def zy (dT : ℕ) (rho : List K) : List K := rho.drop dT
/-- Look.lean:411: zy.extract (rK − iota_c) zy.size ++ zx -/
def zk (rK io : ℕ) (x y : List K) : List K := y.drop (rK - io) ++ x
/-- Look.lean:398-399, :403 -/
def zb0 {P : Type} (N : Nums P K) (t : Trace K) : List K := (byVar N.oE t.cls.xs).reverse
def zb1 {P : Type} (N : Nums P K) (t : Trace K) : List K := (byVar N.oB t.bits.xs).reverse
/-- (t | c | j) = [0, kT) | [kT, kT + cK) | the last five (Look.lean:162-165, :414-415) -/
def zbT (kT : ℕ) (zb : List K) : List K := zb.take kT
def zbC (kT cK : ℕ) (zb : List K) : List K := (zb.drop kT).take cK
def zbJ (kT cK : ℕ) (zb : List K) : List K := zb.drop (kT + cK)

theorem take_map_range {α : Type} (f : ℕ → α) {a b : ℕ} (h : a ≤ b) : ((List.range b).map f).take a
    = (List.range a).map f := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem drop_map_range {α : Type} (f : ℕ → α) (a c : ℕ) : ((List.range (a + c)).map f).drop a =
    (List.range c).map fun u => f (a + u) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_drop, List.getElem_map, List.getElem_range]

/-- a key level that is not the last, and every table level: behind it the array is the line's draw,
then the challenges in the order of the rounds -/
theorem rho_key_inner (h : FoNums.Sh) (s : Sc K × K) (rest : List (Sc K × K)) (hl : rest.length + 1
    ≠ h.v) :
    (pntTop (FoNums.ordK h) [] (s :: rest)).reverse = s.2 :: (List.range rest.length).map fun i =>
        s.1.xs.getD i 0 := by
  rw [rho_top]
  unfold FoNums.ordK
  rw [if_neg hl, back_default]

theorem rho_table (join : List K) (s : Sc K × K) (rest : List (Sc K × K)) :
    (pntTop FoNums.ordT join (s :: rest)).reverse = s.2 :: (List.range (FoNums.w + rest.length)).map
        fun i => s.1.xs.getD i 0 := by
  rw [rho_top]
  unfold FoNums.ordT
  rw [back_default]

/-- the last key level -/
theorem rho_key_last (h : FoNums.Sh) (h9 : h.rK + 9 ≤ h.v - 1) (s : Sc K × K) (rest : List (Sc K ×
    K)) (hl : rest.length + 1 = h.v) :
    (pntTop (FoNums.ordK h) [] (s :: rest)).reverse =
      s.2 :: (List.range (h.v - 1)).map fun i => s.1.xs.getD (rnd (h.v - 1) h.rK i) 0 := by
  have e : rest.length = h.v - 1 := by omega
  rw [rho_top]
  unfold FoNums.ordK
  rw [if_pos hl, e, back_forest h9]

/-- **forest_points**: GENERAL IN h; no premise on a transcript: for every trace whose key side has
h.v levels, the last of them (s, ρ) -/
theorem forest_points {P : Type} (h : FoNums.Sh) (N : Nums P K) (t : Trace K)
    (hv : h.v = h.dT + h.rK) (h10 : 10 ≤ h.dT)
    (hK : N.oK = FoNums.ordK h) (hE : N.oE = FoNums.ordE h) (hB : N.oB = FoNums.ordB h)
    (ks : List (Sc K × K)) (s : Sc K) (ρ : K) (hk : t.keys = ks ++ [(s, ρ)]) (hl : ks.length + 1 =
        h.v) :
    rhoK N t = ρ :: (List.range (h.v - 1)).map (fun i => s.xs.getD (rnd (h.v - 1) h.rK i) 0) ∧
    zx h.dT (rhoK N t) = ρ :: (List.range (h.dT - 1)).map (fun i => s.xs.getD (rnd (h.v - 1) h.rK i)
        0) ∧
    zy h.dT (rhoK N t) = (List.range h.rK).map (fun u => s.xs.getD (h.dT - 1 + u) 0) ∧
    rhoT t = t.join.reverse ∧
    zb0 N t = (List.range (FoNums.w + h.d)).map (fun i => t.cls.xs.getD i 0) ∧
    zb1 N t = (List.range (FoNums.w + h.d)).map (fun i => t.bits.xs.getD i 0) := by
  have e1 : rhoK N t = ρ :: (List.range (h.v - 1)).map (fun i => s.xs.getD (rnd (h.v - 1) h.rK i) 0)
      := by
    unfold rhoK
    rw [hK, hk, List.reverse_append]
    exact rho_key_last h (by omega) (s, ρ) ks.reverse (by rw [List.length_reverse]; exact hl)
  refine ⟨e1, ?_, ?_, rfl, ?_, ?_⟩
  · unfold zx
    obtain ⟨a, ha⟩ : ∃ a, h.dT = a + 1 := ⟨h.dT - 1, by omega⟩
    rw [e1, ha, List.take_succ_cons, Nat.add_sub_cancel, take_map_range _ (by omega)]
  · unfold zy
    obtain ⟨a, ha⟩ : ∃ a, h.dT = a + 1 := ⟨h.dT - 1, by omega⟩
    have e2 : h.v - 1 = a + h.rK := by omega
    rw [e1, ha, List.drop_succ_cons, Nat.add_sub_cancel, e2, drop_map_range]
    refine List.map_congr_left fun u hu => ?_
    have hu' : u < h.rK := List.mem_range.mp hu
    have e3 : rnd (a + h.rK) h.rK (a + u) = a + u := by
      unfold rnd
      rw [if_neg (by omega), if_neg (by omega)]
    rw [e3]
  · unfold zb0 FoNums.ordE at *
    rw [hE, back_place]
  · unfold zb1 FoNums.ordB at *
    rw [hB, back_place]

/-! ### by coordinates: p the point by coordinate (coordinate t = bit t), rho = p.reverse -/

omit [CommRing K] in
theorem zx_coord (dT rK : ℕ) (p : List K) (hp : p.length = dT + rK) : zx dT p.reverse = (p.drop
    rK).reverse := by
  unfold zx
  rw [List.take_reverse, hp, Nat.add_sub_cancel_left]

omit [CommRing K] in
theorem zy_coord (dT rK : ℕ) (p : List K) (hp : p.length = dT + rK) : zy dT p.reverse = (p.take
    rK).reverse := by
  unfold zy
  rw [List.drop_reverse, hp, Nat.add_sub_cancel_left]

omit [CommRing K] in
/-- call c's point: BY COORDINATE it is the place in a tree (the dT coordinates above the tree's
number), then the low io coordinates of the tree's number: FoNums.keyOf's index X / 2^rK + 2^dT (y %
2^io) -/
theorem zk_coord (dT rK io : ℕ) (hio : io ≤ rK) (p : List K) (hp : p.length = dT + rK) :
    zk rK io (zx dT p.reverse) (zy dT p.reverse) = (p.drop rK ++ p.take io).reverse := by
  unfold zk
  rw [zx_coord dT rK p hp, zy_coord dT rK p hp, List.reverse_append, List.drop_reverse,
      List.length_take, hp,
    Nat.min_eq_left (by omega), Nat.sub_sub_self hio, List.take_take, Nat.min_eq_left hio]

omit [CommRing K] in
/-- (t | c | j): by coordinate: the plane's five are the LOW coordinates, then the call's cK, then
the row's kT -/
theorem zbJ_coord (kT cK w : ℕ) (q : List K) (hq : q.length = w + (cK + kT)) : zbJ kT cK q.reverse =
    (q.take w).reverse := by
  unfold zbJ
  rw [List.drop_reverse, hq]
  congr 2
  omega
omit [CommRing K] in
theorem zbT_coord (kT cK w : ℕ) (q : List K) (hq : q.length = w + (cK + kT)) : zbT kT q.reverse =
    (q.drop (w + cK)).reverse := by
  unfold zbT
  rw [List.take_reverse, hq]
  congr 2
  omega
omit [CommRing K] in
theorem zbC_coord (kT cK w : ℕ) (q : List K) (hq : q.length = w + (cK + kT)) : zbC kT cK q.reverse =
    ((q.drop w).take cK).reverse := by
  unfold zbC
  rw [List.drop_reverse, hq, List.take_reverse, List.length_take, hq, List.drop_take]
  congr 2
  · omega
  · congr 1
    omega

/-- the first places of zx, by hand: the line's draw; then the challenges 9, 10, …; its last nine:
6, 7, 8, 3, 4, 5, 0, 1, 2 -/
example : (List.range 22).map (rnd 23 4) = [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 6, 7, 8, 3, 4, 5,
    0, 1, 2, 19, 20, 21] := by decide
/-- not hollow: at k = 23, rK = 4 the array differs from the default's -/
example : (List.range 23).map (rnd 23 4) ≠ List.range 23 := by decide

end
end Fo

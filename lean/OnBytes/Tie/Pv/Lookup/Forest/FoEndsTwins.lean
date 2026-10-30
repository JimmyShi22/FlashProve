-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoEndsTwins.lean.
The fields of the flat function's end values that are computed without a message are the plain twins
of the byte-level verifier's functions.

endsOf h lm jLK rs (OnBytes/Tie/Pv/Lookup/Forest/FoEnds.lean) writes the public factor, the calls'
weights and points, the calls'
tables at the leaves' point and the factor of the planes' value there as sums over cubes. The plain
twins (OnBytes/Tie/Pv/Lookup/Forest/FoTab.lean, OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean,
OnBytes/Tie/Pv/Lookup/Forest/FoPadFac.lean) are written fold for fold as Forest.pad computes
them,
and OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean shows that the byte-level functions, read in a ring, are
these twins. This file
closes the triangle, under lawful public numbers (FoNums.ok h) and for every list of rounds.

* ends_a, ends_e_all, ends_zk_all, ends_leavesA, ends_tT: the five fields.
* tTK_get: a call's entry of tTK as a sum over its table's cube.
* heard_a, heard_e, heard_zk, heard_tT, heard_leavesA: so the byte-level values, read by ρ, are the
  record's fields, given that the byte-level θ, α, zx, zy, zb0 read as the record's.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTwinsFac
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRows
import OnBytes.Tie.Pv.Lookup.Forest.FoEndsE

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes OnBytes.Model

section
variable {K : Type} [CommRing K]

theorem list_ext_getD {α : Type} (d : α) {a b : List α} (hl : a.length = b.length)
    (h : ∀ i, i < a.length → a.getD i d = b.getD i d) : a = b := by
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have := h i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

variable (h : Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : Rounds K)

include H in
/-- The public factor. -/
theorem ends_a : (endsOf h lm jLK rs).a =
    Cb.Fo.PadFac.facK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha :=
  Cb.Fo.PadFac.pad_fac h H lm jLK _ _

include H in
/-- The calls' weights. -/
theorem ends_e_all :
    (endsOf h lm jLK rs).e = (List.range h.NC).map (eK h (endsOf h lm jLK rs).zy) := by
  have hl : (endsOf h lm jLK rs).e.length = h.NC := by
    show ((List.range h.NC).map _).length = _
    rw [List.length_map, List.length_range]
  refine list_ext_getD 0 (by rw [hl, List.length_map, List.length_range]) fun c hc => ?_
  rw [hl] at hc
  rw [ends_e h H lm jLK rs c hc, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map,
    List.getElem_range]

include H in
/-- The calls' points. -/
theorem ends_zk_all : (endsOf h lm jLK rs).zk = (List.range h.NC).map fun c =>
    zk h.rK (io h c) (endsOf h lm jLK rs).zx (endsOf h lm jLK rs).zy := by
  have hl : (endsOf h lm jLK rs).zk.length = h.NC := by
    show ((List.range h.NC).map _).length = _
    rw [List.length_map, List.length_range]
  refine list_ext_getD [] (by rw [hl, List.length_map, List.length_range]) fun c hc => ?_
  rw [hl] at hc
  rw [ends_zk h H lm jLK rs c hc, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map,
    List.getElem_range]

/-- The leaves' point by coordinate has 5 + d coordinates. -/
theorem gam_len : (byVar (forN h lm jLK rs).oE (forTrace h lm jLK rs).cls.xs).length =
    FoNums.w + h.d := by
  rw [byVar_len]
  exact ordE_len h

include H in
/-- alpha - 1 - (the joined table at the leaves' point). -/
theorem ends_leavesA : (endsOf h lm jLK rs).leavesA =
    leavesAK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha (endsOf h lm jLK rs).zb0 :=
  tab_ext_g h H _ _ _ (gam_len h lm jLK rs)

/-- A call's entry of tTK: its table's extension at the low k_c coordinates of the row. -/
theorem tTK_get (hs : h.calls.size = h.NC) (hk : ∀ c < h.NC, kOf h c ≤ h.kT) (h64 : h.kT < 64)
    (xt z : List K) (ht : xt.length = h.kT) (c : ℕ) (hcN : c < h.NC) :
    (tTK h (xt.reverse ++ z)).getD c 0 =
      ∑ s ∈ range (2 ^ kOf h c), eqN (xt.take (kOf h c)) s * ((tauN h c s : ℕ) : K) := by
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
    List.getElem_map, Array.getElem_toList]
  have hex : exL (xt.reverse ++ z) (h.kT - h.calls[c].k) h.kT = (xt.take h.calls[c].k).reverse := by
    have := exL_left xt.reverse z (h.kT - h.calls[c].k) (by rw [List.length_reverse, ht]; omega)
    rw [List.length_reverse, ht] at this
    rw [this, List.drop_reverse, ht]
    congr 2
    omega
  rw [hex, tableK_eq _ _ (by rw [List.length_take, ht]; omega) (lt_of_le_of_lt hle h64), hkc]
  exact Finset.sum_congr rfl fun s _ => by rw [htau]

include H in
/-- The calls' tables at the leaves' point. -/
theorem ends_tT : (endsOf h lm jLK rs).tT = tTK h (endsOf h lm jLK rs).zb0 := by
  obtain ⟨h1, h2, h3, h4, h16⟩ := ok_facts h H
  have h64 : h.kT < 64 := by omega
  have hd : h.d = h.kT + h.cK := rfl
  have hw : FoNums.w = 5 := rfl
  generalize hg : byVar (forN h lm jLK rs).oE (forTrace h lm jLK rs).cls.xs = g
  have hgl : g.length = FoNums.w + h.d := by rw [← hg]; exact gam_len h lm jLK rs
  have hzb : (endsOf h lm jLK rs).zb0 = g.reverse := by rw [← hg]; rfl
  have hT : (endsOf h lm jLK rs).tT = (List.range h.NC).map fun c =>
      ((List.range (2 ^ h.kT)).map fun r =>
        eqN ((g.drop (FoNums.w + h.cK)).take h.kT) r *
          tabF h (thetaOf h rs) (r * 2 ^ h.cK + c)).sum - (c : K) * thetaOf h rs := by
    rw [← hg]
    rfl
  obtain ⟨xt, hxt⟩ : ∃ xt, xt = g.drop (FoNums.w + h.cK) := ⟨_, rfl⟩
  have hxl : xt.length = h.kT := by rw [hxt, List.length_drop]; omega
  have hrev : g.reverse = xt.reverse ++ (g.take (FoNums.w + h.cK)).reverse := by
    rw [hxt, ← List.reverse_append, List.take_append_drop]
  have htk : (g.drop (FoNums.w + h.cK)).take h.kT = xt := by
    rw [← hxt, ← hxl, List.take_length]
  rw [hT, hzb, hrev, htk]
  refine list_ext_getD 0 (by
    rw [List.length_map, List.length_range]
    unfold tTK
    rw [List.length_map, Array.length_toList, h3]) fun c hc => ?_
  rw [List.length_map, List.length_range] at hc
  rw [tTK_get h h3 h4 h64 xt _ hxl c hc, List.getD_eq_getElem _ _ (by simpa using hc),
    List.getElem_map, List.getElem_range, lsum]
  have hc2 : c < 2 ^ h.cK := lt_of_lt_of_le hc h2
  have e0 : ∀ r, tabF h (thetaOf h rs) (r * 2 ^ h.cK + c) =
      ((tauN h c (r % 2 ^ kOf h c) : ℕ) : K) + (c : K) * thetaOf h rs := by
    intro r
    have a1 : (r * 2 ^ h.cK + c) % 2 ^ h.cK = c := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc2]
    have a2 : (r * 2 ^ h.cK + c) / 2 ^ h.cK = r := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.pow_pos (by norm_num)), Nat.div_eq_of_lt hc2,
        Nat.add_zero]
    have a3 : min c (h.NC - 1) = c := Nat.min_eq_left (by omega)
    unfold tabF rowOf fT
    simp only [a1, a2, a3]
  rw [Finset.sum_congr rfl fun r _ => by rw [e0 r, mul_add], Finset.sum_add_distrib,
    ← Finset.sum_mul, ← hxl, eqN_total, one_mul, add_sub_cancel_right,
    eqN_low xt _ (by rw [hxl]; exact h4 c hc) fun s => ((tauN h c s : ℕ) : K)]

end

/-! ### the byte-level record's five fields -/
section
variable {K : Type} [CommRing K] (ρ : Reading K) (h : Sh) (H : FoNums.ok h = true) (lm jLK : ℕ)
  (rs : Rounds K)

theorem ok_k64 {h : Sh} (H : FoNums.ok h = true) : ∀ k ∈ h.calls.toList, k.k ≤ 64 := by
  obtain ⟨_, _, h3, h4, h16⟩ := ok_facts h H
  intro k hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  rw [Array.length_toList] at hi
  have := h4 i (by rw [← h3]; exact hi)
  unfold kOf at this
  rw [Array.getElem?_eq_getElem hi] at this
  rw [Array.getElem_toList]
  have e : (Option.map (fun x => x.k) (some h.calls[i])).getD 0 = h.calls[i].k := rfl
  rw [e] at this
  omega

include H in
theorem heard_a (θ α : E) (h1 : ρ.val θ = (endsOf h lm jLK rs).theta)
    (h2 : ρ.val α = (endsOf h lm jLK rs).alpha) :
    ρ.val ((List.range h.NT).foldl
      (fun a y => mulE a (powE (subE α (Forest.padKeyOf h θ (h.callOf.getD y 0))) (h.pub.getD y 0)))
      (powE (subE α (Forest.padKeyOf h θ 0)) h.emptyKeys)) = (endsOf h lm jLK rs).a := by
  rw [fac_val' ρ h θ α (ok_callOf H), h1, h2, ends_a h H]

include H in
theorem heard_e (zy : Array E) (h1 : rdL ρ zy = (endsOf h lm jLK rs).zy) :
    rdL ρ ((Array.range h.NC).map (Forest.callWeight h zy)) = (endsOf h lm jLK rs).e := by
  rw [e_val, h1, ends_e_all h H]

include H in
theorem heard_zk (zx zy : Array E) (h1 : rdL ρ zx = (endsOf h lm jLK rs).zx)
    (h2 : rdL ρ zy = (endsOf h lm jLK rs).zy) :
    ((Array.range h.NC).map fun c => zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx).toList.map
      (rdL ρ) = (endsOf h lm jLK rs).zk := by
  rw [zk_val, h1, h2, ends_zk_all h H]

include H in
theorem heard_tT (zb0 : Array E) (h1 : rdL ρ zb0 = (endsOf h lm jLK rs).zb0) :
    rdL ρ (h.calls.map fun k => Forest.tableAt k (zb0.extract (h.kT - k.k) h.kT)) =
      (endsOf h lm jLK rs).tT := by
  rw [tT_val ρ h zb0 (ok_k64 H), h1, ends_tT h H]

include H in
theorem heard_leavesA (θ α : E) (zb0 : Array E) (h1 : ρ.val θ = (endsOf h lm jLK rs).theta)
    (h2 : ρ.val α = (endsOf h lm jLK rs).alpha) (h3 : rdL ρ zb0 = (endsOf h lm jLK rs).zb0) :
    ρ.val (subE (subE α oneE) (Forest.joinedTableAt h θ
      (h.calls.map fun k => Forest.tableAt k (zb0.extract (h.kT - k.k) h.kT))
      (zb0.extract h.kT (h.kT + h.cK)))) = (endsOf h lm jLK rs).leavesA := by
  obtain ⟨_, _, _, _, _, _, hN, _⟩ := Cb.Fo.ok_parts H
  rw [leavesA_val ρ h θ α zb0 (by omega) (ok_k64 H), h1, h2, h3, ends_leavesA h H]

end
end Fo

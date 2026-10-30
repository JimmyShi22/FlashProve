-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Rows/GatedEndsProofs.lean: the end claims of the two product layers of the gated
products: proofs of two statements of Johnson/Road/Rows/GatedEnds.lean.

  `endForm_value`: one sum of the end claims, on true tables: the sum, over the blocks x and the
      features s of a block, of the equality weight of the layer's point at (the block's place | s)
      times the extension over the positions of the library's value at (layer, feature).
  `gatedFirstOut` : GatedFirstOut.
  `gatedSecondOut` : GatedSecondOut.

Limits. Identities in a world in which the tables are true (EndGround): no draw, no soundness,
nothing from the field to the integers.
-/
import Johnson.Road.Rows.GatedEnds
import Johnson.Road.HeadEnds
import Cb.Pv.Lay.End.GatedCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Level tenCell eqTab hiTab)
open OnBytes.Model.Layer (Env Ten sumForms)
open Inst.Model.FFSeg (Dim Cell Arr val slV upV slV' upV' lF lFe)
open Blocks (ext eqN)
open Cb.Pv.Lay.End.Gated (ext_nest ext_neg idx_blocks)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}

/-- One sum of the end claims, on true tables. -/
theorem endForm_value (hρ : Numerals ρ) (hS2 : v.y.S2 = 2 ^ v.y.ls) {A : Arr} (hoff : A.off = 0)
    {X : Ten} (T : Tied c t A X.mat X.place) (wh : ∀ i l, v.y.S2 ∣ tenCell X.place l i 0)
    {r : Array E} {g lT tb : ℕ}
    (R : LongTrue ρ W v tb X.mat v.y.ls lT c (fun j => pt ρ r (g + j))
      (fun j => pt ρ r (g + v.y.ls + j)))
    {la : ℕ} {e : Array E} (he : hiTab r la g = .ok e)
    {rows blocks stride first : ℕ} {lamOf : ℕ → ℕ}
    (hidx : ∀ x, x < rows * blocks → x / blocks * stride + x % blocks < 2 ^ g)
    {a : Aff} (h : endForm v tb X e rows blocks stride lamOf first = some a) :
    a.value ρ W = ∑ x ∈ range (rows * blocks), ∑ s ∈ range (2 ^ v.y.ls),
      eqN (g + v.y.ls) 0 (pt ρ r) ((x / blocks * stride + x % blocks) * 2 ^ v.y.ls + s) *
        ext lT (fun p => val t A (lamOf (x / blocks)) ((first + x % blocks) * 2 ^ v.y.ls + s) p)
          (fun j => pt ρ r (g + v.y.ls + j)) := by
  have hraw : ∀ i j, raw t A i j = fun p => val t A i j p := by
    intro i j
    funext p
    unfold raw
    rw [hoff]
    simp
  have h1 : a.value ρ W = ∑ x ∈ range (rows * blocks),
      ρ.val (e.getD (x / blocks * stride + x % blocks) zeroE) *
        ∑ s ∈ range (2 ^ v.y.ls), eqN v.y.ls 0 (fun j => pt ρ r (g + j)) s *
          ext lT (fun p => val t A (lamOf (x / blocks)) ((first + x % blocks) * 2 ^ v.y.ls + s) p)
            (fun j => pt ρ r (g + v.y.ls + j)) := by
    refine sumForms_value ρ W _ _ _ ?_ h
    intro x b k hx
    obtain ⟨a', ha, ek⟩ := Option.map_eq_some_iff.mp hx
    cases ek
    have hl := long_true hρ T R hS2 (i := lamOf (x / blocks)) (fun l => wh _ l)
      (jh := first + x % blocks) ha
    rw [hl]
    simp only [hraw]
  rw [h1]
  refine sum_congr rfl fun x hx => ?_
  rw [mul_sum]
  refine sum_congr rfl fun s hs => ?_
  rw [Hd.squares_weight ρ he (low := fun j => pt ρ r (g + j)) (fun j _ => rfl)
    (hidx x (mem_range.mp hx)) (mem_range.mp hs)]
  ring

/-- The extension over (Y | i), with Y cut into a block x and a feature s of the block. -/
theorem ext_blocks (g ls lT : ℕ) (V p : ℕ → K) :
    ext (g + ls + lT) V p = ∑ x ∈ range (2 ^ g), ∑ s ∈ range (2 ^ ls),
      eqN (g + ls) 0 p (x * 2 ^ ls + s) *
        ext lT (fun i => V ((x * 2 ^ ls + s) * 2 ^ lT + i)) (fun j => p (g + ls + j)) := by
  rw [ext_nest (g + ls) lT]
  unfold Blocks.ext
  rw [pow_add, Alg.sum_range_mul_add]

/-- A number (Y | i), cut. -/
theorem cut_two (n Y i : ℕ) (hi : i < 2 ^ n) :
    (Y * 2 ^ n + i) / 2 ^ n = Y ∧ (Y * 2 ^ n + i) % 2 ^ n = i := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hi,
      Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- One end claim's sum is worth the negative of the extension of a map V at the layer's point, if V
at (Y | i) is the negative of the library's value at layer lamOf (Y / 2^m), feature
first 2^ls + Y mod 2^m, position i. a: the bits of the rows; m: those of a row's features. -/
theorem out_core (hρ : Numerals ρ) (hS2 : v.y.S2 = 2 ^ v.y.ls) {A : Arr} (hoff : A.off = 0)
    {X : Ten} (T : Tied c t A X.mat X.place) (wh : ∀ i l, v.y.S2 ∣ tenCell X.place l i 0)
    {r : Array E} {a m lT tb : ℕ} (hm : v.y.ls ≤ m)
    (R : LongTrue ρ W v tb X.mat v.y.ls lT c (fun j => pt ρ r (a + m - v.y.ls + j))
      (fun j => pt ρ r (a + m - v.y.ls + v.y.ls + j)))
    {la : ℕ} {e : Array E} (he : hiTab r la (a + m - v.y.ls) = .ok e) {first : ℕ}
    {lamOf : ℕ → ℕ} {V : ℕ → K}
    (hV : ∀ Y i, i < 2 ^ lT → V (Y * 2 ^ lT + i) =
      -val t A (lamOf (Y / 2 ^ m)) (first * 2 ^ v.y.ls + Y % 2 ^ m) i)
    {aX : Aff}
    (h : endForm v tb X e (2 ^ a) (2 ^ (m - v.y.ls)) (2 ^ (m - v.y.ls)) lamOf first = some aX) :
    aX.value ρ W = -ext (a + m - v.y.ls + v.y.ls + lT) V (pt ρ r) := by
  have hpow : 2 ^ a * 2 ^ (m - v.y.ls) = 2 ^ (a + m - v.y.ls) := by
    rw [← pow_add]
    congr 1
    omega
  have hv := endForm_value hρ hS2 hoff T wh R he
    (fun x hx => by rw [Nat.div_add_mod']; rw [hpow] at hx; exact hx) h
  rw [hv, ext_blocks, hpow, ← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun s hs => ?_
  rw [Nat.div_add_mod']
  obtain ⟨e1, e2⟩ := cut_two v.y.ls x s (mem_range.mp hs)
  obtain ⟨i1, i2⟩ := idx_blocks v.y.ls m (x * 2 ^ v.y.ls + s) first hm
  rw [e1] at i1 i2
  rw [e2] at i2
  have hx : ext lT (fun i => V ((x * 2 ^ v.y.ls + s) * 2 ^ lT + i))
      (fun j => pt ρ r (a + m - v.y.ls + v.y.ls + j)) =
      -ext lT (fun p => val t A (lamOf (x / 2 ^ (m - v.y.ls)))
        ((first + x % 2 ^ (m - v.y.ls)) * 2 ^ v.y.ls + s) p)
        (fun j => pt ρ r (a + m - v.y.ls + v.y.ls + j)) := by
    rw [← ext_neg]
    refine Blocks.ext_congr (fun i hi => ?_) _
    rw [hV _ _ hi, i1, i2]
  rw [hx]
  ring

theorem gatedFirstOut : GatedFirstOut := by
  intro K _ ρ W v D c t o tb ts tu e aS aU G hla hls hLam hf hPf he hS hU
  have hw : v.y.h.ll + v.y.lPf - v.y.ls = D.lL + lF D - v.y.ls := by
    obtain ⟨_, h2, -⟩ := Hd.hiTab_ok he
    rw [G.size, hla] at h2
    omega
  rw [hw] at he
  rw [hLam, hf, hPf, G.S2, Nat.pow_div hls (by norm_num)] at hS hU
  have hn : D.lL + lF D + D.lT = D.lL + lF D - v.y.ls + v.y.ls + D.lT := by omega
  have hVs : ∀ Y i, i < 2 ^ D.lT → slV D t (Y * 2 ^ D.lT + i) =
      -val t .sl (id (Y / 2 ^ lF D)) (0 * 2 ^ v.y.ls + Y % 2 ^ lF D) i := by
    intro Y i hi
    obtain ⟨d1, d2⟩ := cut_two D.lT Y i hi
    show -val t .sl ((Y * 2 ^ D.lT + i) / 2 ^ D.lT / 2 ^ lF D)
      ((Y * 2 ^ D.lT + i) / 2 ^ D.lT % 2 ^ lF D) ((Y * 2 ^ D.lT + i) % 2 ^ D.lT) = _
    rw [d1, d2, Nat.zero_mul, Nat.zero_add]
    rfl
  have hVu : ∀ Y i, i < 2 ^ D.lT → upV D t (Y * 2 ^ D.lT + i) =
      -val t .up (id (Y / 2 ^ lF D)) (0 * 2 ^ v.y.ls + Y % 2 ^ lF D) i := by
    intro Y i hi
    obtain ⟨d1, d2⟩ := cut_two D.lT Y i hi
    show -val t .up ((Y * 2 ^ D.lT + i) / 2 ^ D.lT / 2 ^ lF D)
      ((Y * 2 ^ D.lT + i) / 2 ^ D.lT % 2 ^ lF D) ((Y * 2 ^ D.lT + i) % 2 ^ D.lT) = _
    rw [d1, d2, Nat.zero_mul, Nat.zero_add]
    rfl
  constructor
  · rw [Aff.value_add, Aff.value_slot,
      out_core G.num G.S2 rfl G.tiedS G.wholeS hls G.trueS he hVs hS, hn]
    ring
  · rw [Aff.value_add, Aff.value_slot,
      out_core G.num G.S2 rfl G.tiedU G.wholeU hls G.trueU he hVu hU, hn]
    ring

theorem gatedSecondOut : GatedSecondOut := by
  intro K _ ρ W v D c t o tb ts tu e aS aU G hla hls hLamM hfe hDfe he hS hU
  have hw : v.y.h.ll - 1 + v.y.lfe - v.y.ls = D.lL - 1 + lFe D - v.y.ls := by
    obtain ⟨_, h2, -⟩ := Hd.hiTab_ok he
    rw [G.size, hla] at h2
    omega
  rw [hw] at he
  rw [hLamM, hfe, G.S2, Nat.pow_div hls (by norm_num)] at hS hU
  have hn : D.lL - 1 + lFe D + D.lT = D.lL - 1 + lFe D - v.y.ls + v.y.ls + D.lT := by omega
  have hfe2 : 2 ^ (lFe D - v.y.ls) * 2 ^ v.y.ls = D.fe := by
    rw [hDfe, ← pow_add]
    congr 1
    omega
  have hVs : ∀ Y i, i < 2 ^ D.lT → slV' D t (Y * 2 ^ D.lT + i) =
      -val t .sl ((fun lm => 2 * lm + 1) (Y / 2 ^ lFe D))
        (2 ^ (lFe D - v.y.ls) * 2 ^ v.y.ls + Y % 2 ^ lFe D) i := by
    intro Y i hi
    obtain ⟨d1, d2⟩ := cut_two D.lT Y i hi
    show -val t .sl (2 * ((Y * 2 ^ D.lT + i) / 2 ^ D.lT / 2 ^ lFe D) + 1)
      (D.fe + (Y * 2 ^ D.lT + i) / 2 ^ D.lT % 2 ^ lFe D) ((Y * 2 ^ D.lT + i) % 2 ^ D.lT) = _
    rw [d1, d2, hfe2]
  have hVu : ∀ Y i, i < 2 ^ D.lT → upV' D t (Y * 2 ^ D.lT + i) =
      -val t .up ((fun lm => 2 * lm + 1) (Y / 2 ^ lFe D))
        (2 ^ (lFe D - v.y.ls) * 2 ^ v.y.ls + Y % 2 ^ lFe D) i := by
    intro Y i hi
    obtain ⟨d1, d2⟩ := cut_two D.lT Y i hi
    show -val t .up (2 * ((Y * 2 ^ D.lT + i) / 2 ^ D.lT / 2 ^ lFe D) + 1)
      (D.fe + (Y * 2 ^ D.lT + i) / 2 ^ D.lT % 2 ^ lFe D) ((Y * 2 ^ D.lT + i) % 2 ^ D.lT) = _
    rw [d1, d2, hfe2]
  constructor
  · rw [Aff.value_add, Aff.value_slot,
      out_core G.num G.S2 rfl G.tiedS G.wholeS hls G.trueS he hVs hS, hn]
    ring
  · rw [Aff.value_add, Aff.value_slot,
      out_core G.num G.S2 rfl G.tiedU G.wholeU hls G.trueU he hVu hU, hn]
    ring

#print axioms gatedFirstOut
#print axioms gatedSecondOut

end OnBytes.Road.Rows

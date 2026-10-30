-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Rows/GatedStartsProofs.lean: the starts of the two product layers of the gated
products: proofs of two statements of Johnson/Road/Rows/GatedEnds.lean.

  `gatedFirstIn` : GatedFirstIn: the sum on which the first layer runs, at the point from which it
      is started, is the extension of the honest never-sent vector 0 at the panel's coordinates.
  `gatedSecondIn` : GatedSecondIn: the second layer's start form, less the sum on which it runs, is
      the combination, under the fresh point's weights, of "hidden value less honest vector".
  `gatedFirstEnd`, `gatedSecondEnd`: with Johnson/Road/Rows/GatedEndsProofs.lean: both records.

Limits. Identities: no draw, no soundness, nothing from the field to the integers.
-/
import Johnson.Road.Rows.GatedEndsProofs
import Johnson.Road.Rows.AttEnds14Below
import Johnson.Road.FormsKeysIdnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Level tenCell eqTab hiTab)
open OnBytes.Model.Layer (Env Ten SBlk sumForms downFrom aff0)
open Inst.Model.FFSeg (Dim Cell Arr val hh hhU Hh1t slV upV slV' upV' lF lFe)
open Blocks (ext eqN)
open Cb.Pv.Lay.End.Gated (ext_nest ext_neg idx_blocks)

variable {K : Type} [Field K]

/-- The kernel reads the m coordinates from off on alone. -/
theorem eqN_same (m off : ℕ) {a a' : ℕ → K} (h : ∀ j, j < m → a (off + j) = a' (off + j))
    (z : ℕ) : eqN m off a z = eqN m off a' z := by
  unfold Blocks.eqN
  exact prod_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

theorem downFrom_size (rs : Array E) {n : ℕ} (h : n ≤ rs.size) : (downFrom rs n).size = n := by
  unfold downFrom
  rw [rev_size rs h, Nat.sub_zero]

/-- The library's kernel at the coordinates n - 1 down to 0 is eqR over the bits 0 to n - 1. -/
theorem eqN_down (ρ : Reading K) (rs : Array E) {n : ℕ} (h : n ≤ rs.size) {p : ℕ → K} {off : ℕ}
    (hp : ∀ j, j < n → p (off + j) = pt ρ (downFrom rs n) j) (c : ℕ) :
    eqN n off p c = eqR ρ rs 0 n c := by
  unfold eqR
  rw [Nat.sub_zero, Cb.Pv.Lay.End.eqN_off]
  refine eqN_same n 0 (fun j hj => ?_) c
  rw [Nat.zero_add, hp j hj]
  unfold pt downFrom
  rw [rev_getD rs h (by omega)]

theorem gatedFirstIn : GatedFirstIn := by
  intro K _ ρ D t rs ztF b u' hwy hw hle
  have hsz := downFrom_size rs hle
  have p1 : ∀ j, j < b.w → pt ρ (downFrom rs b.w ++ ztF) (0 + j) = pt ρ (downFrom rs b.w) j := by
    intro j hj
    rw [Nat.zero_add, pt_append, if_pos (by rw [hsz]; exact hj)]
  have p2 : (fun j => pt ρ (downFrom rs b.w ++ ztF) (b.w + j)) = pt ρ ztF := by
    funext j
    rw [pt_append, if_neg (by rw [hsz]; omega), hsz, Nat.add_sub_cancel_left]
  have inner : (fun Y => ext D.lT
      (fun i => slV D t (Y * 2 ^ D.lT + i) * upV D t (Y * 2 ^ D.lT + i))
      (fun j => pt ρ (downFrom rs b.w ++ ztF) (b.w + j))) = fun Y => Hh1t D t (pt ρ ztF) Y := by
    funext Y
    rw [p2]
    unfold Hh1t hhU
    refine Blocks.ext_congr (fun i hi => ?_) _
    obtain ⟨d1, d2⟩ := cut_two D.lT Y i hi
    show (-val t .sl ((Y * 2 ^ D.lT + i) / 2 ^ D.lT / 2 ^ lF D)
        ((Y * 2 ^ D.lT + i) / 2 ^ D.lT % 2 ^ lF D) ((Y * 2 ^ D.lT + i) % 2 ^ D.lT)) *
      (-val t .up ((Y * 2 ^ D.lT + i) / 2 ^ D.lT / 2 ^ lF D)
        ((Y * 2 ^ D.lT + i) / 2 ^ D.lT % 2 ^ lF D) ((Y * 2 ^ D.lT + i) % 2 ^ D.lT)) = _
    rw [d1, d2]
    unfold hh
    ring
  rw [← hw, ext_nest b.w D.lT, inner]
  unfold Blocks.ext gsum
  have hwle : b.wy ≤ b.w := by omega
  have e : 2 ^ b.w = 2 ^ (b.w - b.wy) * 2 ^ b.wy := by
    rw [← pow_add]
    congr 1
    omega
  rw [e, Alg.sum_range_mul_add]
  refine sum_congr rfl fun i _ => sum_congr rfl fun yv hyv => ?_
  rw [eqN_down ρ rs hle p1]
  have s := eqR_split ρ rs (Nat.zero_le b.wy) hwle i (c' := yv)
    (by rw [Nat.sub_zero]; exact mem_range.mp hyv)
  rw [Nat.sub_zero] at s
  rw [s]
  rfl

#print axioms gatedFirstIn

/-- The start form of the second product layer is worth the routed layers' hidden values under the
equality weights of the fresh point. -/
theorem start2_value (ρ : Reading K) (W : World K) (LamM sH1 : ℕ) (rhoM : Array E) :
    (start2 LamM sH1 rhoM).value ρ W =
      ∑ lm ∈ range LamM, ρ.val ((eqTab rhoM).getD lm zeroE) * W.slot (sH1 + 1 + lm) := by
  unfold start2
  rw [foldAdds_value ρ W _
      (fun lm => ρ.val ((eqTab rhoM).getD lm zeroE) * W.slot (sH1 + 1 + lm))
      (fun a i => by rw [Aff.value_addMul, Aff.value_slot]),
    aff0_value, zero_add, list_range_sum]

theorem gatedSecondIn : GatedSecondIn := by
  intro K _ ρ W D t rs rt rhoM u sH1 LamM lfe hlfe hle hrho hLam
  subst hlfe
  have hsz := downFrom_size rs hle
  have hsz2 : (rhoM ++ downFrom rs (lFe D)).size = D.lL - 1 + lFe D := by
    rw [Array.size_append, hrho, hsz]
  -- the three stretches of the point
  have q1 : ∀ j, j < D.lL - 1 →
      pt ρ (rhoM ++ downFrom rs (lFe D) ++ rt) (0 + j) = pt ρ rhoM (0 + j) := by
    intro j hj
    rw [Nat.zero_add, pt_append, if_pos (by rw [hsz2]; omega), pt_append,
      if_pos (by rw [hrho]; exact hj)]
  have q2 : ∀ j, j < lFe D → pt ρ (rhoM ++ downFrom rs (lFe D) ++ rt) (D.lL - 1 + j) =
      pt ρ (downFrom rs (lFe D)) j := by
    intro j hj
    rw [pt_append, if_pos (by rw [hsz2]; omega), pt_append, if_neg (by rw [hrho]; omega), hrho,
      Nat.add_sub_cancel_left]
  have q3 : (fun j => pt ρ (rhoM ++ downFrom rs (lFe D) ++ rt) (D.lL - 1 + lFe D + j)) =
      pt ρ rt := by
    funext j
    rw [pt_append, if_neg (by rw [hsz2]; omega), hsz2, Nat.add_sub_cancel_left]
  have inner : (fun Y => ext D.lT
      (fun i => slV' D t (Y * 2 ^ D.lT + i) * upV' D t (Y * 2 ^ D.lT + i))
      (fun j => pt ρ (rhoM ++ downFrom rs (lFe D) ++ rt) (D.lL - 1 + lFe D + j))) =
      fun Y => hhU D t (2 * (Y / 2 ^ lFe D) + 1) (D.fe + Y % 2 ^ lFe D) (pt ρ rt) := by
    funext Y
    rw [q3]
    unfold hhU
    refine Blocks.ext_congr (fun i hi => ?_) _
    obtain ⟨d1, d2⟩ := cut_two D.lT Y i hi
    show (-val t .sl (2 * ((Y * 2 ^ D.lT + i) / 2 ^ D.lT / 2 ^ lFe D) + 1)
        (D.fe + (Y * 2 ^ D.lT + i) / 2 ^ D.lT % 2 ^ lFe D) ((Y * 2 ^ D.lT + i) % 2 ^ D.lT)) *
      (-val t .up (2 * ((Y * 2 ^ D.lT + i) / 2 ^ D.lT / 2 ^ lFe D) + 1)
        (D.fe + (Y * 2 ^ D.lT + i) / 2 ^ D.lT % 2 ^ lFe D) ((Y * 2 ^ D.lT + i) % 2 ^ D.lT)) = _
    rw [d1, d2]
    unfold hh
    ring
  rw [start2_value, ext_nest (D.lL - 1 + lFe D) D.lT, inner, Blocks.ext_two, hLam,
    ← sum_sub_distrib]
  refine sum_congr rfl fun lm hlm => ?_
  have hlm' := mem_range.mp hlm
  rw [eqTab_value ρ rhoM lm (by rw [hrho]; exact hlm'), hrho, mul_sub, mul_sum]
  congr 1
  refine sum_congr rfl fun yv hyv => ?_
  obtain ⟨d1, d2⟩ := cut_two (lFe D) lm yv (mem_range.mp hyv)
  rw [eqN_same (D.lL - 1) 0 q1 lm, eqN_down ρ rs hle q2, d1, d2, Nat.add_comm 1 lm]
  show _ = eqN (D.lL - 1) 0 (pt ρ rhoM) lm *
    (eqR ρ rs 0 (lFe D) yv * hhU D t (2 * lm + 1) (D.fe + yv) (pt ρ rt))
  ring

#print axioms gatedSecondIn

/-- The two ends of each product layer of the gated products. -/
theorem gatedFirstEnd : GatedFirstEnd := ⟨gatedFirstOut, gatedFirstIn⟩

theorem gatedSecondEnd : GatedSecondEnd := ⟨gatedSecondOut, gatedSecondIn⟩

end OnBytes.Road.Rows

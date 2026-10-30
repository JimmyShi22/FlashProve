-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/Turned.lean: the vectors of the identities at1 and at2 of an attention segment,
on cubes whose parts stand in the order in which the programs draw the point.

Cb/Pv/Att/Mean/Means.lean and Land.lean write the sums of two sumchecks as extensions of
vectors of identities over the cubes (i | g) and (i | g | k), the order of the sumchecks' variables.
The point at which these extensions are taken is drawn in one message, in the order (tg, ti) and
(tk, tbg, tbi). This file has the same vectors on the cubes (g | i) and (k | g | i) and shows that
their extensions at the points (tg | ti) and (tk | tbg | tbi) are the same elements.

Main definitions: scoreIdnG, bitIdnT.
Main theorems.
 - ext3_sum: the extension of an array on three indices, at a point in three parts, as a triple sum.
 - score_turn, bits_turn: the extensions in the two orders agree.
 - scoreMeanG, bitSum_meanT: ScoreMean and bitSum_mean in the order of the draws.
 - at2_of_cubeG, at1_of_cubeT: if the vectors are 0 on the cubes, the identities are 0 at every
   valid index.

All of it is algebra on the library's definitions. Nothing is said about a verifier.


-/
import Cb.Pv.Att.Mean.Land
import Cb.Pv.Att.Mean.KeyMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E]

/-- The extension of an array on three indices, at a point in three parts. -/
theorem ext3_sum (a b c : ℕ) (u v w : ℕ → E) (f : ℕ → ℕ → ℕ → E) :
    Blocks.ext (a + b + c) (fun X => f (X / 2 ^ c / 2 ^ b) (X / 2 ^ c % 2 ^ b) (X % 2 ^ c))
        (cat a u (cat b v w)) =
      ∑ x ∈ range (2 ^ a), ∑ y ∈ range (2 ^ b), ∑ z ∈ range (2 ^ c),
        eqN a 0 u x * eqN b 0 v y * eqN c 0 w z * f x y z := by
  rw [ext_three]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y hy => sum_congr rfl fun z hz => ?_
  have e1 := Dim.div_step (a := x * 2 ^ b + y) (Nat.two_pow_pos c) (mem_range.mp hz)
  have e2 := Dim.div_step (a := x) (Nat.two_pow_pos b) (mem_range.mp hy)
  have a1 : eqN a 0 (cat a u (cat b v w)) x = eqN a 0 u x :=
    eqN_agree (fun k hk => by simp only [cat, Nat.zero_add, if_pos hk]) x
  have a2 : eqN b 0 (sh (cat a u (cat b v w)) a) y = eqN b 0 v y :=
    eqN_agree (fun k hk => by
      show cat a u (cat b v w) (a + (0 + k)) = v (0 + k)
      have n1 : ¬ a + k < a := by omega
      have n2 : a + k - a = k := by omega
      simp only [cat, Nat.zero_add, if_neg n1, n2, if_pos hk]) y
  have a3 : eqN c 0 (sh (cat a u (cat b v w)) (a + b)) z = eqN c 0 w z :=
    eqN_agree (fun k _ => by
      show cat a u (cat b v w) (a + b + (0 + k)) = w (0 + k)
      have n1 : ¬ a + b + k < a := by omega
      have n2 : a + b + k - a = b + k := by omega
      have n3 : ¬ b + k < b := by omega
      have n4 : b + k - b = k := by omega
      simp only [cat, Nat.zero_add, if_neg n1, n2, if_neg n3, n4]) z
  simp only [e1.1, e1.2, e2.1, e2.2, a1, a2, a3]

variable (D : Dim) (t : Raw → E)

/-! ## The identities at2 -/

/-- The identities at2 of pair b, on the cube (g | i). -/
def scoreIdnG (b Y : ℕ) : E := idnVal D t (.at2 b (Y / D.T) (Y % D.T))

/-- **The two orders of the cube of the identities at2.** -/
theorem score_turn (b : ℕ) (vi vg : ℕ → E) :
    Blocks.ext (D.lT + D.lg) (scoreIdn D t b) (cat D.lT vi vg) =
      Blocks.ext (D.lg + D.lT) (scoreIdnG D t b) (cat D.lg vg vi) := by
  have e1 := rd2_ext D vg vi fun g i => idnVal D t (.at2 b g i)
  have e2 := gi_rd2 D (fun g i => idnVal D t (.at2 b g i)) (cat D.lg vg vi)
  have e3 := rd2_agree D (vg := cat D.lg vg vi) (vg' := vg) (vi := sh (cat D.lg vg vi) D.lg)
    (vi' := vi) (fun k hk => by simp only [cat, if_pos hk])
    (fun k _ => by
      show cat D.lg vg vi (D.lg + k) = vi k
      have n1 : ¬ D.lg + k < D.lg := by omega
      have n2 : D.lg + k - D.lg = k := by omega
      simp only [cat, if_neg n1, n2]) fun g i => idnVal D t (.at2 b g i)
  exact e1.symm.trans (e3.symm.trans e2.symm)

/-- **ScoreMean in the order of the draws.** -/
theorem scoreMeanG (C : Calls) (p : Pub E) :
    (∑ b ∈ range D.nb, p.o b * rvM6 D p t b) - sumPhi D C p t .s16 =
      ∑ b ∈ range D.nb, p.o b *
        Blocks.ext (D.lg + D.lT) (scoreIdnG D t b) (cat D.lg p.tg p.ti) := by
  rw [scoreMean E D C p t]
  exact sum_congr rfl fun b _ => by rw [score_turn]

/-- **If the identities at2 are 0 on the cube (g | i), they are 0 at every valid index.** -/
theorem at2_of_cubeG (h : ∀ b < D.nb, ∀ Y < 2 ^ (D.lg + D.lT), scoreIdnG D t b Y = 0)
    (b g i : ℕ) (hv : Idn.Valid D (.at2 b g i)) : idnVal D t (.at2 b g i) = 0 := by
  obtain ⟨hb, hg, hi⟩ := hv
  have hg' : g < 2 ^ D.lg := hg
  have hi' : i < 2 ^ D.lT := by
    rw [← D.T_eq]
    exact hi
  have e := Dim.div_step (a := g) (Nat.two_pow_pos D.lT) hi'
  have hY : g * 2 ^ D.lT + i < 2 ^ (D.lg + D.lT) := by
    rw [pow_add]
    calc g * 2 ^ D.lT + i < g * 2 ^ D.lT + 2 ^ D.lT := by omega
      _ = (g + 1) * 2 ^ D.lT := by ring
      _ ≤ 2 ^ D.lg * 2 ^ D.lT := Nat.mul_le_mul_right _ hg'
  have h0 := h b hb _ hY
  unfold scoreIdnG at h0
  rw [D.T_eq, e.1, e.2] at h0
  exact h0

/-! ## The identities at1 -/

/-- The identities at1 of pair b as an array on (k, g, i); 0 where k is not the number of a bit of a
position. -/
def bitArr (b k g i : ℕ) : E := if k < D.lT then idnVal D t (.at1 k b g i) else 0

/-- The identities at1 of pair b, on the cube (k | g | i) with kap bits for k. -/
def bitIdnT (b X : ℕ) : E :=
  bitArr D t b (X / 2 ^ D.lT / 2 ^ D.lg) (X / 2 ^ D.lT % 2 ^ D.lg) (X % 2 ^ D.lT)

/-- **The two orders of the cube of the identities at1.** -/
theorem bits_turn (kap b : ℕ) (vi vg vk : ℕ → E) :
    Blocks.ext (D.lT + D.lg + kap) (bitIdnK kap D t b) (cat D.lT vi (cat D.lg vg vk)) =
      Blocks.ext (kap + D.lg + D.lT) (bitIdnT D t b) (cat kap vk (cat D.lg vg vi)) := by
  have e1 := ext3_sum D.lT D.lg kap vi vg vk fun i g k => bitArr D t b k g i
  have e2 := ext3_sum kap D.lg D.lT vk vg vi fun k g i => bitArr D t b k g i
  have l : bitIdnK kap D t b = fun X =>
      (fun i g k => bitArr D t b k g i) (X / 2 ^ kap / 2 ^ D.lg) (X / 2 ^ kap % 2 ^ D.lg)
        (X % 2 ^ kap) := rfl
  have r : bitIdnT D t b = fun X =>
      (fun k g i => bitArr D t b k g i) (X / 2 ^ D.lT / 2 ^ D.lg) (X / 2 ^ D.lT % 2 ^ D.lg)
        (X % 2 ^ D.lT) := rfl
  rw [l, r, e1, e2]
  calc ∑ i ∈ range (2 ^ D.lT), ∑ g ∈ range (2 ^ D.lg), ∑ k ∈ range (2 ^ kap),
        eqN D.lT 0 vi i * eqN D.lg 0 vg g * eqN kap 0 vk k * bitArr D t b k g i
      = ∑ i ∈ range (2 ^ D.lT), ∑ k ∈ range (2 ^ kap), ∑ g ∈ range (2 ^ D.lg),
        eqN D.lT 0 vi i * eqN D.lg 0 vg g * eqN kap 0 vk k * bitArr D t b k g i :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ k ∈ range (2 ^ kap), ∑ i ∈ range (2 ^ D.lT), ∑ g ∈ range (2 ^ D.lg),
        eqN D.lT 0 vi i * eqN D.lg 0 vg g * eqN kap 0 vk k * bitArr D t b k g i := sum_comm
    _ = ∑ k ∈ range (2 ^ kap), ∑ g ∈ range (2 ^ D.lg), ∑ i ∈ range (2 ^ D.lT),
        eqN D.lT 0 vi i * eqN D.lg 0 vg g * eqN kap 0 vk k * bitArr D t b k g i :=
        sum_congr rfl fun _ _ => sum_comm
    _ = _ := sum_congr rfl fun k _ => sum_congr rfl fun g _ => sum_congr rfl fun i _ => by ring

/-- **bitSum_mean in the order of the draws.** -/
theorem bitSum_meanT (kap : ℕ) (p : Pub E) :
    bitSum kap D p t =
      ∑ b ∈ range D.nb, p.o'' b *
        Blocks.ext (kap + D.lg + D.lT) (bitIdnT D t b) (cat kap p.tk (cat D.lg p.tbg p.tbi)) := by
  rw [bitSum_mean]
  exact sum_congr rfl fun b _ => by rw [bits_turn]

/-- **If the identities at1 are 0 on the cube (k | g | i), they are 0 at every valid index.** -/
theorem at1_of_cubeT (kap : ℕ) (hK : D.lT ≤ 2 ^ kap)
    (h : ∀ b < D.nb, ∀ X < 2 ^ (kap + D.lg + D.lT), bitIdnT D t b X = 0) (k b g i : ℕ)
    (hv : Idn.Valid D (.at1 k b g i)) : idnVal D t (.at1 k b g i) = 0 := by
  obtain ⟨hk, hb, hg, hi⟩ := hv
  have hg' : g < 2 ^ D.lg := hg
  have hi' : i < 2 ^ D.lT := by
    rw [← D.T_eq]
    exact hi
  have hk' : k < 2 ^ kap := Nat.lt_of_lt_of_le hk hK
  have e1 := Dim.div_step (a := k * 2 ^ D.lg + g) (Nat.two_pow_pos D.lT) hi'
  have e2 := Dim.div_step (a := k) (Nat.two_pow_pos D.lg) hg'
  have hX : (k * 2 ^ D.lg + g) * 2 ^ D.lT + i < 2 ^ (kap + D.lg + D.lT) := by
    rw [pow_add, pow_add]
    calc (k * 2 ^ D.lg + g) * 2 ^ D.lT + i < (k * 2 ^ D.lg + g) * 2 ^ D.lT + 2 ^ D.lT := by omega
      _ = (k * 2 ^ D.lg + g + 1) * 2 ^ D.lT := by ring
      _ ≤ ((k + 1) * 2 ^ D.lg) * 2 ^ D.lT :=
        Nat.mul_le_mul_right _ (by
          have : (k + 1) * 2 ^ D.lg = k * 2 ^ D.lg + 2 ^ D.lg := by ring
          omega)
      _ ≤ (2 ^ kap * 2 ^ D.lg) * 2 ^ D.lT :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk')
  have h0 := h b hb _ hX
  unfold bitIdnT bitArr at h0
  rw [e1.1, e1.2, e2.1, e2.2, if_pos hk] at h0
  exact h0

end Cb.Pv.Att

#print axioms Cb.Pv.Att.scoreMeanG
#print axioms Cb.Pv.Att.bitSum_meanT
#print axioms Cb.Pv.Att.at2_of_cubeG
#print axioms Cb.Pv.Att.at1_of_cubeT

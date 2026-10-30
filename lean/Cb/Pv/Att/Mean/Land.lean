-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/Land.lean: from the sums of the sumchecks for the bits and for the score at
the index to the identities of the library's relation of an attention segment.

The library's relation on the cells of an attention segment (RFraw in Inst/Model/Att/Trace.lean)
asks that the identities at1 (a cell of the index is a bit) and at2 (the row maximum is the score at
the index) are 0 at every valid index. Cb/Pv/Att/Mean/Means.lean writes the sums of the two
sumchecks as extensions of vectors of these identities over a cube. This file has the sum of the
sumcheck for the bits (bitSum in Cb/Pv/Att/Bits.lean) for any number kap of bits that number a bit
(the verifier takes 4), and it
shows that a vector over the cube that is 0 everywhere gives the identities at every valid index.

Main definitions: bitIdnK.
Main theorems.
 - bitSum_mean: the sum of the sumcheck for the bits, with kap bits, is the batch of the extensions
   of the identities at1 at the drawn point. bitSum_lK, bitIdnK_lK: with the library's number of
   bits the sum is the library's, and the vector is bitIdn.
 - at1_of_cube, at2_of_cube: if the vectors are 0 on the cube, the identities are 0 at every valid
   index.

What this file does not claim. That an extension which is 0 at a drawn point comes from a vector
that is 0 on the cube holds only up to an error, which is not counted here (the library counts it:
Blocks.cnt_ext_zero_le). Nothing is said about a verifier, a proof or hiding.


-/
import Cb.Pv.Att.Mean.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E]

/-- The identities at1 of pair b, on the cube (i | g | k) with kap bits for k; 0 where k is not the
number of a bit of a position. -/
def bitIdnK (kap : ℕ) (D : Dim) (t : Raw → E) (b X : ℕ) : E :=
  if X % 2 ^ kap < D.lT then
    idnVal D t (.at1 (X % 2 ^ kap) b (X / 2 ^ kap % D.nG) (X / 2 ^ kap / D.nG))
  else 0

/-- With the library's number of bits the vector is bitIdn of Cb/Pv/Att/Mean/Means.lean. -/
theorem bitIdnK_lK (D : Dim) (t : Raw → E) (b : ℕ) : bitIdnK D.lK D t b = bitIdn D t b := rfl

/-- With the library's number of bits the sum is the library's. -/
theorem bitSum_lK (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E) :
    bitSum D.lK D p t = sumPhi D C p t .s21 :=
  (sumPhi_cube D C p t .s21).symm

/-- **The sum of the sumcheck for the bits is the batch of the identities at1 at the drawn
point.** -/
theorem bitSum_mean (kap : ℕ) (D : Dim) (p : Pub E) (t : Raw → E) :
    bitSum kap D p t =
      ∑ b ∈ range D.nb, p.o'' b *
        Blocks.ext (D.lT + D.lg + kap) (bitIdnK kap D t b)
          (cat D.lT p.tbi (cat D.lg p.tbg p.tk)) := by
  unfold bitSum
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  unfold Blocks.ext
  rw [mul_sum]
  refine sum_congr rfl fun X _ => ?_
  have w : bitWt kap D p b (cubePt (D.lT + D.lg + kap) X) =
      p.o'' b * eqN (D.lT + D.lg + kap) 0 (cat D.lT p.tbi (cat D.lg p.tbg p.tk)) X := by
    unfold bitWt
    rw [eqPt_vertex (g := D.lT + D.lg + kap) (n := D.lT) (X := X) (off := 0) (m := D.lg + kap)
        p.tbi (cubePt (D.lT + D.lg + kap) X) (by omega) (fun k _ => by rw [Nat.zero_add]),
      eqPt_vertex (g := D.lT + D.lg + kap) (n := D.lg) (X := X) (off := D.lT) (m := kap) p.tbg
        (sh (cubePt (D.lT + D.lg + kap) X) D.lT) (by omega) (fun _ _ => rfl),
      eqPt_vertex (g := D.lT + D.lg + kap) (n := kap) (X := X) (off := D.lT + D.lg) (m := 0)
        p.tk (sh (cubePt (D.lT + D.lg + kap) X) (D.lT + D.lg)) (by omega) (fun _ _ => rfl),
      Nat.add_assoc, eqN_cat, eqN_cat, pow_zero, Nat.div_one]
    ring
  have k : bitCube kap D t b X * (bitCube kap D t b X - 1) = bitIdnK kap D t b X := by
    show (if X % 2 ^ kap < D.lT then
          ibV t (X % 2 ^ kap) b (X / 2 ^ kap % D.nG) (X / 2 ^ kap / D.nG) else 0) *
        ((if X % 2 ^ kap < D.lT then
          ibV t (X % 2 ^ kap) b (X / 2 ^ kap % D.nG) (X / 2 ^ kap / D.nG) else 0) - 1) =
      if X % 2 ^ kap < D.lT then
        ibV t (X % 2 ^ kap) b (X / 2 ^ kap % D.nG) (X / 2 ^ kap / D.nG) *
          (ibV t (X % 2 ^ kap) b (X / 2 ^ kap % D.nG) (X / 2 ^ kap / D.nG) - 1)
      else 0
    split_ifs <;> ring
  rw [w, mul_assoc, k]
  ring

/-- **If the identities at1 are 0 on the cube, they are 0 at every valid index.** -/
theorem at1_of_cube (kap : ℕ) (D : Dim) (t : Raw → E) (hK : D.lT ≤ 2 ^ kap)
    (h : ∀ b < D.nb, ∀ X < 2 ^ (D.lT + D.lg + kap), bitIdnK kap D t b X = 0) (k b g i : ℕ)
    (hv : Idn.Valid D (.at1 k b g i)) : idnVal D t (.at1 k b g i) = 0 := by
  obtain ⟨hk, hb, hg, hi⟩ := hv
  have hg' : g < 2 ^ D.lg := hg
  have hi' : i < 2 ^ D.lT := by
    rw [← D.T_eq]
    exact hi
  have hk' : k < 2 ^ kap := Nat.lt_of_lt_of_le hk hK
  have e1 := Dim.div_step (a := i * 2 ^ D.lg + g) (Nat.two_pow_pos kap) hk'
  have e2 := Dim.div_step (a := i) (Nat.two_pow_pos D.lg) hg'
  have hX : (i * 2 ^ D.lg + g) * 2 ^ kap + k < 2 ^ (D.lT + D.lg + kap) := by
    rw [pow_add, pow_add]
    calc (i * 2 ^ D.lg + g) * 2 ^ kap + k < (i * 2 ^ D.lg + g) * 2 ^ kap + 2 ^ kap := by omega
      _ = (i * 2 ^ D.lg + g + 1) * 2 ^ kap := by ring
      _ ≤ ((i + 1) * 2 ^ D.lg) * 2 ^ kap :=
        Nat.mul_le_mul_right _ (by
          have : (i + 1) * 2 ^ D.lg = i * 2 ^ D.lg + 2 ^ D.lg := by ring
          omega)
      _ ≤ (2 ^ D.lT * 2 ^ D.lg) * 2 ^ kap :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi')
  have h0 := h b hb _ hX
  unfold bitIdnK at h0
  rw [e1.2, if_pos hk, e1.1] at h0
  have e3 : (i * 2 ^ D.lg + g) % D.nG = g := e2.2
  have e4 : (i * 2 ^ D.lg + g) / D.nG = i := e2.1
  rw [e3, e4] at h0
  exact h0

/-- **If the identities at2 are 0 on the cube, they are 0 at every valid index.** -/
theorem at2_of_cube (D : Dim) (t : Raw → E)
    (h : ∀ b < D.nb, ∀ Y < 2 ^ (D.lT + D.lg), scoreIdn D t b Y = 0) (b g i : ℕ)
    (hv : Idn.Valid D (.at2 b g i)) : idnVal D t (.at2 b g i) = 0 := by
  obtain ⟨hb, hg, hi⟩ := hv
  have hg' : g < 2 ^ D.lg := hg
  have hi' : i < 2 ^ D.lT := by
    rw [← D.T_eq]
    exact hi
  have e2 := Dim.div_step (a := i) (Nat.two_pow_pos D.lg) hg'
  have hY : i * 2 ^ D.lg + g < 2 ^ (D.lT + D.lg) := by
    rw [pow_add]
    calc i * 2 ^ D.lg + g < i * 2 ^ D.lg + 2 ^ D.lg := by omega
      _ = (i + 1) * 2 ^ D.lg := by ring
      _ ≤ 2 ^ D.lT * 2 ^ D.lg := Nat.mul_le_mul_right _ hi'
  have h0 := h b hb _ hY
  unfold scoreIdn at h0
  have e3 : (i * 2 ^ D.lg + g) % D.nG = g := e2.2
  have e4 : (i * 2 ^ D.lg + g) / D.nG = i := e2.1
  rw [e3, e4] at h0
  exact h0

end Cb.Pv.Att

#print axioms Cb.Pv.Att.bitSum_mean
#print axioms Cb.Pv.Att.bitSum_lK
#print axioms Cb.Pv.Att.at1_of_cube
#print axioms Cb.Pv.Att.at2_of_cube

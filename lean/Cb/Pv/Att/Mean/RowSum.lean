-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/RowSum.lean: laws of the library's sum over a row of scores and of its
reads, for the value product of an attention segment.

The library's rowSum (Inst/Model/Att/Trace.lean) is the sum, over the entries of a row of scores, of
the softmax weight times a function G of the key's position. The sum of the weights (EF) and the
accumulator (AC) are values of it. This file shows that rowSum is linear in G, that the library's
read rd2 is linear in its array, and how the lookup's point on a position splits into block and
place.

Main theorems.
 - rowSum_add, rowSum_smul, rowSum_sum, rowSum_lin: rowSum at G j = c + (a contraction over the
   channels) is c times EF plus the contraction of rowSum.
 - rd2_add, rd2_smul, rd2_congr.
 - yi_split: the equality weight of the lookup's point yi at the position B I + i' is that of yI at
   I times that of yi' at i'.
 - atY_rd2: the library's extension atY of an array on (g, i, n) is the read of its contraction over
   the channels.

All of it is algebra on the library's definitions. Nothing is said about a verifier.


-/
import Cb.Pv.Att.Mean.ReadsTiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] (D : Dim)

/-! ## The sum over a row of scores -/

section Row
variable (t : Raw → E) (b g i : ℕ)

theorem rowSum_add (G H : ℕ → E) :
    rowSum D t (fun j => G j + H j) b g i = rowSum D t G b g i + rowSum D t H b g i := by
  unfold rowSum
  have h : ∀ (c : Prop) [Decidable c] (x y : E),
      (if c then x + y else 0) = (if c then x else 0) + (if c then y else 0) := by
    intro c _ x y
    split_ifs <;> simp
  simp only [mul_add, sum_add_distrib, h]
  ring

theorem rowSum_smul (c : E) (G : ℕ → E) :
    rowSum D t (fun j => c * G j) b g i = c * rowSum D t G b g i := by
  unfold rowSum
  have h : ∀ (q : Prop) [Decidable q] (x : E),
      (if q then c * x else 0) = c * (if q then x else 0) := by
    intro q _ x
    split_ifs <;> simp
  have e : ∀ w x : E, w * (c * x) = c * (w * x) := fun w x => by ring
  simp only [e, ← mul_sum, h, ← mul_add]

theorem rowSum_sum (m : ℕ) (G : ℕ → ℕ → E) :
    rowSum D t (fun j => ∑ n ∈ range m, G n j) b g i =
      ∑ n ∈ range m, rowSum D t (G n) b g i := by
  induction m with
  | zero => simp [rowSum]
  | succ m ih =>
    simp only [sum_range_succ]
    rw [rowSum_add, ih]

/-- **rowSum at a constant plus a contraction over the channels.** -/
theorem rowSum_lin (c : E) (v : ℕ → E) (V : ℕ → ℕ → E) :
    rowSum D t (fun j => c + conN D v fun n => V j n) b g i =
      c * EF D t b g i + conN D v fun n => rowSum D t (fun j => V j n) b g i := by
  unfold conN EF
  have e : (fun j => c + ∑ n ∈ range D.ch, eqN D.ln 0 v n * V j n) =
      fun j => c * 1 + ∑ n ∈ range D.ch, eqN D.ln 0 v n * V j n := by
    funext j
    rw [mul_one]
  rw [e, rowSum_add, rowSum_smul, rowSum_sum]
  congr 1
  exact sum_congr rfl fun n _ => rowSum_smul D t b g i _ _

end Row

/-! ## Reads -/

theorem rd2_add (vg Ψ : ℕ → E) (a a' : ℕ → ℕ → E) :
    rd2 D vg Ψ (fun g i => a g i + a' g i) = rd2 D vg Ψ a + rd2 D vg Ψ a' := by
  unfold rd2
  simp only [mul_add, sum_add_distrib]

theorem rd2_smul (vg Ψ : ℕ → E) (c : E) (a : ℕ → ℕ → E) :
    rd2 D vg Ψ (fun g i => c * a g i) = c * rd2 D vg Ψ a := by
  unfold rd2
  simp only [mul_sum]
  exact sum_congr rfl fun g _ => sum_congr rfl fun i _ => by ring

theorem rd2_congr (vg Ψ : ℕ → E) {a a' : ℕ → ℕ → E} (h : ∀ g i, a g i = a' g i) :
    rd2 D vg Ψ a = rd2 D vg Ψ a' :=
  congrArg (rd2 D vg Ψ) (funext fun g => funext fun i => h g i)

variable (C : Calls) (p : Pub E)

/-- **The lookup's point on a position, by block and place.** -/
theorem yi_split (I : ℕ) {i' : ℕ} (h : i' < D.B) :
    eqT D (yi D C p.z) (D.B * I + i') =
      eqN (D.lP + 1) 0 (yI D C p.z) I * eqN D.lB 0 (yi' D C p.z) i' := by
  have ap := eqN_append' (D.lP + 1) D.lB 0 (yi D C p.z) I h
  rw [Nat.mul_comm]
  show eqN (D.lP + 1 + D.lB) 0 (yi D C p.z) (I * 2 ^ D.lB + i') = _
  rw [ap]
  congr 1
  exact eqN_agree (fun k _ => by
    show uW D C p.z (1 + D.lg + (0 + (D.lP + 1) + k)) = uW D C p.z (1 + D.lg + (D.lP + 1) + (0 + k))
    exact congrArg _ (by omega)) i'

/-- **The library's extension of an array on (g, i, n) at the lookup's point is the read of its
contraction over the channels.** -/
theorem atY_rd2 (a : ℕ → ℕ → ℕ → E) :
    atY D C p a =
      rd2 D (yg D C p.z) (eqT D (yi D C p.z)) fun g i => conN D (yn D C p.z) (a g i) := by
  show Blocks.ext (D.lg + D.lT + D.ln)
    (fun X => a (X / D.ch / D.T) (X / D.ch % D.T) (X % D.ch)) (sh (uW D C p.z) 1) = _
  rw [ext_three]
  unfold rd2 eqT conN
  rw [D.T_eq]
  refine sum_congr rfl fun g _ => sum_congr rfl fun i hi => ?_
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have e1 := Dim.div_step (a := g * 2 ^ D.lT + i) (Nat.two_pow_pos D.ln) (mem_range.mp hn)
  have e2 := Dim.div_step (a := g) (Nat.two_pow_pos D.lT) (mem_range.mp hi)
  have a2 : eqN D.lT 0 (sh (sh (uW D C p.z) 1) D.lg) i = eqN D.lT 0 (yi D C p.z) i :=
    eqN_agree (fun k _ => by
      show uW D C p.z (1 + (D.lg + (0 + k))) = uW D C p.z (1 + D.lg + (0 + k))
      exact congrArg _ (by omega)) i
  have a3 : eqN D.ln 0 (sh (sh (uW D C p.z) 1) (D.lg + D.lT)) n = eqN D.ln 0 (yn D C p.z) n :=
    eqN_agree (fun k _ => by
      show uW D C p.z (1 + (D.lg + D.lT + (0 + k))) = uW D C p.z (1 + D.lg + D.lT + (0 + k))
      exact congrArg _ (by omega)) n
  simp only [Dim.ch, e1.1, e1.2, e2.1, e2.2, a2, a3]
  show eqN D.lg 0 (yg D C p.z) g * _ * _ * _ = eqN D.lg 0 (yg D C p.z) g * _ * (_ * _)
  ring

end Cb.Pv.Att

#print axioms Cb.Pv.Att.rowSum_lin
#print axioms Cb.Pv.Att.yi_split
#print axioms Cb.Pv.Att.atY_rd2

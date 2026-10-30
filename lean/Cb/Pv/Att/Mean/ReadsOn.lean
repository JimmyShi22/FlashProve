-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/ReadsOn.lean: the maps of the library's step s12 of an attention segment, written
as reads of arrays.

Step s12 is the value product on the diagonal tiles (Inst/Model/Att/Sums.lean). Its cube is
(head g | block I | place j' in the block).
 - bext12: the second map is th plus the read of the values. Block and place together are a
   position, so the weights on the positions are the equality weights of the point's last part.
 - aext12: the first map is the extension of the softmax weights over the entries (g | I | i' | j')
   of the region of the diagonal tiles, at any point that has the step's point on g, I and j' and
   the lookup's point yi' on i'.

All of it is algebra on the library's definitions, for every content of the cells and all values of
the challenges. Nothing is said about the verifier.


-/
import Cb.Pv.Att.Mean.ReadsTiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E)

/-- The positions are the blocks times the places of a block. -/
theorem pos_pow : 2 ^ (D.lP + 1 + D.lB) = D.B * D.nBlk := by
  rw [pow_add, nBlk_pow]
  exact Nat.mul_comm _ _

/-- **The second map of step s12 is th plus the read of the values.** -/
theorem bext12 (b : ℕ) (ξ : ℕ → E) :
    Bext D C p t .s12 b ξ =
      p.th + rd3 D ξ (eqT D (sh ξ D.lg)) (yn D C p.z) (valV t (D.lamOf b)) := by
  show ext (D.lg + (D.lP + 1) + D.lB)
    (fun X => p.th + conN D (yn D C p.z) fun n =>
      valV t (D.lamOf b) (X / D.B / D.nBlk) (D.B * (X / D.B % D.nBlk) + X % D.B) n) ξ = _
  rw [ext_add, ext_const, Nat.add_assoc, ext_two]
  congr 1
  unfold rd3 eqT conN
  rw [D.T_eq]
  refine sum_congr rfl fun g _ => sum_congr rfl fun j hj => ?_
  have hj' : j < D.B * D.nBlk := by
    rw [← pos_pow]
    exact mem_range.mp hj
  have e := Dim.div_step (a := g) (Nat.mul_pos D.B_pos D.nBlk_pos) hj'
  have e4 : D.B * ((g * (D.B * D.nBlk) + j) / D.B % D.nBlk) + (g * (D.B * D.nBlk) + j) % D.B =
      j := by
    rw [Nat.add_comm, ← Nat.mod_mul, e.2]
  have e5 : (g * (D.B * D.nBlk) + j) / D.B / D.nBlk = g := by
    rw [Nat.div_div_eq_div_mul, e.1]
  simp only [pos_pow, e4, e5]
  rw [eqN_sh, mul_sum]
  exact sum_congr rfl fun n _ => by
    show eqN D.lg 0 ξ g * eqN (D.lP + 1 + D.lB) D.lg ξ j * _ =
      eqN D.lg 0 ξ g * eqN (D.lP + 1 + D.lB) D.lg ξ j * _ * _
    ring

/-- **The first map of step s12 is the extension of the softmax weights on the diagonal tiles.**
zeta: a point on the entries (g | I | i' | j') that has the step's point on g, I and j' and the
lookup's point yi' on i'. -/
theorem aext12 (b : ℕ) (ξ zeta : ℕ → E)
    (h1 : ∀ k < D.lg + (D.lP + 1), zeta k = ξ k)
    (h2 : ∀ k < D.lB, zeta (D.lg + (D.lP + 1) + k) = yi' D C p.z k)
    (h3 : ∀ k < D.lB, zeta (D.lg + (D.lP + 1) + D.lB + k) = ξ (D.lg + (D.lP + 1) + k)) :
    Aext D C p t .s12 b ξ = ext D.lD (wtV t .D b) zeta := by
  show ext (D.lg + (D.lP + 1) + D.lB)
    (fun X => conB D (yi' D C p.z) fun i' =>
      wtV t .D b (D.codeD (X / D.B / D.nBlk) (X / D.B % D.nBlk) i' (X % D.B))) ξ =
    ext (D.lg + (D.lP + 1) + D.lB + D.lB) (wtV t .D b) zeta
  rw [ext_three, ext_four, nBlk_pow]
  refine sum_congr rfl fun g _ => sum_congr rfl fun I hI => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j' hj => ?_
  have a1 : eqN D.lg 0 zeta g = eqN D.lg 0 ξ g :=
    eqN_agree (fun k hk => by rw [Nat.zero_add]; exact h1 k (by omega)) g
  have a2 : eqN (D.lP + 1) 0 (sh zeta D.lg) I = eqN (D.lP + 1) 0 (sh ξ D.lg) I :=
    eqN_agree (fun k hk => by
      show zeta (D.lg + (0 + k)) = ξ (D.lg + (0 + k))
      rw [Nat.zero_add]
      exact h1 _ (by omega)) I
  have a4 : eqN D.lB 0 (sh zeta (D.lg + (D.lP + 1) + D.lB)) j' =
      eqN D.lB 0 (sh ξ (D.lg + (D.lP + 1))) j' :=
    eqN_agree (fun k hk => by
      show zeta (D.lg + (D.lP + 1) + D.lB + (0 + k)) = ξ (D.lg + (D.lP + 1) + (0 + k))
      rw [Nat.zero_add]
      exact h3 k hk) j'
  have e1 := Dim.div_step (a := g * D.nBlk + I) (Nat.two_pow_pos D.lB) (mem_range.mp hj)
  have e2 := Dim.div_step (a := g) D.nBlk_pos (mem_range.mp hI)
  unfold conB
  simp only [Dim.B, e1.1, e1.2, e2.1, e2.2]
  rw [mul_sum]
  refine sum_congr rfl fun i' _ => ?_
  have a3 : eqN D.lB 0 (sh zeta (D.lg + (D.lP + 1))) i' = eqN D.lB 0 (yi' D C p.z) i' :=
    eqN_agree (fun k hk => by
      show zeta (D.lg + (D.lP + 1) + (0 + k)) = yi' D C p.z (0 + k)
      rw [Nat.zero_add]
      exact h2 k hk) i'
  rw [a1, a2, a3, a4]
  show _ * (_ * wtV t .D b (((g * D.nBlk + I) * 2 ^ D.lB + i') * 2 ^ D.lB + j')) = _
  ring

end Cb.Pv.Att

#print axioms Cb.Pv.Att.aext12
#print axioms Cb.Pv.Att.bext12

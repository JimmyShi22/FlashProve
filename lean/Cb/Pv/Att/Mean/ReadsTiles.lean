-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/ReadsTiles.lean: the maps of the steps s6b, s6d, s8 and s11 of an attention segment,
as the library's reads.

Inst/Model/Att/Sums.lean defines the two maps of a pair in each sumcheck of products on the cube
(Acube, Bcube) and extends them (Aext, Bext). The same file defines what a read represents: rd2 and
rd3, sums of an array under an equality vector on the heads, a vector of weights on the positions
and an equality vector on the channels. This file proves that each map of the four steps is such a
read, or, for the softmax weight of step s11, the extension of the array over the entries of the
region at a point that is put together from the step's point and a part of the lookup's.

Main theorems: ext_four, tile_row, tile_col; aext8, bext8; aext6d, bext6d; aext6b, bext6b; aext11,
bext11.

All of it is algebra on the library's definitions, for every content of the cells and all values of
the challenges. Nothing is said about the verifier.


-/
import Cb.Pv.Att.Mean.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E]

/-! ## Tools -/

/-- The extension of a vector with four-part indices, as a fourfold sum. -/
theorem ext_four (a b c d : ℕ) (v ξ : ℕ → E) :
    ext (a + b + c + d) v ξ =
      ∑ x ∈ range (2 ^ a), ∑ y ∈ range (2 ^ b), ∑ z ∈ range (2 ^ c), ∑ w ∈ range (2 ^ d),
        eqN a 0 ξ x * eqN b 0 (sh ξ a) y * eqN c 0 (sh ξ (a + b)) z *
          eqN d 0 (sh ξ (a + b + c)) w * v (((x * 2 ^ b + y) * 2 ^ c + z) * 2 ^ d + w) := by
  have h1 : ext (a + b + c + d) v ξ = ext (a + b + c)
      (fun X => ∑ w ∈ range (2 ^ d), eqN d 0 (sh ξ (a + b + c)) w * v (X * 2 ^ d + w)) ξ := by
    rw [ext_two]
    unfold Blocks.ext
    refine sum_congr rfl fun X _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun w _ => by rw [eqN_sh]; ring
  rw [h1, ext_three]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun w _ => by ring

variable (D : Dim)

/-- The number of blocks of positions is a power of two. -/
theorem nBlk_pow : 2 ^ (D.lP + 1) = D.nBlk := by
  unfold Dim.nBlk Dim.hP
  rw [pow_succ]
  ring

/-- A sum over the blocks under the weights of the row blocks, as a sum over the pairs (P, s). The
last s of a row P stands for no block. -/
theorem tile_row (vP vs : ℕ → E) (H : ℕ → E) :
    ∑ I ∈ range D.nBlk, blkRow D vP vs I * H I =
      ∑ P ∈ range D.hP, ∑ s ∈ range D.nBlk, eqN D.lP 0 vP P * eqN (D.lP + 1) 0 vs s *
        (if s < D.nBlk - 1 then H (D.rowBlk P s) else 0) := by
  have hn : D.nBlk = D.nBlk - 1 + 1 := by have := D.nBlk_pos; omega
  unfold blkRow
  simp only [sum_mul]
  refine Eq.trans sum_comm ?_
  refine sum_congr rfl fun P hP => ?_
  refine Eq.trans sum_comm ?_
  conv_rhs => rw [hn, sum_range_succ]
  have hlast : ¬ D.nBlk - 1 < D.nBlk - 1 + 1 - 1 := by omega
  rw [if_neg hlast, mul_zero, add_zero]
  refine sum_congr rfl fun s hs => ?_
  have hs' : s < D.nBlk - 1 := mem_range.mp hs
  have hlt : s < D.nBlk - 1 + 1 - 1 := by omega
  have hr := (D.blk_of_slot (mem_range.mp hP) hs').2.1
  rw [if_pos hlt]
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq, if_pos (mem_range.mpr hr)]

/-- The same for the column blocks. -/
theorem tile_col (vP vs : ℕ → E) (H : ℕ → E) :
    ∑ J ∈ range D.nBlk, blkCol D vP vs J * H J =
      ∑ P ∈ range D.hP, ∑ s ∈ range D.nBlk, eqN D.lP 0 vP P * eqN (D.lP + 1) 0 vs s *
        (if s < D.nBlk - 1 then H (D.colBlk P s) else 0) := by
  have hn : D.nBlk = D.nBlk - 1 + 1 := by have := D.nBlk_pos; omega
  unfold blkCol
  simp only [sum_mul]
  refine Eq.trans sum_comm ?_
  refine sum_congr rfl fun P hP => ?_
  refine Eq.trans sum_comm ?_
  conv_rhs => rw [hn, sum_range_succ]
  have hlast : ¬ D.nBlk - 1 < D.nBlk - 1 + 1 - 1 := by omega
  rw [if_neg hlast, mul_zero, add_zero]
  refine sum_congr rfl fun s hs => ?_
  have hs' : s < D.nBlk - 1 := mem_range.mp hs
  have hlt : s < D.nBlk - 1 + 1 - 1 := by omega
  have hb := D.blk_of_slot (mem_range.mp hP) hs'
  have hr : D.colBlk P s < D.nBlk := lt_trans hb.1 hb.2.1
  rw [if_pos hlt]
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq, if_pos (mem_range.mpr hr)]

/-- A sum over the positions, block by block. -/
theorem sum_pos (f : ℕ → E) :
    ∑ i ∈ range D.T, f i = ∑ I ∈ range D.nBlk, ∑ i' ∈ range D.B, f (D.B * I + i') := by
  show ∑ i ∈ range (D.nBlk * D.B), f i = _
  rw [Alg.sum_range_mul_add]
  exact sum_congr rfl fun I _ => sum_congr rfl fun i' _ => by rw [Nat.mul_comm]

/-- The block and the place in the block of a position. -/
theorem pos_parts {I i' : ℕ} (h : i' < D.B) :
    (D.B * I + i') / D.B = I ∧ (D.B * I + i') % D.B = i' := by
  rw [Nat.mul_comm]
  exact Dim.div_step D.B_pos h

variable (C : Calls) (p : Pub E) (t : Raw → E)

/-! ## Step s8: the denominator times the output -/

/-- The first map of step s8 is the read of the denominators. -/
theorem aext8 (b : ℕ) (ξ : ℕ → E) :
    Aext D C p t .s8 b ξ = rd2 D ξ (eqT D (sh ξ D.lg)) (denV t b) := by
  show ext (D.lg + D.lT) (fun X => denV t b (X / D.T) (X % D.T)) ξ = _
  rw [ext_two]
  unfold rd2 eqT
  rw [D.T_eq]
  refine sum_congr rfl fun g _ => sum_congr rfl fun i hi => ?_
  have e := Dim.div_step (a := g) (Nat.two_pow_pos D.lT) (mem_range.mp hi)
  rw [e.1, e.2, eqN_sh]

/-- The second map of step s8 is the read of the outputs. -/
theorem bext8 (b : ℕ) (ξ : ℕ → E) :
    Bext D C p t .s8 b ξ = rd3 D ξ (eqT D (sh ξ D.lg)) (yn D C p.z) (outV t b) := by
  show ext (D.lg + D.lT)
    (fun X => conN D (yn D C p.z) fun n => outV t b (X / D.T) (X % D.T) n) ξ = _
  rw [ext_two]
  unfold rd3 eqT conN
  rw [D.T_eq]
  refine sum_congr rfl fun g _ => sum_congr rfl fun i hi => ?_
  have e := Dim.div_step (a := g) (Nat.two_pow_pos D.lT) (mem_range.mp hi)
  rw [e.1, e.2, eqN_sh, mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-! ## Step s6d: the scores on the diagonal -/

/-- The weights on the positions of a read at a block point vI and a point v in the block. -/
def psiDiag (vI v : ℕ → E) (i : ℕ) : E := eqN D.lB 0 v (i % D.B) * eqN (D.lP + 1) 0 vI (i / D.B)

/-- A map on the cube (g | I | n) that contracts the places of block I, as a read. -/
theorem diag_rd3 (v : ℕ → E) (a : ℕ → ℕ → ℕ → E) (ξ : ℕ → E) :
    ext (D.lg + (D.lP + 1) + D.ln)
        (fun X => conB D v fun i' => a (X / D.ch / D.nBlk) (D.B * (X / D.ch % D.nBlk) + i')
          (X % D.ch)) ξ =
      rd3 D ξ (psiDiag D (sh ξ D.lg) v) (sh ξ (D.lg + (D.lP + 1))) a := by
  rw [ext_three, nBlk_pow]
  unfold rd3 conB psiDiag
  refine sum_congr rfl fun g _ => ?_
  rw [sum_pos]
  refine sum_congr rfl fun I hI => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  have e1 := Dim.div_step (a := g * D.nBlk + I) (Nat.two_pow_pos D.ln) (mem_range.mp hn)
  have e2 := Dim.div_step (a := g) D.nBlk_pos (mem_range.mp hI)
  simp only [Dim.ch, e1.1, e1.2, e2.1, e2.2]
  rw [mul_sum]
  refine sum_congr rfl fun i' hi' => ?_
  have e3 := pos_parts D (I := I) (mem_range.mp hi')
  rw [e3.1, e3.2]
  ring

/-- The first map of step s6d is the read of the queries. -/
theorem aext6d (b : ℕ) (ξ : ℕ → E) :
    Aext D C p t .s6d b ξ =
      rd3 D ξ (psiDiag D (sh ξ D.lg) (zi' D C p.z)) (sh ξ (D.lg + (D.lP + 1))) (qryV t b) :=
  diag_rd3 D (zi' D C p.z) (qryV t b) ξ

/-- The second map of step s6d is the read of the keys. -/
theorem bext6d (b : ℕ) (ξ : ℕ → E) :
    Bext D C p t .s6d b ξ =
      rd3 D ξ (psiDiag D (sh ξ D.lg) (zj' D C p.z)) (sh ξ (D.lg + (D.lP + 1)))
        (keyV t (D.lamOf b)) :=
  diag_rd3 D (zj' D C p.z) (keyV t (D.lamOf b)) ξ

/-! ## Steps s6b and s11: the tiles below the diagonal -/

/-- The sums over the pairs (P, s) and over two further indices, gathered by blocks. blkW, blk: the
weights of the blocks and the block of a pair, for rows or for columns (tile_row, tile_col). -/
theorem tile_sum (vP vs : ℕ → E) (blkW : ℕ → E) (blk : ℕ → ℕ → ℕ)
    (ht : ∀ H : ℕ → E, ∑ I ∈ range D.nBlk, blkW I * H I =
      ∑ P ∈ range D.hP, ∑ s ∈ range D.nBlk, eqN D.lP 0 vP P * eqN (D.lP + 1) 0 vs s *
        (if s < D.nBlk - 1 then H (blk P s) else 0))
    (U V : Finset ℕ) (f : ℕ → ℕ → ℕ → E) :
    ∑ P ∈ range D.hP, ∑ s ∈ range D.nBlk, ∑ u ∈ U,
        eqN D.lP 0 vP P * eqN (D.lP + 1) 0 vs s *
          (if s < D.nBlk - 1 then ∑ v ∈ V, f (blk P s) u v else 0) =
      ∑ I ∈ range D.nBlk, blkW I * ∑ u ∈ U, ∑ v ∈ V, f I u v := by
  rw [ht fun I => ∑ u ∈ U, ∑ v ∈ V, f I u v]
  refine sum_congr rfl fun P _ => sum_congr rfl fun s _ => ?_
  by_cases c : s < D.nBlk - 1
  · simp only [if_pos c]
    rw [mul_sum]
  · simp only [if_neg c, mul_zero, sum_const_zero]

/-- A map on the cube (g | P | s | n) that contracts the places of the block of (P, s), and is 0 at
the last s, as a read. -/
theorem tile_rd3 (blkW : ℕ → E) (blk : ℕ → ℕ → ℕ) (ξ : ℕ → E)
    (ht : ∀ H : ℕ → E, ∑ I ∈ range D.nBlk, blkW I * H I =
      ∑ P ∈ range D.hP, ∑ s ∈ range D.nBlk,
        eqN D.lP 0 (sh ξ D.lg) P * eqN (D.lP + 1) 0 (sh ξ (D.lg + D.lP)) s *
          (if s < D.nBlk - 1 then H (blk P s) else 0))
    (v : ℕ → E) (a : ℕ → ℕ → ℕ → E) :
    ext (D.lg + D.lP + (D.lP + 1) + D.ln)
        (fun X => if X / D.ch % D.nBlk < D.nBlk - 1 then
          conB D v fun i' => a (X / D.ch / D.nBlk / D.hP)
            (D.B * blk (X / D.ch / D.nBlk % D.hP) (X / D.ch % D.nBlk) + i') (X % D.ch)
          else 0) ξ =
      rd3 D ξ (fun i => eqN D.lB 0 v (i % D.B) * blkW (i / D.B))
        (sh ξ (D.lg + D.lP + (D.lP + 1))) a := by
  rw [ext_four, nBlk_pow]
  unfold rd3 conB
  refine sum_congr rfl fun g _ => ?_
  have hR : ∑ i ∈ range D.T, ∑ n ∈ range D.ch,
      eqN D.lg 0 ξ g * (eqN D.lB 0 v (i % D.B) * blkW (i / D.B)) *
        eqN D.ln 0 (sh ξ (D.lg + D.lP + (D.lP + 1))) n * a g i n =
      ∑ I ∈ range D.nBlk, blkW I * ∑ n ∈ range D.ch, ∑ i' ∈ range D.B,
        eqN D.lg 0 ξ g * eqN D.ln 0 (sh ξ (D.lg + D.lP + (D.lP + 1))) n *
          (eqN D.lB 0 v i' * a g (D.B * I + i') n) := by
    rw [sum_pos]
    refine sum_congr rfl fun I _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i' hi' => ?_
    have e3 := pos_parts D (I := I) (mem_range.mp hi')
    rw [e3.1, e3.2]
    ring
  rw [hR, ← tile_sum D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) blkW blk ht]
  refine sum_congr rfl fun P hP => sum_congr rfl fun s hs => sum_congr rfl fun n hn => ?_
  have e1 := Dim.div_step (a := (g * 2 ^ D.lP + P) * D.nBlk + s) (Nat.two_pow_pos D.ln)
    (mem_range.mp hn)
  have e2 := Dim.div_step (a := g * 2 ^ D.lP + P) D.nBlk_pos (mem_range.mp hs)
  have e3 := Dim.div_step (a := g) (Nat.two_pow_pos D.lP) (mem_range.mp hP)
  simp only [Dim.ch, Dim.hP, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
  by_cases c : s < D.nBlk - 1
  · simp only [if_pos c]
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun i' _ => by ring
  · simp only [if_neg c, mul_zero]

/-- The first map of step s6b is the read of the queries. -/
theorem aext6b (b : ℕ) (ξ : ℕ → E) :
    Aext D C p t .s6b b ξ =
      rd3 D ξ (psiRow D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (zi' D C p.z))
        (sh ξ (D.lg + D.lP + (D.lP + 1))) (qryV t b) :=
  tile_rd3 D (blkRow D (sh ξ D.lg) (sh ξ (D.lg + D.lP))) D.rowBlk ξ
    (tile_row D (sh ξ D.lg) (sh ξ (D.lg + D.lP))) (zi' D C p.z) (qryV t b)

/-- The second map of step s6b is the read of the keys. -/
theorem bext6b (b : ℕ) (ξ : ℕ → E) :
    Bext D C p t .s6b b ξ =
      rd3 D ξ (psiCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (zj' D C p.z))
        (sh ξ (D.lg + D.lP + (D.lP + 1))) (keyV t (D.lamOf b)) :=
  tile_rd3 D (blkCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP))) D.colBlk ξ
    (tile_col D (sh ξ D.lg) (sh ξ (D.lg + D.lP))) (zj' D C p.z) (keyV t (D.lamOf b))

/-- The second map of step s11 is th plus the read of the values. -/
theorem bext11 (b : ℕ) (ξ : ℕ → E) :
    Bext D C p t .s11 b ξ =
      p.th + rd3 D ξ (psiCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (sh ξ (D.lg + D.lP + (D.lP + 1))))
        (yn D C p.z) (valV t (D.lamOf b)) := by
  have hB : Bcube D C p t .s11 b = fun X => p.th +
      (if X / D.B % D.nBlk < D.nBlk - 1 then
        conN D (yn D C p.z) fun n => valV t (D.lamOf b) (X / D.B / D.nBlk / D.hP)
          (D.B * D.colBlk (X / D.B / D.nBlk % D.hP) (X / D.B % D.nBlk) + X % D.B) n
      else 0) := by
    funext X
    show (if X / D.B % D.nBlk < D.nBlk - 1 then _ else _) = _
    by_cases c : X / D.B % D.nBlk < D.nBlk - 1
    · rw [if_pos c, if_pos c]
    · rw [if_neg c, if_neg c, add_zero]
  show ext (D.lg + D.lP + (D.lP + 1) + D.lB) (Bcube D C p t .s11 b) ξ = _
  rw [hB, ext_add, ext_const]
  congr 1
  rw [ext_four, nBlk_pow]
  unfold rd3 conN psiCol
  refine sum_congr rfl fun g _ => ?_
  have hR : ∑ i ∈ range D.T, ∑ n ∈ range D.ch,
      eqN D.lg 0 ξ g * (eqN D.lB 0 (sh ξ (D.lg + D.lP + (D.lP + 1))) (i % D.B) *
        blkCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (i / D.B)) *
        eqN D.ln 0 (yn D C p.z) n * valV t (D.lamOf b) g i n =
      ∑ I ∈ range D.nBlk, blkCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) I *
        ∑ j' ∈ range D.B, ∑ n ∈ range D.ch,
          eqN D.lg 0 ξ g * eqN D.lB 0 (sh ξ (D.lg + D.lP + (D.lP + 1))) j' *
            (eqN D.ln 0 (yn D C p.z) n * valV t (D.lamOf b) g (D.B * I + j') n) := by
    rw [sum_pos]
    refine sum_congr rfl fun I _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j' hj' => ?_
    rw [mul_sum]
    have e3 := pos_parts D (I := I) (mem_range.mp hj')
    refine sum_congr rfl fun n _ => ?_
    rw [e3.1, e3.2]
    ring
  rw [hR, ← tile_sum D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) _ D.colBlk
    (tile_col D (sh ξ D.lg) (sh ξ (D.lg + D.lP)))]
  refine sum_congr rfl fun P hP => sum_congr rfl fun s hs => sum_congr rfl fun j' hj' => ?_
  have e1 := Dim.div_step (a := (g * 2 ^ D.lP + P) * D.nBlk + s) (Nat.two_pow_pos D.lB)
    (mem_range.mp hj')
  have e2 := Dim.div_step (a := g * 2 ^ D.lP + P) D.nBlk_pos (mem_range.mp hs)
  have e3 := Dim.div_step (a := g) (Nat.two_pow_pos D.lP) (mem_range.mp hP)
  simp only [Dim.B, Dim.hP, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
  by_cases c : s < D.nBlk - 1
  · simp only [if_pos c]
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  · simp only [if_neg c, mul_zero]

/-- The point at which step s11 reads the softmax weights: the step's coordinates of (g | P | s),
the lookup's coordinates of the row in a tile, the step's coordinates of the column in a tile. -/
def ptBelow (ξ : ℕ → E) : ℕ → E :=
  cat (D.lg + D.lP + (D.lP + 1)) ξ
    (cat D.lB (yi' D C p.z) (sh ξ (D.lg + D.lP + (D.lP + 1))))

/-- The first map of step s11 is the extension of the softmax weights over the entries of the region
below the diagonal. -/
theorem aext11 (b : ℕ) (ξ : ℕ → E) :
    Aext D C p t .s11 b ξ = ext D.lM (wtV t .M b) (ptBelow D C p ξ) := by
  show ext (D.lg + D.lP + (D.lP + 1) + D.lB)
      (fun X => conB D (yi' D C p.z) fun i' => wtV t .M b
        (D.codeM (X / D.B / D.nBlk / D.hP) (X / D.B / D.nBlk % D.hP) (X / D.B % D.nBlk) i'
          (X % D.B))) ξ =
    ext (D.lg + D.lP + (D.lP + 1) + D.lB + D.lB) (wtV t .M b) (ptBelow D C p ξ)
  conv_lhs => rw [ext_two]
  conv_rhs => rw [ext_three]
  unfold conB
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j' hj' => ?_
  have e1 := Dim.div_step (a := u) (Nat.two_pow_pos D.lB) (mem_range.mp hj')
  simp only [Dim.B, e1.1, e1.2]
  rw [mul_sum]
  refine sum_congr rfl fun i' _ => ?_
  have c1 : D.codeM (u / D.nBlk / D.hP) (u / D.nBlk % D.hP) (u % D.nBlk) i' j' =
      (u * 2 ^ D.lB + i') * 2 ^ D.lB + j' := by
    show (((u / D.nBlk / D.hP * D.hP + u / D.nBlk % D.hP) * D.nBlk + u % D.nBlk) * 2 ^ D.lB +
      i') * 2 ^ D.lB + j' = _
    rw [Nat.div_add_mod', Nat.div_add_mod']
  have a1 : eqN (D.lg + D.lP + (D.lP + 1)) 0 (ptBelow D C p ξ) u =
      eqN (D.lg + D.lP + (D.lP + 1)) 0 ξ u :=
    eqN_agree (fun k hk => by simp only [ptBelow, cat, Nat.zero_add, if_pos hk]) u
  have a2 : eqN D.lB 0 (sh (ptBelow D C p ξ) (D.lg + D.lP + (D.lP + 1))) i' =
      eqN D.lB 0 (yi' D C p.z) i' :=
    eqN_agree (fun k hk => by
      have n1 : ¬ D.lg + D.lP + (D.lP + 1) + k < D.lg + D.lP + (D.lP + 1) := by omega
      have n2 : D.lg + D.lP + (D.lP + 1) + k - (D.lg + D.lP + (D.lP + 1)) = k := by omega
      simp only [ptBelow, cat, sh, Nat.zero_add, if_neg n1, n2, if_pos hk]) i'
  have a3 : eqN D.lB 0 (sh (ptBelow D C p ξ) (D.lg + D.lP + (D.lP + 1) + D.lB)) j' =
      eqN D.lB (D.lg + D.lP + (D.lP + 1)) ξ j' :=
    eqN_agree (fun k _ => by
      have n1 : ¬ D.lg + D.lP + (D.lP + 1) + D.lB + k < D.lg + D.lP + (D.lP + 1) := by
        omega
      have n2 : D.lg + D.lP + (D.lP + 1) + D.lB + k - (D.lg + D.lP + (D.lP + 1)) =
          D.lB + k := by omega
      have n3 : ¬ D.lB + k < D.lB := by omega
      have n4 : D.lB + k - D.lB = k := by omega
      simp only [ptBelow, cat, sh, Nat.zero_add, if_neg n1, n2, if_neg n3, n4]) j'
  rw [c1, a1, a2, a3]
  ring

end Cb.Pv.Att

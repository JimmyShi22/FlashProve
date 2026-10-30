-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/ValueBelow.lean: the sum of step s11 of an attention segment, as a read of the
part of the library's sum over a row of scores that runs over the tiles below the diagonal; and a
proof of ValueMean (Cb/Pv/Att/Mean/Means.lean).

Step s11 (Inst/Model/Att/Sums.lean) is the value product on the tiles below the diagonal. Its cube
is (head g | slot row P | slot s | place j' in the tile). At a vertex the public weight is the
equality weight of the lookup's point at the row block of the slot (P, s), and 0 at the one slot of
a row that stands for no tile (wb11_vertex). The library's sum over a row of scores asks, for a
position i, for the slots whose row block is the block of i; summed over the positions under the
equality weights of the lookup's point this is the same sum over the slots (right11).

Main theorems: eqPt_at_cube, ext_at_cube, wb11_vertex, acube11, bcube11, left11, right11, sum11,
valueMean, value_split (if the two sums add up to a + th c, then (a - the accumulator's rule value)
+ th (c - the batch of the reads of the sums of the softmax weights) = 0: an equation of degree 1 in
th whose two coefficients do not hang on th).

All of it is algebra on the library's definitions. Nothing is said about a verifier.


-/
import Cb.Pv.Att.Mean.ValueOn
import Cb.Pv.Att.Mean.Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E]

/-! ## Tools -/

/-- The equality polynomial of u and a point whose first n coordinates are those of the vertex x. -/
theorem eqPt_at_cube (n : ℕ) (u ξ : ℕ → E) (x : ℕ) (h : ∀ k < n, ξ k = cubePt n x k) :
    eqPt n u ξ = eqN n 0 u x := by
  rw [eqPt_vertex (g := n) (n := n) (X := x) (off := 0) (m := 0) u ξ (by omega)
    (fun k hk => by rw [Nat.zero_add]; exact h k hk), pow_zero, Nat.div_one]

/-- An extension at a point whose first n coordinates are those of the vertex x. -/
theorem ext_at_cube (n : ℕ) (f ξ : ℕ → E) {x : ℕ} (hx : x < 2 ^ n)
    (h : ∀ k < n, ξ k = cubePt n x k) : Blocks.ext n f ξ = f x := by
  rw [ext_congr_point h, ext_cubePt _ _ hx]

/-- Four sums in another order. -/
theorem sum_slot4 (A B C' D' : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → E) :
    ∑ I ∈ A, ∑ i ∈ B, ∑ P ∈ C', ∑ s ∈ D', f I i P s =
      ∑ P ∈ C', ∑ s ∈ D', ∑ i ∈ B, ∑ I ∈ A, f I i P s := by
  calc ∑ I ∈ A, ∑ i ∈ B, ∑ P ∈ C', ∑ s ∈ D', f I i P s
      = ∑ i ∈ B, ∑ I ∈ A, ∑ P ∈ C', ∑ s ∈ D', f I i P s := sum_comm
    _ = ∑ i ∈ B, ∑ P ∈ C', ∑ I ∈ A, ∑ s ∈ D', f I i P s :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ i ∈ B, ∑ P ∈ C', ∑ s ∈ D', ∑ I ∈ A, f I i P s :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ P ∈ C', ∑ i ∈ B, ∑ s ∈ D', ∑ I ∈ A, f I i P s := sum_comm
    _ = ∑ P ∈ C', ∑ s ∈ D', ∑ i ∈ B, ∑ I ∈ A, f I i P s :=
        sum_congr rfl fun _ _ => sum_comm

variable (D : Dim)

/-- A sum over the slots of a row that stand for a tile, as a sum over all slots. -/
theorem sum_slots (f : ℕ → E) :
    ∑ s ∈ range (D.nBlk - 1), f s =
      ∑ s ∈ range (2 ^ (D.lP + 1)), if s < D.nBlk - 1 then f s else 0 := by
  rw [nBlk_pow]
  calc ∑ s ∈ range (D.nBlk - 1), f s
      = ∑ s ∈ range (D.nBlk - 1), if s < D.nBlk - 1 then f s else 0 :=
        sum_congr rfl fun s hs => by rw [if_pos (mem_range.mp hs)]
    _ = ∑ s ∈ range D.nBlk, if s < D.nBlk - 1 then f s else 0 :=
        sum_subset (range_subset_range.mpr (Nat.sub_le _ _)) fun x _ hx =>
          if_neg fun h => hx (mem_range.mpr h)

variable (C : Calls) (p : Pub E) (t : Raw → E)

/-! ## Step s11 at a vertex -/

section Vertex
variable (b g : ℕ) {P s j' : ℕ} (hP : P < 2 ^ D.lP) (hs : s < 2 ^ (D.lP + 1))
  (hj : j' < 2 ^ D.lB)

include hP hs hj in
/-- The weight of step s11 at the vertex (g | P | s | j'). -/
theorem wb11_vertex :
    Wb D C p .s11 b (cubePt (D.lg + D.lP + (D.lP + 1) + D.lB)
        (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j')) =
      wp D C p.z .w3 b * eqN D.lg 0 (yg D C p.z) g *
        (if s < D.nBlk - 1 then eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P s) else 0) := by
  have c1 : ∀ k < D.lg, (cubePt (D.lg + D.lP + (D.lP + 1) + D.lB)
      (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') : ℕ → E) k =
      cubePt D.lg g k := fun k hk => by
    rw [cube_fst (D.lg + D.lP) (D.lP + 1) D.lB _ hs hj (by omega),
      cube_two_fst D.lg D.lP g hP hk]
  have c2 : ∀ k < D.lP, sh (cubePt (D.lg + D.lP + (D.lP + 1) + D.lB)
      (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') : ℕ → E) D.lg k =
      cubePt D.lP P k := fun k hk => by
    show (cubePt _ _ : ℕ → E) (D.lg + k) = _
    rw [cube_fst (D.lg + D.lP) (D.lP + 1) D.lB _ hs hj (by omega),
      cube_two_snd D.lg D.lP g hP hk]
  have c3 : ∀ k < D.lP + 1, sh (cubePt (D.lg + D.lP + (D.lP + 1) + D.lB)
      (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') : ℕ → E) (D.lg + D.lP) k =
      cubePt (D.lP + 1) s k := fun k hk =>
    cube_snd (D.lg + D.lP) (D.lP + 1) D.lB _ hs hj hk
  generalize (cubePt (D.lg + D.lP + (D.lP + 1) + D.lB)
    (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') : ℕ → E) = ξ at c1 c2 c3 ⊢
  show wp D C p.z .w3 b * eqPt D.lg (yg D C p.z) ξ *
      ∑ P' ∈ range (2 ^ D.lP), ∑ s' ∈ range (D.nBlk - 1), eqN D.lP 0 (sh ξ D.lg) P' *
        eqN (D.lP + 1) 0 (sh ξ (D.lg + D.lP)) s' *
        eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P' s') = _
  rw [eqPt_at_cube D.lg (yg D C p.z) ξ g c1]
  congr 1
  have i1 : ∑ P' ∈ range (2 ^ D.lP), ∑ s' ∈ range (D.nBlk - 1), eqN D.lP 0 (sh ξ D.lg) P' *
        eqN (D.lP + 1) 0 (sh ξ (D.lg + D.lP)) s' *
        eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P' s') =
      Blocks.ext D.lP (fun P' => ∑ s' ∈ range (D.nBlk - 1),
        eqN (D.lP + 1) 0 (sh ξ (D.lg + D.lP)) s' *
          eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P' s')) (sh ξ D.lg) := by
    unfold Blocks.ext
    refine sum_congr rfl fun P' _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun s' _ => by ring
  rw [i1, ext_at_cube D.lP _ (sh ξ D.lg) hP c2, sum_slots]
  have i2 : ∑ s' ∈ range (2 ^ (D.lP + 1)), (if s' < D.nBlk - 1 then
        eqN (D.lP + 1) 0 (sh ξ (D.lg + D.lP)) s' *
          eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P s') else 0) =
      Blocks.ext (D.lP + 1) (fun s' => if s' < D.nBlk - 1 then
        eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P s') else 0) (sh ξ (D.lg + D.lP)) := by
    unfold Blocks.ext
    refine sum_congr rfl fun s' _ => ?_
    beta_reduce
    by_cases h : s' < D.nBlk - 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [i2, ext_at_cube (D.lP + 1) _ (sh ξ (D.lg + D.lP)) hs c3]

include hP hs hj in
/-- The parts of the index of a vertex. -/
theorem parts11 :
    ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB / 2 ^ (D.lP + 1) /
        2 ^ D.lP = g) ∧
      ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB / 2 ^ (D.lP + 1) %
        2 ^ D.lP = P) ∧
      ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB % 2 ^ (D.lP + 1) =
        s) ∧
      ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') % 2 ^ D.lB = j') := by
  have e1 := Dim.div_step (a := (g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) (Nat.two_pow_pos D.lB) hj
  have e2 := Dim.div_step (a := g * 2 ^ D.lP + P) (Nat.two_pow_pos (D.lP + 1)) hs
  have e3 := Dim.div_step (a := g) (Nat.two_pow_pos D.lP) hP
  rw [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

include hP hs hj in
/-- The first map of step s11 at the vertex (g | P | s | j'). -/
theorem acube11 :
    Acube D C p t .s11 b (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') =
      ∑ i' ∈ range (2 ^ D.lB),
        eqN D.lB 0 (yi' D C p.z) i' * wtV t .M b (D.codeM g P s i' j') := by
  obtain ⟨q1, q2, q3, q4⟩ := parts11 D g hP hs hj
  show ∑ i' ∈ range (2 ^ D.lB), eqN D.lB 0 (yi' D C p.z) i' * wtV t .M b
    (D.codeM
      ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB / D.nBlk / 2 ^ D.lP)
      ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB / D.nBlk % 2 ^ D.lP)
      ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB % D.nBlk) i'
      ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') % 2 ^ D.lB)) = _
  rw [← nBlk_pow, q1, q2, q3, q4]

include hP hs hj in
/-- The second map of step s11 at the vertex (g | P | s | j'). -/
theorem bcube11 :
    Bcube D C p t .s11 b (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') =
      if s < D.nBlk - 1 then valG D C p t b g (2 ^ D.lB * D.colBlk P s + j') else p.th := by
  obtain ⟨q1, q2, q3, q4⟩ := parts11 D g hP hs hj
  have n0 := nBlk_pow D
  show (if (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB % D.nBlk <
        D.nBlk - 1 then
      p.th + conN D (yn D C p.z) (fun n => valV t (D.lamOf b)
        ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB / D.nBlk /
          2 ^ D.lP)
        (2 ^ D.lB * D.colBlk
          ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB / D.nBlk %
            2 ^ D.lP)
          ((((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') / 2 ^ D.lB % D.nBlk) +
          (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') % 2 ^ D.lB) n)
    else p.th) = _
  rw [← n0, q1, q2, q3, q4]
  rfl

end Vertex

/-! ## The two sides -/

/-- The sum over the places j' of a tile below the diagonal, at the place i' of the row. -/
def tileZ (G : ℕ → E) (b g i' P s : ℕ) : E :=
  ∑ j' ∈ range (2 ^ D.lB), wtV t .M b (D.codeM g P s i' j') * G (2 ^ D.lB * D.colBlk P s + j')

/-- The sum of step s11 over the slots and places, for a pair and a head. -/
theorem left11 (b g : ℕ) :
    ∑ P ∈ range (2 ^ D.lP), ∑ s ∈ range (2 ^ (D.lP + 1)), ∑ j' ∈ range (2 ^ D.lB),
        Wb D C p .s11 b (cubePt (D.lg + D.lP + (D.lP + 1) + D.lB)
            (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j')) *
          Acube D C p t .s11 b (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') *
          Bcube D C p t .s11 b (((g * 2 ^ D.lP + P) * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + j') =
      wp D C p.z .w3 b * (eqN D.lg 0 (yg D C p.z) g *
        ∑ P ∈ range (2 ^ D.lP), ∑ s ∈ range (D.nBlk - 1),
          eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P s) *
            ∑ i' ∈ range (2 ^ D.lB), eqN D.lB 0 (yi' D C p.z) i' *
              tileZ D t (valG D C p t b g) b g i' P s) := by
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun P hP => ?_
  rw [sum_slots, mul_sum, mul_sum]
  refine sum_congr rfl fun s hs => ?_
  rw [sum_congr rfl fun j' hj => by
    rw [wb11_vertex D C p b g (mem_range.mp hP) (mem_range.mp hs) (mem_range.mp hj),
      acube11 D C p t b g (mem_range.mp hP) (mem_range.mp hs) (mem_range.mp hj),
      bcube11 D C p t b g (mem_range.mp hP) (mem_range.mp hs) (mem_range.mp hj)]]
  by_cases h : s < D.nBlk - 1
  · simp only [if_pos h]
    unfold tileZ
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun i' _ => sum_congr rfl fun j' _ => by ring
  · simp only [if_neg h, mul_zero, zero_mul, sum_const_zero]

/-- The read of the part below the diagonal over the positions, for a pair and a head. -/
theorem right11 (G : ℕ → E) (b g : ℕ) :
    ∑ i ∈ range (2 ^ D.lT), eqN D.lT 0 (yi D C p.z) i * rowBelow D t G b g i =
      ∑ P ∈ range (2 ^ D.lP), ∑ s ∈ range (D.nBlk - 1),
        eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P s) *
          ∑ i' ∈ range (2 ^ D.lB), eqN D.lB 0 (yi' D C p.z) i' * tileZ D t G b g i' P s := by
  show ∑ i ∈ range (2 ^ (D.lP + 1 + D.lB)), _ = _
  rw [pow_add 2 (D.lP + 1) D.lB, Alg.sum_range_mul_add]
  have l : ∀ I ∈ range (2 ^ (D.lP + 1)), ∀ i' ∈ range (2 ^ D.lB),
      eqN D.lT 0 (yi D C p.z) (I * 2 ^ D.lB + i') * rowBelow D t G b g (I * 2 ^ D.lB + i') =
        ∑ P ∈ range (2 ^ D.lP), ∑ s ∈ range (D.nBlk - 1),
          if D.rowBlk P s = I then eqN (D.lP + 1) 0 (yI D C p.z) I *
            (eqN D.lB 0 (yi' D C p.z) i' * tileZ D t G b g i' P s) else 0 := by
    intro I _ i' hi
    have e := Dim.div_step (a := I) (Nat.two_pow_pos D.lB) (mem_range.mp hi)
    rw [yi_cut D C p I (mem_range.mp hi)]
    show _ * (∑ P ∈ range (2 ^ D.lP), ∑ s ∈ range (D.nBlk - 1),
      if D.rowBlk P s = (I * 2 ^ D.lB + i') / 2 ^ D.lB then
        ∑ j' ∈ range (2 ^ D.lB),
          wtV t .M b (D.codeM g P s ((I * 2 ^ D.lB + i') % 2 ^ D.lB) j') *
            G (2 ^ D.lB * D.colBlk P s + j')
      else 0) = _
    rw [e.1, e.2, mul_sum]
    refine sum_congr rfl fun P _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun s _ => ?_
    unfold tileZ
    split_ifs <;> ring
  rw [sum_congr rfl fun I hI => sum_congr rfl fun i' hi => l I hI i' hi, sum_slot4]
  refine sum_congr rfl fun P hP => sum_congr rfl fun s hs => ?_
  have hr : D.rowBlk P s ∈ range (2 ^ (D.lP + 1)) := by
    rw [nBlk_pow]
    exact mem_range.mpr (D.blk_of_slot (mem_range.mp hP) (mem_range.mp hs)).2.1
  rw [mul_sum]
  refine sum_congr rfl fun i' _ => ?_
  rw [sum_ite_eq, if_pos hr]

/-- **The sum of step s11 is the batch of the reads of the part of rowSum below the diagonal.** -/
theorem sum11 :
    sumPhi D C p t .s11 =
      ∑ b ∈ range D.nb, wp D C p.z .w3 b *
        rd2 D (yg D C p.z) (eqT D (yi D C p.z)) fun g i =>
          rowBelow D t (valG D C p t b g) b g i := by
  rw [sumPhi_cube, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  show ∑ X ∈ range (2 ^ (D.lg + D.lP + (D.lP + 1) + D.lB)),
    Wb D C p .s11 b (cubePt (D.lg + D.lP + (D.lP + 1) + D.lB) X) * Acube D C p t .s11 b X *
      Bcube D C p t .s11 b X = _
  rw [pow_add 2 (D.lg + D.lP + (D.lP + 1)) D.lB, Alg.sum_range_mul_add,
    pow_add 2 (D.lg + D.lP) (D.lP + 1), Alg.sum_range_mul_add, pow_add 2 D.lg D.lP,
    Alg.sum_range_mul_add]
  unfold rd2 eqT
  rw [D.T_eq, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [left11 D C p t b g, ← right11 D C p t (valG D C p t b g) b g, mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-! ## The two sums together -/

/-- **ValueMean holds.** -/
theorem valueMean : ValueMean := by
  intro E _ D C p t
  rw [sum11, sum12, ← sum_add_distrib]
  show _ = (∑ b ∈ range D.nb, wp D C p.z .w3 b * atY D C p (AC D t b)) + _
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← mul_add, ← rd2_add, atY_rd2]
  have e : ∀ g i, rowBelow D t (valG D C p t b g) b g i + rowOn D t (valG D C p t b g) b g i =
      p.th * EF D t b g i + conN D (yn D C p.z) (AC D t b g i) := by
    intro g i
    rw [← rowSum_halves]
    exact rowSum_lin D t b g i p.th (yn D C p.z) fun j n => valV t (D.lamOf b) g j n
  rw [rd2_congr D _ _ e, rd2_add, rd2_smul]
  ring

/-- **The equation of the value product, sorted by powers of th.** -/
theorem value_split (a c : E)
    (h : sumPhi D C p t .s11 + sumPhi D C p t .s12 = a + p.th * c) :
    (a - rv D C p t .acc) + p.th * (c - ∑ b ∈ range D.nb, wp D C p.z .w3 b *
      rd2 D (yg D C p.z) (eqT D (yi D C p.z)) (EF D t b)) = 0 := by
  have e := valueMean E D C p t
  rw [h] at e
  linear_combination e

end Cb.Pv.Att

#print axioms Cb.Pv.Att.sum11
#print axioms Cb.Pv.Att.valueMean
#print axioms Cb.Pv.Att.value_split

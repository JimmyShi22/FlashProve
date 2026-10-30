-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/BitsScore.lean: proofs of statements of Cb/Pv/Att/Mean/Means.lean.

Proved here: BitsMean (bitsMean) and ScoreMean (scoreMean).

The way. The library's sum of a step runs over the vertices of a cube, and at a vertex an extension
is the array's entry (Blocks.ext_cubePt): sumPhi_cube. The public weight of a step is a product of
equality polynomials of two points; at a vertex each of them is the equality polynomial of a point
and an index (eqPt_vertex), and those of neighbouring parts of a point multiply to that of the whole
point (eqN_cat). What is left is to cut an index into its parts.

Tools: cubePt_at, eqPt_vertex, eqN_cat, eqN_agree, ext_cat, rd2_ext, sumPhi_cube.


-/
import Cb.Pv.Att.Mean.Means
import Blocks.LookupCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

section Tools
variable {E : Type} [Field E]

/-- A coordinate of a vertex of the cube. -/
theorem cubePt_at (g X k : ℕ) (h : k < g) :
    (cubePt g X : ℕ → E) k = if X.testBit (g - 1 - k) then 1 else 0 := by
  simp [cubePt, nat, h, Alg.corner, Alg.bits]

/-- The equality polynomial of a point u and n coordinates of a vertex, from coordinate off on, is
the equality polynomial of u and the index that these coordinates spell. m: the number of
coordinates behind them. -/
theorem eqPt_vertex {g n off m X : ℕ} (u ξ : ℕ → E) (h : off + n + m = g)
    (hξ : ∀ k < n, ξ k = cubePt g X (off + k)) : eqPt n u ξ = eqN n 0 u (X / 2 ^ m) := by
  unfold eqPt eqN
  refine prod_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  have e : g - 1 - (off + k) = n - 1 - k + m := by omega
  rw [hξ k hk', cubePt_at g X (off + k) (by omega), Nat.testBit_div_two_pow, Nat.zero_add, e]
  unfold eq1
  split_ifs <;> ring

/-- The equality polynomial of a point in two parts. -/
theorem eqN_cat (a b : ℕ) (u v : ℕ → E) (X : ℕ) :
    eqN (a + b) 0 (cat a u v) X = eqN a 0 u (X / 2 ^ b) * eqN b 0 v X := by
  unfold eqN
  rw [prod_range_add]
  refine congrArg₂ (· * ·) (prod_congr rfl fun k hk => ?_) (prod_congr rfl fun k hk => ?_)
  · have hk' := mem_range.mp hk
    have e : a + b - 1 - k = a - 1 - k + b := by omega
    rw [Nat.testBit_div_two_pow, e]
    simp only [cat, Nat.zero_add, if_pos hk']
  · have hk' := mem_range.mp hk
    have e : a + b - 1 - (a + k) = b - 1 - k := by omega
    have e2 : ¬ a + k < a := by omega
    have e3 : a + k - a = k := by omega
    rw [e]
    simp only [cat, Nat.zero_add, if_neg e2, e3]

/-- The equality polynomial reads g coordinates of its point, from the offset on. -/
theorem eqN_agree {g off off' : ℕ} {a a' : ℕ → E} (h : ∀ k < g, a (off + k) = a' (off' + k))
    (X : ℕ) : eqN g off a X = eqN g off' a' X := by
  unfold eqN
  exact prod_congr rfl fun k hk => by rw [h k (mem_range.mp hk)]

/-- The extension at a point in two parts, as a double sum. -/
theorem ext_cat (a b : ℕ) (u w v : ℕ → E) :
    ext (a + b) v (cat a u w) =
      ∑ x ∈ range (2 ^ a), ∑ y ∈ range (2 ^ b),
        eqN a 0 u x * eqN b 0 w y * v (x * 2 ^ b + y) := by
  rw [ext_two]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  have h1 : eqN a 0 (cat a u w) x = eqN a 0 u x :=
    eqN_agree (fun k hk => by simp only [cat, Nat.zero_add, if_pos hk]) x
  have h2 : eqN b a (cat a u w) y = eqN b 0 w y :=
    eqN_agree (fun k _ => by
      have e1 : ¬ a + k < a := by omega
      have e2 : a + k - a = k := by omega
      simp only [cat, if_neg e1, e2, Nat.zero_add]) y
  rw [h1, h2]

variable (D : Dim)

/-- The library's read of an array on (g, i) is the extension of the array on the cube (i | g). -/
theorem rd2_ext (vg vi : ℕ → E) (a : ℕ → ℕ → E) :
    rd2 D vg (eqT D vi) a =
      ext (D.lT + D.lg) (fun Y => a (Y % D.nG) (Y / D.nG)) (cat D.lT vi vg) := by
  rw [ext_cat]
  unfold rd2 eqT
  rw [sum_comm, D.T_eq]
  refine sum_congr rfl fun i _ => sum_congr rfl fun g hg => ?_
  have hg' : g < 2 ^ D.lg := mem_range.mp hg
  have e := Dim.div_step (a := i) (Nat.two_pow_pos D.lg) hg'
  show eqN D.lg 0 vg g * eqN D.lT 0 vi i * a g i =
    eqN D.lT 0 vi i * eqN D.lg 0 vg g *
      a ((i * 2 ^ D.lg + g) % 2 ^ D.lg) ((i * 2 ^ D.lg + g) / 2 ^ D.lg)
  rw [e.1, e.2]
  ring

variable (C : Calls) (p : Pub E) (t : Raw → E)

/-- The sum of a step, on the arrays at the vertices. -/
theorem sumPhi_cube (s : Step) :
    sumPhi D C p t s =
      ∑ X ∈ range (2 ^ s.g D), ∑ b ∈ range D.nb,
        Wb D C p s b (cubePt (s.g D) X) * Acube D C p t s b X * Bcube D C p t s b X := by
  unfold sumPhi Phi Aext Bext
  refine sum_congr rfl fun X hX => sum_congr rfl fun b _ => ?_
  rw [ext_cubePt _ _ (mem_range.mp hX), ext_cubePt _ _ (mem_range.mp hX)]

end Tools

/-! ## The bits -/

/-- **BitsMean holds.** -/
theorem bitsMean : BitsMean := by
  intro E _ D C p t
  rw [sumPhi_cube, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  unfold Blocks.ext
  rw [mul_sum]
  refine sum_congr rfl fun X _ => ?_
  have w : Wb D C p .s21 b (cubePt (D.lT + D.lg + D.lK) X) =
      p.o'' b * eqN (D.lT + D.lg + D.lK) 0 (cat D.lT p.tbi (cat D.lg p.tbg p.tk)) X := by
    show p.o'' b * eqPt D.lT p.tbi (cubePt (D.lT + D.lg + D.lK) X) *
        eqPt D.lg p.tbg (sh (cubePt (D.lT + D.lg + D.lK) X) D.lT) *
        eqPt D.lK p.tk (sh (cubePt (D.lT + D.lg + D.lK) X) (D.lT + D.lg)) = _
    rw [eqPt_vertex (g := D.lT + D.lg + D.lK) (n := D.lT) (X := X) (off := 0) (m := D.lg + D.lK)
        p.tbi (cubePt (D.lT + D.lg + D.lK) X) (by omega) (fun k _ => by rw [Nat.zero_add]),
      eqPt_vertex (g := D.lT + D.lg + D.lK) (n := D.lg) (X := X) (off := D.lT) (m := D.lK) p.tbg
        (sh (cubePt (D.lT + D.lg + D.lK) X) D.lT) (by omega) (fun _ _ => rfl),
      eqPt_vertex (g := D.lT + D.lg + D.lK) (n := D.lK) (X := X) (off := D.lT + D.lg) (m := 0)
        p.tk (sh (cubePt (D.lT + D.lg + D.lK) X) (D.lT + D.lg)) (by omega) (fun _ _ => rfl),
      Nat.add_assoc, eqN_cat, eqN_cat, pow_zero, Nat.div_one]
    ring
  have k : Acube D C p t .s21 b X * Bcube D C p t .s21 b X = bitIdn D t b X := by
    show (if X % 2 ^ D.lK < D.lT then
          ibV t (X % 2 ^ D.lK) b (X / 2 ^ D.lK % D.nG) (X / 2 ^ D.lK / D.nG) else 0) *
        ((if X % 2 ^ D.lK < D.lT then
          ibV t (X % 2 ^ D.lK) b (X / 2 ^ D.lK % D.nG) (X / 2 ^ D.lK / D.nG) else 0) - 1) =
      if X % 2 ^ D.lK < D.lT then
        ibV t (X % 2 ^ D.lK) b (X / 2 ^ D.lK % D.nG) (X / 2 ^ D.lK / D.nG) *
          (ibV t (X % 2 ^ D.lK) b (X / 2 ^ D.lK % D.nG) (X / 2 ^ D.lK / D.nG) - 1)
      else 0
    split_ifs <;> ring
  show Wb D C p .s21 b (cubePt (D.lT + D.lg + D.lK) X) * Acube D C p t .s21 b X *
      Bcube D C p t .s21 b X = _
  rw [w, mul_assoc, k]
  ring

/-! ## The score at the index -/

/-- The sum of step s16, pair by pair, as an extension on the cube (i | g). -/
theorem sum16 {E : Type} [Field E] (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E) :
    sumPhi D C p t .s16 =
      ∑ b ∈ range D.nb, p.o b *
        ext (D.lT + D.lg)
          (fun Y => ∑ n ∈ range D.ch,
            qryV t b (Y % D.nG) (Y / D.nG) n * sel D t b (Y % D.nG) (Y / D.nG) n)
          (cat D.lT p.ti p.tg) := by
  rw [sumPhi_cube, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  show ∑ X ∈ range (2 ^ (D.lT + D.lg + D.ln)),
    Wb D C p .s16 b (cubePt (D.lT + D.lg + D.ln) X) * Acube D C p t .s16 b X *
      Bcube D C p t .s16 b X = _
  unfold Blocks.ext
  rw [pow_add, Alg.sum_range_mul_add, mul_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn' : n < 2 ^ D.ln := mem_range.mp hn
  have e := Dim.div_step (a := Y) (Nat.two_pow_pos D.ln) hn'
  have e3 : (Y * 2 ^ D.ln + n) / 2 ^ (D.lg + D.ln) = Y / 2 ^ D.lg := by
    rw [Nat.add_comm D.lg, pow_add, ← Nat.div_div_eq_div_mul, e.1]
  have w : Wb D C p .s16 b (cubePt (D.lT + D.lg + D.ln) (Y * 2 ^ D.ln + n)) =
      p.o b * eqN (D.lT + D.lg) 0 (cat D.lT p.ti p.tg) Y := by
    show p.o b * eqPt D.lg p.tg (sh (cubePt (D.lT + D.lg + D.ln) (Y * 2 ^ D.ln + n)) D.lT) *
        eqPt D.lT p.ti (cubePt (D.lT + D.lg + D.ln) (Y * 2 ^ D.ln + n)) = _
    rw [eqPt_vertex (g := D.lT + D.lg + D.ln) (n := D.lg) (X := Y * 2 ^ D.ln + n) (off := D.lT)
        (m := D.ln) p.tg (sh (cubePt (D.lT + D.lg + D.ln) (Y * 2 ^ D.ln + n)) D.lT) (by omega)
        (fun _ _ => rfl),
      eqPt_vertex (g := D.lT + D.lg + D.ln) (n := D.lT) (X := Y * 2 ^ D.ln + n) (off := 0)
        (m := D.lg + D.ln) p.ti (cubePt (D.lT + D.lg + D.ln) (Y * 2 ^ D.ln + n)) (by omega)
        (fun k _ => by rw [Nat.zero_add]),
      e.1, e3, eqN_cat]
    ring
  show Wb D C p .s16 b (cubePt (D.lT + D.lg + D.ln) (Y * 2 ^ D.ln + n)) *
      qryV t b ((Y * 2 ^ D.ln + n) / 2 ^ D.ln % D.nG) ((Y * 2 ^ D.ln + n) / 2 ^ D.ln / D.nG)
        ((Y * 2 ^ D.ln + n) % 2 ^ D.ln) *
      sel D t b ((Y * 2 ^ D.ln + n) / 2 ^ D.ln % D.nG) ((Y * 2 ^ D.ln + n) / 2 ^ D.ln / D.nG)
        ((Y * 2 ^ D.ln + n) % 2 ^ D.ln) =
    p.o b * (eqN (D.lT + D.lg) 0 (cat D.lT p.ti p.tg) Y *
      (qryV t b (Y % D.nG) (Y / D.nG) n * sel D t b (Y % D.nG) (Y / D.nG) n))
  rw [w, e.1, e.2]
  ring

/-- **ScoreMean holds.** -/
theorem scoreMean : ScoreMean := by
  intro E _ D C p t
  rw [sum16, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [show rvM6 D p t b = rd2 D p.tg (eqT D p.ti) (mxV t b) from rfl, rd2_ext, ← mul_sub,
    ← ext_sub]
  rfl

end Cb.Pv.Att

#print axioms Cb.Pv.Att.bitsMean
#print axioms Cb.Pv.Att.scoreMean

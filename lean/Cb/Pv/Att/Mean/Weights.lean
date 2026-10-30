-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/Weights.lean: the public weights of three sumchecks of an attention segment are
the multilinear extensions of their values on the cube.

The library writes the public weight of a step as a polynomial in the point (Wb in
Inst/Model/Att/Sums.lean). Cb/Pv/Att/Steps.lean, which puts the steps into the general sumcheck of
products, takes in its place the multilinear extension of the weight's values on the cube. On the
cube the two agree by definition. This file shows that they agree at every point, for the steps s12
and s16 and for the sumcheck for the bits with any number of bits that number a bit (bitWt in
Cb/Pv/Att/Bits.lean; at the library's number it is step s21).

Main theorems: wbExt12, wbExt16, bitWtExt, wbExt21.
Tools: ext_eqN (the extension of an equality vector is the equality polynomial of two points),
eqN_low, vertex_fst, vertex_snd, vertex_trd (the equality polynomials at a vertex of a cube in three
parts), sum3_factor, sum_eqN_one.

All of it is algebra on the library's definitions. Nothing is said about a verifier.


-/
import Cb.Pv.Att.Mean.Reads
import Blocks.ProductBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E]

/-! ## Tools -/

/-- The extension of the equality vector of a point u is the equality polynomial of u and the
point. -/
theorem ext_eqN (n : ℕ) (u ξ : ℕ → E) : Blocks.ext n (eqN n 0 u) ξ = eqPt n u ξ := by
  rw [Blocks.PL.ext_eq_mleN, Alg.mleN_eq_mle]
  have e : (fun b : Fin n → Bool => eqN n 0 u (Alg.num b)) =
      Alg.eqk (fun k : Fin n => u k) := by
    funext b
    rw [eqN_eq, Alg.eqN_num]
    simp only [Nat.zero_add]
  rw [e, Alg.mle_eqk]
  exact Fin.prod_univ_eq_prod_range (fun k => eq1 (u k) (ξ k)) n

/-- The same, written out. -/
theorem sum_eqN_eqN (n : ℕ) (u ξ : ℕ → E) :
    ∑ x ∈ range (2 ^ n), eqN n 0 ξ x * eqN n 0 u x = eqPt n u ξ := ext_eqN n u ξ

/-- The equality weights of a point add up to 1. -/
theorem sum_eqN_one (n : ℕ) (ξ : ℕ → E) : ∑ x ∈ range (2 ^ n), eqN n 0 ξ x = 1 := by
  have h := ext_const n (1 : E) ξ
  unfold Blocks.ext at h
  simpa using h

/-- The equality polynomial of a point of n coordinates reads the low n bits of the index. -/
theorem eqN_low (n : ℕ) (u : ℕ → E) (Y : ℕ) {z : ℕ} (hz : z < 2 ^ n) :
    eqN n 0 u (Y * 2 ^ n + z) = eqN n 0 u z := by
  have h := eqN_append' 0 n 0 u Y hz
  simp only [Nat.zero_add] at h
  have h0 : eqN 0 0 u Y = 1 := by simp [eqN]
  rw [h, h0, one_mul]

/-- A triple sum of products of three factors, one for each index. -/
theorem sum3_factor (s1 s2 s3 : Finset ℕ) (a b c : ℕ → E) :
    ∑ i ∈ s1, ∑ g ∈ s2, ∑ n ∈ s3, a i * b g * c n =
      (∑ i ∈ s1, a i) * (∑ g ∈ s2, b g) * ∑ n ∈ s3, c n := by
  rw [sum_mul_sum, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_mul_sum]

section Vertex
variable (a b c : ℕ) (u : ℕ → E) (x : ℕ) {y z : ℕ} (hy : y < 2 ^ b) (hz : z < 2 ^ c)

include hy hz in
/-- At the vertex (x | y | z): the equality polynomial on the first part. -/
theorem vertex_fst :
    eqPt a u (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z)) = eqN a 0 u x := by
  rw [eqPt_vertex (g := a + b + c) (n := a) (X := (x * 2 ^ b + y) * 2 ^ c + z) (off := 0)
    (m := b + c) u (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z)) (by omega)
    (fun k _ => by rw [Nat.zero_add])]
  have e1 := Dim.div_step (a := x * 2 ^ b + y) (Nat.two_pow_pos c) hz
  have e2 := Dim.div_step (a := x) (Nat.two_pow_pos b) hy
  rw [Nat.add_comm b, pow_add, ← Nat.div_div_eq_div_mul, e1.1, e2.1]

include hy hz in
/-- At the vertex (x | y | z): the equality polynomial on the second part. -/
theorem vertex_snd :
    eqPt b u (sh (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z)) a) = eqN b 0 u y := by
  rw [eqPt_vertex (g := a + b + c) (n := b) (X := (x * 2 ^ b + y) * 2 ^ c + z) (off := a)
    (m := c) u (sh (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z)) a) (by omega)
    (fun _ _ => rfl)]
  have e1 := Dim.div_step (a := x * 2 ^ b + y) (Nat.two_pow_pos c) hz
  rw [e1.1, eqN_low b u x hy]

include hz in
/-- At the vertex (x | y | z): the equality polynomial on the third part. -/
theorem vertex_trd :
    eqPt c u (sh (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z)) (a + b)) = eqN c 0 u z := by
  rw [eqPt_vertex (g := a + b + c) (n := c) (X := (x * 2 ^ b + y) * 2 ^ c + z) (off := a + b)
    (m := 0) u (sh (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z)) (a + b)) (by omega)
    (fun _ _ => rfl), pow_zero, Nat.div_one, eqN_low c u _ hz]

end Vertex

variable (D : Dim) (C : Calls) (p : Pub E)

/-! ## The score at the index -/

/-- **The weight of step s16 is the extension of its values on the cube.** -/
theorem wbExt16 (b : ℕ) (ξ : ℕ → E) :
    Blocks.ext (Step.s16.g D) (fun X => Wb D C p .s16 b (cubePt (Step.s16.g D) X)) ξ =
      Wb D C p .s16 b ξ := by
  show Blocks.ext (D.lT + D.lg + D.ln)
      (fun X => p.o b * eqPt D.lg p.tg (sh (cubePt (D.lT + D.lg + D.ln) X) D.lT) *
        eqPt D.lT p.ti (cubePt (D.lT + D.lg + D.ln) X)) ξ =
    p.o b * eqPt D.lg p.tg (sh ξ D.lT) * eqPt D.lT p.ti ξ
  rw [ext_three, ← sum_eqN_eqN D.lg p.tg (sh ξ D.lT), ← sum_eqN_eqN D.lT p.ti ξ]
  have s : ∀ i ∈ range (2 ^ D.lT), ∀ g ∈ range (2 ^ D.lg), ∀ n ∈ range (2 ^ D.ln),
      eqN D.lT 0 ξ i * eqN D.lg 0 (sh ξ D.lT) g * eqN D.ln 0 (sh ξ (D.lT + D.lg)) n *
          (p.o b * eqPt D.lg p.tg
            (sh (cubePt (D.lT + D.lg + D.ln) ((i * 2 ^ D.lg + g) * 2 ^ D.ln + n)) D.lT) *
            eqPt D.lT p.ti (cubePt (D.lT + D.lg + D.ln) ((i * 2 ^ D.lg + g) * 2 ^ D.ln + n))) =
        p.o b * (eqN D.lT 0 ξ i * eqN D.lT 0 p.ti i) *
          (eqN D.lg 0 (sh ξ D.lT) g * eqN D.lg 0 p.tg g) *
          eqN D.ln 0 (sh ξ (D.lT + D.lg)) n := by
    intro i _ g hg n hn
    rw [vertex_fst D.lT D.lg D.ln p.ti i (mem_range.mp hg) (mem_range.mp hn),
      vertex_snd D.lT D.lg D.ln p.tg i (mem_range.mp hg) (mem_range.mp hn)]
    ring
  rw [sum_congr rfl fun i hi => sum_congr rfl fun g hg => sum_congr rfl fun n hn =>
    s i hi g hg n hn, sum3_factor, sum_eqN_one, ← mul_sum]
  ring

/-! ## The bits of the index -/

/-- **The weight of the sumcheck for the bits is the extension of its values on the cube.** -/
theorem bitWtExt (kap b : ℕ) (ξ : ℕ → E) :
    Blocks.ext (D.lT + D.lg + kap) (fun X => bitWt kap D p b (cubePt (D.lT + D.lg + kap) X)) ξ =
      bitWt kap D p b ξ := by
  unfold bitWt
  rw [ext_three, ← sum_eqN_eqN D.lT p.tbi ξ, ← sum_eqN_eqN D.lg p.tbg (sh ξ D.lT),
    ← sum_eqN_eqN kap p.tk (sh ξ (D.lT + D.lg))]
  have s : ∀ i ∈ range (2 ^ D.lT), ∀ g ∈ range (2 ^ D.lg), ∀ k ∈ range (2 ^ kap),
      eqN D.lT 0 ξ i * eqN D.lg 0 (sh ξ D.lT) g * eqN kap 0 (sh ξ (D.lT + D.lg)) k *
          (p.o'' b *
            eqPt D.lT p.tbi (cubePt (D.lT + D.lg + kap) ((i * 2 ^ D.lg + g) * 2 ^ kap + k)) *
            eqPt D.lg p.tbg
              (sh (cubePt (D.lT + D.lg + kap) ((i * 2 ^ D.lg + g) * 2 ^ kap + k)) D.lT) *
            eqPt kap p.tk
              (sh (cubePt (D.lT + D.lg + kap) ((i * 2 ^ D.lg + g) * 2 ^ kap + k))
                (D.lT + D.lg))) =
        p.o'' b * (eqN D.lT 0 ξ i * eqN D.lT 0 p.tbi i) *
          (eqN D.lg 0 (sh ξ D.lT) g * eqN D.lg 0 p.tbg g) *
          (eqN kap 0 (sh ξ (D.lT + D.lg)) k * eqN kap 0 p.tk k) := by
    intro i _ g hg k hk
    rw [vertex_fst D.lT D.lg kap p.tbi i (mem_range.mp hg) (mem_range.mp hk),
      vertex_snd D.lT D.lg kap p.tbg i (mem_range.mp hg) (mem_range.mp hk),
      vertex_trd D.lT D.lg kap p.tk i (y := g) (mem_range.mp hk)]
    ring
  rw [sum_congr rfl fun i hi => sum_congr rfl fun g hg => sum_congr rfl fun k hk =>
    s i hi g hg k hk, sum3_factor, ← mul_sum]

/-- **The weight of step s21 is the extension of its values on the cube.** -/
theorem wbExt21 (b : ℕ) (ξ : ℕ → E) :
    Blocks.ext (Step.s21.g D) (fun X => Wb D C p .s21 b (cubePt (Step.s21.g D) X)) ξ =
      Wb D C p .s21 b ξ :=
  bitWtExt D p D.lK b ξ

/-! ## The value product on the diagonal tiles -/

/-- **The weight of step s12 is the extension of its values on the cube.** -/
theorem wbExt12 (b : ℕ) (ξ : ℕ → E) :
    Blocks.ext (Step.s12.g D) (fun X => Wb D C p .s12 b (cubePt (Step.s12.g D) X)) ξ =
      Wb D C p .s12 b ξ := by
  show Blocks.ext (D.lg + (D.lP + 1) + D.lB)
      (fun X => wp D C p.z .w3 b *
        eqPt D.lg (yg D C p.z) (cubePt (D.lg + (D.lP + 1) + D.lB) X) *
        eqPt (D.lP + 1) (yI D C p.z) (sh (cubePt (D.lg + (D.lP + 1) + D.lB) X) D.lg)) ξ =
    wp D C p.z .w3 b * eqPt D.lg (yg D C p.z) ξ * eqPt (D.lP + 1) (yI D C p.z) (sh ξ D.lg)
  rw [ext_three, ← sum_eqN_eqN D.lg (yg D C p.z) ξ,
    ← sum_eqN_eqN (D.lP + 1) (yI D C p.z) (sh ξ D.lg)]
  have s : ∀ g ∈ range (2 ^ D.lg), ∀ I ∈ range (2 ^ (D.lP + 1)), ∀ j ∈ range (2 ^ D.lB),
      eqN D.lg 0 ξ g * eqN (D.lP + 1) 0 (sh ξ D.lg) I *
          eqN D.lB 0 (sh ξ (D.lg + (D.lP + 1))) j *
          (wp D C p.z .w3 b *
            eqPt D.lg (yg D C p.z)
              (cubePt (D.lg + (D.lP + 1) + D.lB) ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j)) *
            eqPt (D.lP + 1) (yI D C p.z)
              (sh (cubePt (D.lg + (D.lP + 1) + D.lB) ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j))
                D.lg)) =
        wp D C p.z .w3 b * (eqN D.lg 0 ξ g * eqN D.lg 0 (yg D C p.z) g) *
          (eqN (D.lP + 1) 0 (sh ξ D.lg) I * eqN (D.lP + 1) 0 (yI D C p.z) I) *
          eqN D.lB 0 (sh ξ (D.lg + (D.lP + 1))) j := by
    intro g _ I hI j hj
    rw [vertex_fst D.lg (D.lP + 1) D.lB (yg D C p.z) g (mem_range.mp hI) (mem_range.mp hj),
      vertex_snd D.lg (D.lP + 1) D.lB (yI D C p.z) g (mem_range.mp hI) (mem_range.mp hj)]
    ring
  rw [sum_congr rfl fun g hg => sum_congr rfl fun I hI => sum_congr rfl fun j hj =>
    s g hg I hI j hj, sum3_factor, sum_eqN_one, ← mul_sum]
  ring

end Cb.Pv.Att

#print axioms Cb.Pv.Att.wbExt12
#print axioms Cb.Pv.Att.wbExt16
#print axioms Cb.Pv.Att.wbExt21
#print axioms Cb.Pv.Att.bitWtExt

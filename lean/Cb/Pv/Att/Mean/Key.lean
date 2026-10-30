-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/Key.lean: the sum of step 18 of an attention segment is the batch of the
keys at the index. A proof of KeyMean (Cb/Pv/Att/Mean/Means.lean).

Step 18 (Phi18 in Inst/Model/Att/Sums.lean) runs over the cube (key's position j | head g | query's
position i). At a vertex its three extensions are entries of arrays, because the parts of a vertex
are vertices (cube_fst, cube_snd, cube_trd, cube_two), and the coordinate of j that belongs to the
bit of weight 2^k is that bit (cube_bit). The second map of step s16 is the read of the library's
sel (bext16), which is a sum over j. What is left is to change the order of five sums.

Main theorems: ign_rd3, bext16, rd3_agree, phi18_vertex, keyMean.
Tools: testBit_low, testBit_high, cube_fst, cube_snd, cube_trd, cube_two_fst, cube_two_snd,
cube_bit, sum_rot4.

All of it is algebra on the library's definitions. Nothing is said about a verifier.


-/
import Cb.Pv.Att.Mean.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E]

/-! ## The parts of a vertex are vertices -/

/-- A low bit of Y 2^n + z is a bit of z. -/
theorem testBit_low (n Y : ℕ) {z k : ℕ} (hz : z < 2 ^ n) (hk : k < n) :
    (Y * 2 ^ n + z).testBit k = z.testBit k := by
  have e := (Dim.div_step (a := Y) (Nat.two_pow_pos n) hz).2
  have h := Nat.testBit_mod_two_pow (Y * 2 ^ n + z) n k
  rw [e] at h
  rw [h]
  simp [hk]

/-- A high bit of Y 2^n + z is a bit of Y. -/
theorem testBit_high (n Y : ℕ) {z : ℕ} (k : ℕ) (hz : z < 2 ^ n) :
    (Y * 2 ^ n + z).testBit (k + n) = Y.testBit k := by
  have e := (Dim.div_step (a := Y) (Nat.two_pow_pos n) hz).1
  rw [← Nat.testBit_div_two_pow, e]

/-- The first part of a vertex in two parts. -/
theorem cube_two_fst (a b x : ℕ) {y k : ℕ} (hy : y < 2 ^ b) (hk : k < a) :
    (cubePt (a + b) (x * 2 ^ b + y) : ℕ → E) k = cubePt a x k := by
  rw [cubePt_at _ _ _ (by omega), cubePt_at _ _ _ hk,
    show a + b - 1 - k = a - 1 - k + b by omega, testBit_high b x _ hy]

/-- The second part of a vertex in two parts. -/
theorem cube_two_snd (a b x : ℕ) {y k : ℕ} (hy : y < 2 ^ b) (hk : k < b) :
    (cubePt (a + b) (x * 2 ^ b + y) : ℕ → E) (a + k) = cubePt b y k := by
  rw [cubePt_at _ _ _ (by omega), cubePt_at _ _ _ hk,
    show a + b - 1 - (a + k) = b - 1 - k by omega, testBit_low b x hy (by omega)]

section Three
variable (a b c x : ℕ) {y z k : ℕ} (hy : y < 2 ^ b) (hz : z < 2 ^ c)

include hy hz in
/-- The first part of a vertex in three parts. -/
theorem cube_fst (hk : k < a) :
    (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z) : ℕ → E) k = cubePt a x k := by
  rw [cube_two_fst (a + b) c _ hz (by omega), cube_two_fst a b x hy hk]

include hy hz in
/-- The second part of a vertex in three parts. -/
theorem cube_snd (hk : k < b) :
    (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z) : ℕ → E) (a + k) = cubePt b y k := by
  rw [cube_two_fst (a + b) c _ hz (by omega), cube_two_snd a b x hy hk]

include hz in
/-- The third part of a vertex in three parts. -/
theorem cube_trd (hk : k < c) :
    (cubePt (a + b + c) ((x * 2 ^ b + y) * 2 ^ c + z) : ℕ → E) (a + b + k) = cubePt c z k :=
  cube_two_snd (a + b) c _ hz hk

end Three

/-- The coordinate of a vertex that belongs to the bit of weight 2^k is that bit. -/
theorem cube_bit (n j : ℕ) {k : ℕ} (hk : k < n) :
    (cubePt n j : ℕ → E) (n - 1 - k) = bitR E k j := by
  rw [cubePt_at _ _ _ (by omega), show n - 1 - (n - 1 - k) = k by omega]
  rfl

/-- Four sums, the first index last and the last first. -/
theorem sum_rot4 (A B C' D' : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → E) :
    ∑ j ∈ A, ∑ g ∈ B, ∑ i ∈ C', ∑ b ∈ D', f j g i b =
      ∑ b ∈ D', ∑ g ∈ B, ∑ i ∈ C', ∑ j ∈ A, f j g i b := by
  calc ∑ j ∈ A, ∑ g ∈ B, ∑ i ∈ C', ∑ b ∈ D', f j g i b
      = ∑ j ∈ A, ∑ g ∈ B, ∑ b ∈ D', ∑ i ∈ C', f j g i b :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ j ∈ A, ∑ b ∈ D', ∑ g ∈ B, ∑ i ∈ C', f j g i b :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ b ∈ D', ∑ j ∈ A, ∑ g ∈ B, ∑ i ∈ C', f j g i b := sum_comm
    _ = ∑ b ∈ D', ∑ g ∈ B, ∑ j ∈ A, ∑ i ∈ C', f j g i b :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ b ∈ D', ∑ g ∈ B, ∑ i ∈ C', ∑ j ∈ A, f j g i b :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm

variable (D : Dim)

/-! ## Reads -/

/-- The extension of an array over the cube (i | g | n) is the read of the array. -/
theorem ign_rd3 (a : ℕ → ℕ → ℕ → E) (ξ : ℕ → E) :
    Blocks.ext (D.lT + D.lg + D.ln)
        (fun X => a (X / 2 ^ D.ln % 2 ^ D.lg) (X / 2 ^ D.ln / 2 ^ D.lg) (X % 2 ^ D.ln)) ξ =
      rd3 D (sh ξ D.lT) (eqT D ξ) (sh ξ (D.lT + D.lg)) a := by
  rw [ext_three, sum_comm]
  unfold rd3 eqT
  rw [D.T_eq]
  refine sum_congr rfl fun g hg => sum_congr rfl fun i _ => sum_congr rfl fun n hn => ?_
  have e1 := Dim.div_step (a := i * 2 ^ D.lg + g) (Nat.two_pow_pos D.ln) (mem_range.mp hn)
  have e2 := Dim.div_step (a := i) (Nat.two_pow_pos D.lg) (mem_range.mp hg)
  simp only [e1.1, e1.2, e2.1, e2.2]
  ring

/-- Two reads agree if their points agree on the coordinates that are read. -/
theorem rd3_agree {vg vg' vi vi' vn vn' : ℕ → E} (hg : ∀ k < D.lg, vg k = vg' k)
    (hi : ∀ k < D.lT, vi k = vi' k) (hn : ∀ k < D.ln, vn k = vn' k) (a : ℕ → ℕ → ℕ → E) :
    rd3 D vg (eqT D vi) vn a = rd3 D vg' (eqT D vi') vn' a := by
  unfold rd3 eqT
  refine sum_congr rfl fun g _ => sum_congr rfl fun i _ => sum_congr rfl fun n _ => ?_
  rw [eqN_agree (a := vg) (a' := vg') (off := 0) (off' := 0)
      (fun k hk => by rw [Nat.zero_add]; exact hg k hk) g,
    eqN_agree (a := vi) (a' := vi') (off := 0) (off' := 0)
      (fun k hk => by rw [Nat.zero_add]; exact hi k hk) i,
    eqN_agree (a := vn) (a' := vn') (off := 0) (off' := 0)
      (fun k hk => by rw [Nat.zero_add]; exact hn k hk) n]

variable (C : Calls) (p : Pub E) (t : Raw → E)

/-- **The second map of step s16 is the read of the key at the index.** -/
theorem bext16 (b : ℕ) (ξ : ℕ → E) :
    Bext D C p t .s16 b ξ = rd3 D (sh ξ D.lT) (eqT D ξ) (sh ξ (D.lT + D.lg)) (sel D t b) :=
  ign_rd3 D (sel D t b) ξ

/-! ## Step 18 at a vertex -/

/-- **The summand of step 18 at the vertex (j | g | i).** -/
theorem phi18_vertex {j g i : ℕ} (hj : j < 2 ^ D.lT) (hg : g < 2 ^ D.lg) (hi : i < 2 ^ D.lT) :
    Phi18 D p t (cubePt (D.lT + D.lg + D.lT) ((j * 2 ^ D.lg + g) * 2 ^ D.lT + i)) =
      eqN D.lT 0 p.fi i * eqN D.lg 0 p.fg g *
        ∑ b ∈ range D.nb, p.o' b * conN D p.fn (fun n => keyV t (D.lamOf b) g j n) *
          ∏ k ∈ range D.lT, eq1 (ibV t k b g i) (bitR E k j) := by
  have eT := D.T_eq
  have dj := Dim.div_step (a := g) (Nat.two_pow_pos D.lT) hj
  have di := Dim.div_step (a := g) (Nat.two_pow_pos D.lT) hi
  unfold Phi18
  rw [vertex_trd D.lT D.lg D.lT p.fi j (y := g) hi, vertex_snd D.lT D.lg D.lT p.fg j hg hi]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  have k1 : Blocks.ext (D.lg + D.lT) (kc D p t (D.lamOf b))
      (cat D.lg (sh (cubePt (D.lT + D.lg + D.lT) ((j * 2 ^ D.lg + g) * 2 ^ D.lT + i)) D.lT)
        (cubePt (D.lT + D.lg + D.lT) ((j * 2 ^ D.lg + g) * 2 ^ D.lT + i))) =
      conN D p.fn (fun n => keyV t (D.lamOf b) g j n) := by
    rw [ext_congr_point (z' := cubePt (D.lg + D.lT) (g * 2 ^ D.lT + j)) (fun k hk => ?_),
      ext_cubePt _ _ (by
        rw [pow_add]
        calc g * 2 ^ D.lT + j < g * 2 ^ D.lT + 2 ^ D.lT := by omega
          _ = (g + 1) * 2 ^ D.lT := by ring
          _ ≤ 2 ^ D.lg * 2 ^ D.lT := Nat.mul_le_mul_right _ hg)]
    · unfold kc
      rw [eT, dj.1, dj.2]
    · by_cases h1 : k < D.lg
      · show (if k < D.lg then _ else _) = _
        rw [if_pos h1, cube_two_fst D.lg D.lT g hj h1]
        exact cube_snd D.lT D.lg D.lT j hg hi h1
      · show (if k < D.lg then _ else _) = _
        rw [if_neg h1]
        have e : k = D.lg + (k - D.lg) := by omega
        rw [cube_fst D.lT D.lg D.lT j hg hi (by omega)]
        conv_rhs => rw [e]
        rw [cube_two_snd D.lg D.lT g hj (by omega)]
  have k2 : ∀ k, Blocks.ext (D.lg + D.lT) (fun X => ibV t k b (X / D.T) (X % D.T))
      (sh (cubePt (D.lT + D.lg + D.lT) ((j * 2 ^ D.lg + g) * 2 ^ D.lT + i)) D.lT) =
      ibV t k b g i := by
    intro k
    rw [ext_congr_point (z' := cubePt (D.lg + D.lT) (g * 2 ^ D.lT + i)) (fun q hq => ?_),
      ext_cubePt _ _ (by
        rw [pow_add]
        calc g * 2 ^ D.lT + i < g * 2 ^ D.lT + 2 ^ D.lT := by omega
          _ = (g + 1) * 2 ^ D.lT := by ring
          _ ≤ 2 ^ D.lg * 2 ^ D.lT := Nat.mul_le_mul_right _ hg)]
    · rw [eT, di.1, di.2]
    · show cubePt (D.lT + D.lg + D.lT) ((j * 2 ^ D.lg + g) * 2 ^ D.lT + i) (D.lT + q) = _
      by_cases h1 : q < D.lg
      · rw [cube_snd D.lT D.lg D.lT j hg hi h1, cube_two_fst D.lg D.lT g hi h1]
      · have e : q = D.lg + (q - D.lg) := by omega
        have e' : D.lT + q = D.lT + D.lg + (q - D.lg) := by omega
        rw [e', cube_trd D.lT D.lg D.lT j (y := g) hi (by omega)]
        conv_rhs => rw [e]
        rw [cube_two_snd D.lg D.lT g hi (by omega)]
  rw [k1]
  congr 1
  refine prod_congr rfl fun k hk => ?_
  rw [k2 k, cube_fst D.lT D.lg D.lT j hg hi (by have := mem_range.mp hk; omega),
    cube_bit D.lT j (mem_range.mp hk)]

/-! ## The sum -/

/-- **KeyMean holds.** -/
theorem keyMean : KeyMean := by
  intro E _ D C p t
  show ∑ X ∈ range (2 ^ (D.lT + D.lg + D.lT)),
    Phi18 D p t (cubePt (D.lT + D.lg + D.lT) X) = _
  rw [pow_add, Alg.sum_range_mul_add, pow_add, Alg.sum_range_mul_add]
  have l1 : ∀ j ∈ range (2 ^ D.lT), ∀ g ∈ range (2 ^ D.lg), ∀ i ∈ range (2 ^ D.lT),
      Phi18 D p t (cubePt (D.lT + D.lg + D.lT) ((j * 2 ^ D.lg + g) * 2 ^ D.lT + i)) =
        ∑ b ∈ range D.nb, p.o' b * (eqN D.lg 0 p.fg g * eqN D.lT 0 p.fi i *
          (conN D p.fn (fun n => keyV t (D.lamOf b) g j n) *
            ∏ k ∈ range D.lT, eq1 (ibV t k b g i) (bitR E k j))) := by
    intro j hj g hg i hi
    rw [phi18_vertex D p t (mem_range.mp hj) (mem_range.mp hg) (mem_range.mp hi), mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [sum_congr rfl fun j hj => sum_congr rfl fun g hg => sum_congr rfl fun i hi =>
    l1 j hj g hg i hi, sum_rot4]
  refine sum_congr rfl fun b _ => ?_
  rw [bext16, rd3_agree D (vg' := p.fg) (vi' := p.fi) (vn' := p.fn)
    (fun k hk => by
      show cat D.lT p.fi (cat D.lg p.fg p.fn) (D.lT + k) = p.fg k
      have e1 : ¬ D.lT + k < D.lT := by omega
      have e2 : D.lT + k - D.lT = k := by omega
      simp only [cat, if_neg e1, e2, if_pos hk])
    (fun k hk => by simp only [cat, if_pos hk])
    (fun k _ => by
      show cat D.lT p.fi (cat D.lg p.fg p.fn) (D.lT + D.lg + k) = p.fn k
      have e1 : ¬ D.lT + D.lg + k < D.lT := by omega
      have e2 : D.lT + D.lg + k - D.lT = D.lg + k := by omega
      have e3 : ¬ D.lg + k < D.lg := by omega
      have e4 : D.lg + k - D.lg = k := by omega
      simp only [cat, if_neg e1, e2, if_neg e3, e4])]
  unfold rd3 eqT
  rw [D.T_eq, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  unfold sel conN
  rw [D.T_eq]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun n _ => sum_congr rfl fun j _ => by ring

end Cb.Pv.Att

#print axioms Cb.Pv.Att.bext16
#print axioms Cb.Pv.Att.phi18_vertex
#print axioms Cb.Pv.Att.keyMean

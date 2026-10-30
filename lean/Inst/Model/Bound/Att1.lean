-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Bound/Att1.lean: no wrap-around in an attention segment, first half, at a variable number
p.

"No wrap-around": what holds modulo p of the cells' small integers is shown to hold over the
integers. All theorems are under `h : IntRel D tb p t` (Inst/Model/Att/NoWrap0.lean): the segment's
field relation over `ZMod p`, said over the integers. The steps that read the modulus are here, in
the namespace `Cm.TI`, for a variable number p with `Big p` (Inst/Model/Bound/Base.lean; that p is
prime is not assumed); the others are in Inst/Model/Att/NoWrap1.lean.

Main names:
  `half1`: under the hypotheses of its statement, `Half1 D t b` (Inst/Model/Att/NoWrap0.lean): the
    facts (FA1), (FA2), (FA5), (FA6), over the integers, for one pair b of a layer and the number
    of a query head among those of its key/value head (all key/value heads g).

Why: each step "p divides a - b and |a - b| < 2^61 - 1, so a = b" is by `Cm.TI.eq_of_dvd` or, in
`step_fa1` and `step_fa2`, by `Cm.TI.mul_big`; the bound of both is the numeral 2^61 - 1.

Limits: for what each name is and under which hypotheses each step is stated, see the head of
Inst/Model/Att/NoWrap1.lean. (The limits on the prime: the head of Inst/Model/Bound/Base.lean.)
Terms: lean/GLOSSARY.md.
-/
import Inst.Model.Att.NoWrap1
import Inst.Model.Bound.Base


set_option autoImplicit false

namespace Cm.TI.AttSeg

open Inst.Model Inst.Model.AttSeg

variable {p : ℕ} [Big p]

open Finset

/-! ## Steps A1, A2 and A4 (Step A3, `step_fa5`: Inst/Model/Att/NoWrap1.lean) -/

section Steps
variable [scl : Scl]
variable {D : Dim} {tb : Tables} {t : Raw → ℤ} (h : IntRel D tb p t)
include h

/-- Under the hypotheses of its statement. **Step A1, (FA1)**: at every place of both regions the
remainder is below 2^16, and the flag says whether it is at least 2^sh (the paper: 2^8). -/
theorem step_fa1 {ρ : Reg} {b x : ℕ} (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    0 ≤ rm t ρ b x ∧
    rm t ρ b x < 2 ^ 16 ∧
    flV t ρ b x = if 2 ^ D.sh ≤ rm t ρ b x then 1 else 0 := by
  obtain ⟨ι, hι, k, hk⟩ := h.k1 ρ b x hb hx
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, _⟩ := h.place_abs hb hx
  simp only [key1, tau1] at hk
  have hf : ∃ f : ℤ, (f = if 2 ^ D.sh ≤ ι then 1 else 0) ∧
      (if 2 ^ D.sh ≤ ι then (2 ^ 40 : ℤ) else 0) = 2 ^ 40 * f ∧ 0 ≤ f ∧ f ≤ 1 := by
    by_cases h8 : 2 ^ D.sh ≤ ι
    · exact ⟨1, by rw [if_pos h8], by rw [if_pos h8, mul_one], by norm_num, le_rfl⟩
    · exact ⟨0, by rw [if_neg h8], by rw [if_neg h8, mul_zero], le_rfl, by norm_num⟩
  obtain ⟨f, hfd, hfe, hf0, hf1⟩ := hf
  rw [hfe] at hk
  have he0 : (0 : ℤ) ≤ ((ι % 256 : ℕ) : ℤ) ∧ ((ι % 256 : ℕ) : ℤ) ≤ 255 := by omega
  have he1 : (0 : ℤ) ≤ ((ι / 256 : ℕ) : ℤ) ∧ ((ι / 256 : ℕ) : ℤ) ≤ 255 := by omega
  have hιe : ((ι % 256 : ℕ) : ℤ) + 256 * ((ι / 256 : ℕ) : ℤ) = (ι : ℤ) := by omega
  generalize ((ι % 256 : ℕ) : ℤ) = e0 at hk he0 hιe
  generalize ((ι / 256 : ℕ) : ℤ) = e1 at hk he1 hιe
  have hk0 : k = 0 := by
    rcases mul_big p k with h0 | h0 | h0
    · exact h0
    all_goals (exfalso; generalize (p : ℤ) * k = z at hk h0; omega)
  subst hk0
  obtain ⟨s1, s2⟩ := NW.split2 (k := 20) (a0 := r0 t ρ b x)
    (a1 := r1 t ρ b x + 2 ^ 20 * flV t ρ b x) (e0 := e0) (e1 := e1 + 2 ^ 20 * f)
    (by linarith) (by rw [abs_lt]; constructor <;> omega)
  obtain ⟨s3, s4⟩ := NW.split2 (k := 20) s2 (by rw [abs_lt]; constructor <;> omega)
  have hrm : rm t ρ b x = (ι : ℤ) ∧ flV t ρ b x = if 2 ^ D.sh ≤ ι then 1 else 0 := by
    unfold rm
    rw [s1, s3, s4, hfd]
    exact ⟨hιe, rfl⟩
  rw [hrm.1, hrm.2]
  refine ⟨by omega, by omega, ?_⟩
  by_cases h8 : 2 ^ D.sh ≤ ι
  · rw [if_pos h8, if_pos (by exact_mod_cast h8)]
  · rw [if_neg h8, if_neg (by exact_mod_cast h8)]

/-- Step A1, (FA2): the two bytes of the division. -/
theorem step_fa2 {b g i n : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    (0 ≤ qhV t b g i n ∧ qhV t b g i n ≤ 255) ∧ (0 ≤ qhV' t b g i n ∧ qhV' t b g i n ≤ 255) := by
  obtain ⟨ι, hι, k, hk⟩ := h.k4 b g i n hb hg hi hn
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := h.qhV_abs hb hg hi hn
  simp only [key4, tau4] at hk
  have he0 : (0 : ℤ) ≤ ((ι % 256 : ℕ) : ℤ) ∧ ((ι % 256 : ℕ) : ℤ) ≤ 255 := by omega
  have he1 : (0 : ℤ) ≤ ((ι / 256 : ℕ) : ℤ) ∧ ((ι / 256 : ℕ) : ℤ) ≤ 255 := by omega
  generalize ((ι % 256 : ℕ) : ℤ) = e0 at hk he0
  generalize ((ι / 256 : ℕ) : ℤ) = e1 at hk he1
  have hk0 : k = 0 := by
    rcases mul_big p k with h0 | h0 | h0
    · exact h0
    all_goals (exfalso; generalize (p : ℤ) * k = z at hk h0; omega)
  subst hk0
  obtain ⟨s1, s2⟩ := NW.split2 (k := 20) (a0 := qhV t b g i n) (a1 := qhV' t b g i n) (e0 := e0)
    (e1 := e1) (by linarith) (by rw [abs_lt]; constructor <;> omega)
  rw [s1, s2]
  exact ⟨he0, he1⟩

/-- Step A2, (FA3), under the hypotheses of its statement: the cells of the index are bits. -/
theorem step_fa3 {k b g i : ℕ} (hk : k < D.lT) (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) :
    ibV t k b g i = 0 ∨ ibV t k b g i = 1 := by
  have hd := h.at1 k b g i hk hb hg hi
  obtain ⟨a1, a2⟩ := h.ibV_abs hk hb hg hi
  have h0 : ibV t k b g i * (ibV t k b g i - 1) = 0 := by
    refine eq_of_dvd (by rw [sub_zero]; exact hd) ?_
    rw [sub_zero, abs_lt]
    constructor <;> nlinarith
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by omega)

theorem jst_lt {b g i : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) :
    jst D t b g i < D.T := by
  rw [D.T_eq]
  exact Bits.num_lt D.lT fun k hk => step_fa3 h hk hb hg hi

/-- Step A2, (FA4), under the hypotheses of its statement: j* ≤ i. -/
theorem step_fa4 (hlT : D.lT ≤ 10) {b g i : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) :
    jst D t b g i ≤ i := by
  obtain ⟨ι, hι, hd⟩ := h.k3X b g i hb hg hi
  have hj := jst_lt h hb hg hi
  have hT : D.T ≤ 2 ^ 10 := by rw [D.T_eq]; exact Nat.pow_le_pow_right (by norm_num) hlT
  have hc := Bits.cast_num (u := fun k => ibV t k b g i) D.lT fun k hk => step_fa3 h hk hb hg hi
  unfold key3X at hd
  rw [← hc, ← jst_def] at hd
  have hc1 : (0 : ℤ) < 2 ^ (16 - D.lT) := by positivity
  have hc2 : (2 : ℤ) ^ (16 - D.lT) ≤ 2 ^ 16 := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  generalize (2 : ℤ) ^ (16 - D.lT) = c at hd hc1 hc2
  have hi' : (i : ℤ) < 1024 := by exact_mod_cast lt_of_lt_of_le hi hT
  have hj' : ((jst D t b g i : ℕ) : ℤ) < 1024 := by exact_mod_cast lt_of_lt_of_le hj hT
  have hi0 : (0 : ℤ) ≤ i := Int.natCast_nonneg _
  have hj0 : (0 : ℤ) ≤ (jst D t b g i : ℕ) := Int.natCast_nonneg _
  have hι' : ((ι : ℕ) : ℤ) < 65536 := by exact_mod_cast hι
  have hι0 : (0 : ℤ) ≤ (ι : ℕ) := Int.natCast_nonneg _
  have he : c * ((i : ℤ) - (jst D t b g i : ℕ)) = (ι : ℕ) := by
    refine eq_of_dvd hd ?_
    rw [abs_lt]
    norm_num at hc2
    constructor <;> nlinarith
  by_contra hlt
  have hlt' : (i : ℤ) - (jst D t b g i : ℕ) ≤ -1 := by
    have : (i : ℤ) < (jst D t b g i : ℕ) := by exact_mod_cast Nat.lt_of_not_le hlt
    omega
  nlinarith

/-- Under the hypotheses of its statement, the key that the bits select is the key at j*. -/
theorem sel_eq {b g i : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) (n : ℕ) :
    sel D t b g i n = keyV t (D.lamOf b) g (jst D t b g i) n := by
  unfold sel
  have hbits : ∀ k < D.lT, ibV t k b g i = 0 ∨ ibV t k b g i = 1 := fun k hk =>
    step_fa3 h hk hb hg hi
  rw [sum_congr rfl fun j hj => by
    rw [Bits.prod_eq1 (u := fun k => ibV t k b g i) D.lT hbits
          (by rw [← D.T_eq]; exact mem_range.mp hj), ← jst_def]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq' , if_pos (mem_range.mpr (jst_lt h hb hg hi))]

/-- Step A4, (FA6), under the hypotheses of its statement: mx (the cells for the greatest score) is
the score at j*. -/
theorem step_fa6 (hch : D.ch ≤ 128) {b : ℕ} (hin : InB D t b) {g i : ℕ} (hb : b < D.nb)
    (hg : g < D.nG) (hi : i < D.T) :
    mxV t b g i = scV D t b g i (jst D t b g i) := by
  have hd := h.at2 b g i hb hg hi
  have hs : (∑ n ∈ range D.ch, qryV t b g i n * sel D t b g i n) =
      scV D t b g i (jst D t b g i) := by
    unfold scV
    exact sum_congr rfl fun n _ => by rw [sel_eq h hb hg hi n]
  rw [hs] at hd
  have h1 := abs_le.mp (h.mxV_abs hb hg hi)
  have h2 := abs_le.mp (step_fa5 hch hin hg hi (jst_lt h hb hg hi))
  unfold Smax at h2
  refine eq_of_dvd hd ?_
  rw [abs_lt]
  constructor <;> omega

end Steps

/-- **Steps A1 to A4 of Lemma S15.7**, for one pair b of a layer and a query head: (FA1), (FA2),
(FA5), (FA6). (b: a layer and the number of a query head among those of its key/value head:
`Dim.nb`, Inst/Model/Att/Index.lean.) -/
theorem half1 [scl : Scl] {D : Dim} {tb : Tables} {t : Raw → ℤ} (h : IntRel D tb p t)
    (hch : D.ch ≤ 128) (hlT : D.lT ≤ 10) {b : ℕ} (hb : b < D.nb) (hin : InB D t b) :
    Half1 D t b where
  fa1 := fun _ _ hx => step_fa1 h hb hx
  fa2 := fun _ _ _ hg hi hn => step_fa2 h hb hg hi hn
  fa5 := fun _ _ _ hg hi hj => step_fa5 hch hin hg hi hj
  fa6 := fun g i hg hi => ⟨jst D t b g i, step_fa4 h hlT hb hg hi, step_fa6 h hch hin hb hg hi⟩

end Cm.TI.AttSeg

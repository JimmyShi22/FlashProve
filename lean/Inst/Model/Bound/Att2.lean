-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Bound/Att2.lean: no wrap-around in an attention segment, second half, at a variable
number p.

"No wrap-around": what holds modulo p of the cells' small integers is shown to hold over the
integers. The steps that read the modulus are here, in the namespace `Cm.TI`, for a variable number
p with `Big p` (Inst/Model/Bound/Base.lean; that p is prime is not assumed); the others are in
Inst/Model/Att/NoWrap2.lean.

Main names:
  `NW2.out_link`: under the hypotheses of its statement, among them `IntRel D tb p t` (the
    segment's field relation over `ZMod p`, said over the integers), `Half1 D t b` and `InputsAre`
    (the cells hold the program's inputs of a layer): out holds the output of the program
    (Inst/Model/Program.lean).
  `NW2.fa12`: see its docstring.
The theorems of Parts 2 to 4 are under `hO`, `hE`, `h : IntRel D tb p t`, `H : Half1 D t b`, `hb`
(the `variable` lines).

Why: each step "p divides a - b and |a - b| < 2^61 - 1, so a = b" is by `Cm.TI.eq_of_dvd`, whose
bound is the numeral 2^61 - 1.

Limits: for what each name is and under which hypotheses each step is stated, see the head of
Inst/Model/Att/NoWrap2.lean. (The limits on the prime: the head of Inst/Model/Bound/Base.lean.)
Terms: lean/GLOSSARY.md.
-/
import Inst.Model.Att.NoWrap2
import Inst.Model.Bound.Att1


set_option autoImplicit false

namespace Cm.TI.AttSeg

open Inst.Model Inst.Model.AttSeg

variable {p : ℕ} [Big p]

open Finset

namespace NW2
open Inst.Model.AttSeg.NW2

/-! ## Part 1. The three steps on bare integers -/

/-- Step A5 at one place. gp: the extended gap; rm, fl: remainder and flag, as Step A1 leaves them;
wt: the weight, of which only the bound of two cells is known. -/
theorem stepA5 {sh u0 : ℕ} (hO : ExpOK sh u0) {tb : Tables}
    (hE : ∀ u : ℕ, u < u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12) {gp rm fl wt : ℤ} (hr0 : 0 ≤ rm)
    (hr1 : rm < 2 ^ 16) (hfl : fl = if 2 ^ sh ≤ rm then 1 else 0) (hg0 : -1072693504 ≤ gp)
    (hg1 : gp ≤ 2145387008 + cutC sh u0) (hw : |wt| ≤ 67370879) {ι : ℕ} (hι : ι < 2 ^ 16)
    (hk : (p : ℤ) ∣ gp - rm + 2 ^ 32 * fl + 2 ^ 33 * wt - (tau2 sh u0 tb).row ι) :
    0 ≤ gp ∧ (gp < cutC sh u0 → wt = tb.Exp (gp / 2 ^ sh)) ∧ (cutC sh u0 ≤ gp → wt = 0) ∧
    0 ≤ wt ∧ wt ≤ 2 ^ 12 := by
  obtain ⟨e1, f, v, hrow, hc⟩ := tau2_row hO hE hι
  obtain ⟨hw0, hw1⟩ := abs_le.mp hw
  obtain ⟨s0, s1⟩ := un_bounds hO
  obtain ⟨c0, c1⟩ := cutC_bounds hO
  have hCs := un_le_cutC hO
  have hS : Smax = 536346752 := by norm_num [Smax]
  have hfl01 : fl = 0 ∨ fl = 1 := by
    rw [hfl]; split_ifs <;> simp
  -- a live row begins at least one step below the cut-off
  have hlive : ι < u0 →
      (0 : ℤ) ≤ 2 ^ sh * ι ∧ (2 : ℤ) ^ sh * ι + 2 ^ sh ≤ cutC sh u0 := fun h1 => by
    refine ⟨by positivity, ?_⟩
    have : (2 : ℤ) ^ sh * ((ι : ℤ) + 1) ≤ 2 ^ sh * u0 :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h1) (by positivity)
    unfold cutC
    linarith
  have hb : 0 ≤ e1 ∧ e1 ≤ cutC sh u0 + 4 * Smax + 2 ^ 15 ∧ (f = 0 ∨ f = 1) ∧ 0 ≤ v ∧ v ≤ 4096 := by
    rcases hc with ⟨h1, h2, h3, -, h5, h6⟩ | ⟨h1, h2, h3, h4⟩
    · obtain ⟨l0, l1⟩ := hlive h1
      refine ⟨by omega, by omega, Or.inl h3, by omega, by omega⟩
    · refine ⟨by omega, h4, Or.inr h1, by omega, by omega⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  have heq : gp - rm + 2 ^ 32 * fl + 2 ^ 33 * wt = (tau2 sh u0 tb).row ι := by
    refine eq_of_dvd hk ?_
    rw [hrow, abs_lt]
    constructor <;> rcases hfl01 with h | h <;> rcases b3 with h' | h' <;> subst h h' <;> omega
  rw [hrow] at heq
  have hX : gp - rm = e1 ∧ fl = f ∧ wt = v := by
    rcases hfl01 with h | h <;> rcases b3 with h' | h' <;> subst h h' <;> omega
  obtain ⟨x1, x2, x3⟩ := hX
  rcases hc with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4⟩
  · -- a live row
    obtain ⟨l0, l1⟩ := hlive h1
    have hr8 : rm < 2 ^ sh := by
      by_contra hcon
      rw [if_pos (not_lt.mp hcon)] at hfl
      omega
    have hq : gp / 2 ^ sh = (ι : ℤ) :=
      ((Int.ediv_emod_unique (by positivity : (0 : ℤ) < 2 ^ sh)).2
        ⟨by rw [← h2]; omega, hr0, hr8⟩).1
    refine ⟨by omega, fun _ => by rw [hq, x3, h4], fun hge => by omega, by omega, by omega⟩
  · -- a dead row
    have hr8 : 2 ^ sh ≤ rm := by
      by_contra hcon
      rw [if_neg hcon] at hfl
      omega
    refine ⟨by omega, fun hlt => by omega, fun _ => by omega, by omega, by omega⟩

/-- Step A6, the equality, under the hypotheses of its statement: the denominator, a value of four
cells, is the sum of the weights. -/
theorem stepA6 {den EF : ℤ} (hd : |den| ≤ 4415276908287) (h0 : 0 ≤ EF)
    (h1 : EF ≤ 2 ^ 22) (hk : (p : ℤ) ∣ den - EF) : den = EF := by
  obtain ⟨a, b⟩ := abs_le.mp hd
  refine eq_of_dvd hk ?_
  rw [abs_lt]
  constructor <;> omega

/-- Step A7. AC, den: numerator and denominator, as Step A6 leaves them; out: a value of two cells;
qh, qh': as Step A1 leaves them; e0, e1: rows of τ3. -/
theorem stepA7 {AC den out qh qh' : ℤ} {e0 e1 : ℕ} (hd0 : 2 ^ 12 ≤ den) (hd1 : den ≤ 2 ^ 22)
    (hA : |AC| ≤ 2047 * den) (ho : |out| ≤ 67370751) (hq : 0 ≤ qh ∧ qh ≤ 255)
    (hq' : 0 ≤ qh' ∧ qh' ≤ 255) (he0 : e0 < 2 ^ 16) (he1 : e1 < 2 ^ 16)
    (hk0 : (p : ℤ) ∣ (2 * AC + den - 2 * den * out) - 2 ^ 16 * qh - (e0 : ℕ))
    (hk1 : (p : ℤ) ∣ 2 * den - 1 - (2 * AC + den - 2 * den * out) - 2 ^ 16 * qh' - (e1 : ℕ)) :
    out = (2 * AC + den) / (2 * den) ∧ |out| ≤ 2047 := by
  obtain ⟨a0, a1⟩ := abs_le.mp hA
  obtain ⟨o0, o1⟩ := abs_le.mp ho
  -- the one product in which a factor has only the bound of its cells
  have hp : |den * out| ≤ 2 ^ 22 * 67370751 := by
    rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ den)]
    exact mul_le_mul hd1 ho (abs_nonneg _) (by norm_num)
  obtain ⟨p0, p1⟩ := abs_le.mp hp
  generalize hP : den * out = P at *
  have hP2 : 2 * den * out = 2 * P := by rw [← hP]; ring
  rw [hP2] at hk0 hk1
  have hA1 : AC ≤ 2047 * 2 ^ 22 := by omega
  have hA0 : -(2047 * 2 ^ 22) ≤ AC := by omega
  have E0 : (2 * AC + den - 2 * P) - 2 ^ 16 * qh = (e0 : ℕ) := by
    refine eq_of_dvd hk0 ?_
    rw [abs_lt]
    constructor <;> omega
  have E1 : 2 * den - 1 - (2 * AC + den - 2 * P) - 2 ^ 16 * qh' = (e1 : ℕ) := by
    refine eq_of_dvd hk1 ?_
    rw [abs_lt]
    constructor <;> omega
  have R0 : 0 ≤ 2 * AC + den - 2 * P := by omega
  have R1 : 2 * AC + den - 2 * P < 2 * den := by omega
  have hdiv : (2 * AC + den) / (2 * den) = out :=
    ((Int.ediv_emod_unique (by omega : (0 : ℤ) < 2 * den)).2 ⟨by rw [← hP]; ring, R0, R1⟩).1
  refine ⟨hdiv.symm, ?_⟩
  rw [abs_le]
  constructor
  · -- 2 den out > 2 AC − den ≥ −4,095 den
    by_contra hcon
    have h1 : out ≤ -2048 := by omega
    have h2 : den * out ≤ den * (-2048) := mul_le_mul_of_nonneg_left h1 (by omega)
    rw [hP] at h2
    omega
  · by_contra hcon
    have h1 : 2048 ≤ out := by omega
    have h2 : den * 2048 ≤ den * out := mul_le_mul_of_nonneg_left h1 (by omega)
    rw [hP] at h2
    omega

/-! ## Part 2. Step A5 at the places -/

section Places
variable {D : Dim} {tb : Tables} {t : Raw → ℤ} {b : ℕ}

variable [scl : Scl]
variable (hO : ExpOK D.sh D.u0) (hE : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12)
  (h : IntRel D tb p t) (H : Half1 D t b) (hb : b < D.nb)
include hO hE h H hb

/-- (FA7), at every place of both regions. -/
theorem fa7 (ρ : Reg) {x : ℕ} (hx : x < 2 ^ D.lReg ρ) :
    0 ≤ gp D t ρ b x ∧
    (gp D t ρ b x < D.cutC → wtV t ρ b x = tb.Exp (gp D t ρ b x / 2 ^ D.sh)) ∧
    (D.cutC ≤ gp D t ρ b x → wtV t ρ b x = 0) ∧
    0 ≤ wtV t ρ b x ∧
    wtV t ρ b x ≤ 2 ^ 12 := by
  obtain ⟨r0, r1, rf⟩ := H.fa1 ρ x hx
  obtain ⟨g0, g1⟩ := gp_bounds hO H ρ hx
  obtain ⟨ι, hι, hk⟩ := h.k2 ρ b x hb hx
  exact stepA5 hO hE r0 r1 rf g0 g1 (h.place_abs hb hx).2.2.2 hι hk

/-- Under the hypotheses of its statement, the gap is not negative, and the weight is a function of
it: (PA3), (PA4). -/
theorem wt_of_gap {ρ : Reg} {x : ℕ} (hx : x < 2 ^ D.lReg ρ) {d : ℤ} (hd : gp D t ρ b x = d) :
    0 ≤ d ∧ wtV t ρ b x = (if d / 2 ^ D.sh < D.u0 then tb.Exp (d / 2 ^ D.sh) else 0) := by
  obtain ⟨f0, f1, f2, -, -⟩ := fa7 hO hE h H hb ρ hx
  rw [hd] at f0 f1 f2
  refine ⟨f0, ?_⟩
  have hiff : d / 2 ^ D.sh < D.u0 ↔ d < D.cutC := by
    rw [Int.ediv_lt_iff_lt_mul (by positivity : (0 : ℤ) < 2 ^ D.sh)]
    show _ ↔ d < 2 ^ D.sh * D.u0
    rw [mul_comm]
  by_cases hc : d / 2 ^ D.sh < D.u0
  · rw [if_pos hc]
    exact f1 (hiff.1 hc)
  · rw [if_neg hc]
    exact f2 (not_lt.1 fun hlt => hc (hiff.2 hlt))

/-- (FA9), (FA7) at the place of a pair of positions j ≤ i, under the hypotheses of its statement:
the gap is mx − sc, it is not negative, and the weight is that of (PA3), (PA4). -/
theorem wtIJ_le {g i j : ℕ} (hg : g < D.nG) (hi : i < D.T) (hj : j ≤ i) :
    0 ≤ mxV t b g i - scV D t b g i j ∧
    wtIJ D t b g i j =
      (if (mxV t b g i - scV D t b g i j) / 2 ^ D.sh < D.u0 then
          tb.Exp ((mxV t b g i - scV D t b g i j) / 2 ^ D.sh)
        else 0) := by
  have hI : i / D.B < D.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  have hi' : i % D.B < D.B := Nat.mod_lt _ D.B_pos
  have hj' : j % D.B < D.B := Nat.mod_lt _ D.B_pos
  have ei : D.B * (i / D.B) + i % D.B = i := Nat.div_add_mod i D.B
  have ej : D.B * (j / D.B) + j % D.B = j := Nat.div_add_mod j D.B
  unfold wtIJ
  by_cases hJ : j / D.B < i / D.B
  · rw [if_pos hJ]
    obtain ⟨s1, s2, s3, s4⟩ := D.slot_of_blk hJ hI
    have s2' : D.slotS (i / D.B) (j / D.B) < D.nBlk := by omega
    obtain ⟨q1, q2, q3, q4, q5⟩ := D.parts_codeM (g := g) s1 s2' hi' hj'
    refine wt_of_gap hO hE h H hb (ρ := .M) (D.codeM_lt hg s1 s2' hi' hj') ?_
    have hne : ¬ D.EmptyM
        (D.codeM g (D.slotP (i / D.B)) (D.slotS (i / D.B) (j / D.B)) (i % D.B) (j % D.B)) := by
      unfold Dim.EmptyM
      rw [q3]
      omega
    rw [gp_M, if_neg hne]
    unfold Dim.iM Dim.jM
    rw [q1, q2, q3, q4, q5, s3, s4, ei, ej]
  · rw [if_neg hJ]
    have hJI : j / D.B = i / D.B := le_antisymm (Nat.div_le_div_right hj) (not_lt.mp hJ)
    obtain ⟨q1, q2, q3, q4⟩ := D.parts_codeD (g := g) hI hi' hj'
    refine wt_of_gap hO hE h H hb (ρ := .D) (D.codeD_lt hg hI hi' hj') ?_
    have hnm : ¬ D.MaskedD (D.codeD g (i / D.B) (i % D.B) (j % D.B)) := by
      unfold Dim.MaskedD
      rw [q3, q4]
      rw [hJI] at ej
      omega
    rw [gp_D, if_neg hnm, add_zero]
    unfold Dim.iD Dim.jD
    rw [q1, q2, q3, q4, ei]
    rw [hJI] at ej
    rw [ej]

/-- (FA8), under the hypotheses of its statement: the places of the row with j > i are masked, and
their weight is 0. -/
theorem wtIJ_gt {g i j : ℕ} (hg : g < D.nG) (hi : i < D.T)
    (hij : i < j) (hj : j < D.B * (i / D.B + 1)) : wtIJ D t b g i j = 0 := by
  have hI : i / D.B < D.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  have hi' : i % D.B < D.B := Nat.mod_lt _ D.B_pos
  have hj' : j % D.B < D.B := Nat.mod_lt _ D.B_pos
  have ei : D.B * (i / D.B) + i % D.B = i := Nat.div_add_mod i D.B
  have ej : D.B * (j / D.B) + j % D.B = j := Nat.div_add_mod j D.B
  have hJI : j / D.B = i / D.B :=
    le_antisymm (Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul hj)) (Nat.div_le_div_right (le_of_lt hij))
  unfold wtIJ
  rw [if_neg (by omega)]
  obtain ⟨q1, q2, q3, q4⟩ := D.parts_codeD (g := g) hI hi' hj'
  have hx := D.codeD_lt hg hI hi' hj'
  have hm : D.MaskedD (D.codeD g (i / D.B) (i % D.B) (j % D.B)) := by
    unfold Dim.MaskedD
    rw [q3, q4]
    rw [hJI] at ej
    omega
  obtain ⟨-, -, f2, -, -⟩ := fa7 hO hE h H hb .D (x := D.codeD g (i / D.B) (i % D.B) (j % D.B)) hx
  refine f2 ?_
  obtain ⟨p1, p2, p3⟩ := posD hx
  have := diff_bounds H p1 p2 p3
  rw [gp_D, if_pos hm]
  have hOm : Om D = 1072693504 + D.cutC := by norm_num [Om, Smax]
  rw [hOm]
  omega

end Places

/-! ## Part 3. Step A6: the greatest score, the denominator, the numerator -/

section Sums
variable {D : Dim} {tb : Tables} {t : Raw → ℤ} {b : ℕ}
variable [scl : Scl]
variable (hO : ExpOK D.sh D.u0) (hE : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12)
  (h : IntRel D tb p t) (H : Half1 D t b) (hb : b < D.nb)
include hO hE h H hb

/-- Under the hypotheses of its statement, a sum over the places of row (g, i) is the sum over the
positions j ≤ i, with the weights of the program ((FA7), (FA8), (FA9)). -/
theorem rowSum_le (G : ℕ → ℤ) {g i : ℕ} (hg : g < D.nG) (hi : i < D.T) :
    rowSum D t G b g i = ∑ j ∈ range (i + 1), wtP D tb (mxV t b g i) (scV D t b g i) j * G j := by
  rw [rowSum_eq D t G b g hi]
  have hle : i + 1 ≤ D.B * (i / D.B + 1) := by
    have e := Nat.div_add_mod i D.B
    have l := Nat.mod_lt i D.B_pos
    rw [Nat.mul_succ]
    omega
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hle) (fun j hj hn => by
    rw [wtIJ_gt hO hE h H hb hg hi (by rw [mem_range] at hn; omega) (mem_range.mp hj), zero_mul])]
  exact sum_congr rfl fun j hj => by
    rw [(wtIJ_le hO hE h H hb hg hi (Nat.lt_succ_iff.mp (mem_range.mp hj))).2]
    rfl

/-- (PA2), under the hypotheses of its statement: mx is the greatest score among the positions j ≤
i. -/
theorem mx_eq {g i : ℕ} (hg : g < D.nG) (hi : i < D.T) : mxV t b g i = maxTo (scV D t b g i) i := by
  refine (maxTo_eq (fun j hj => ?_) ?_).symm
  · have := (wtIJ_le hO hE h H hb hg hi hj).1
    omega
  · obtain ⟨js, hjs, e⟩ := H.fa6 g i hg hi
    exact ⟨js, hjs, e.symm⟩

theorem wt_bounds {g i j : ℕ} (hg : g < D.nG) (hi : i < D.T) (hj : j ∈ range (i + 1)) :
    0 ≤ wtP D tb (mxV t b g i) (scV D t b g i) j ∧
    wtP D tb (mxV t b g i) (scV D t b g i) j ≤ 2 ^ 12 :=
  wtP_bounds hE (wtIJ_le hO hE h H hb hg hi (Nat.lt_succ_iff.mp (mem_range.mp hj))).1

/-- (FA10), under the hypotheses of its statement: (PA5), and 2^12 ≤ den ≤ 2^22. -/
theorem fa10 (hE0 : tb.Exp 0 = 2 ^ 12) (hT : D.T ≤ 1024) {g i : ℕ} (hg : g < D.nG) (hi : i < D.T) :
    denV t b g i = ∑ j ∈ range (i + 1), wtP D tb (mxV t b g i) (scV D t b g i) j ∧
    2 ^ 12 ≤ denV t b g i ∧
    denV t b g i ≤ 2 ^ 22 := by
  have hEF : EF D t b g i = ∑ j ∈ range (i + 1), wtP D tb (mxV t b g i) (scV D t b g i) j := by
    unfold EF
    rw [rowSum_le hO hE h H hb _ hg hi]
    exact sum_congr rfl fun j _ => mul_one _
  have h0 : ∀ j ∈ range (i + 1), 0 ≤ wtP D tb (mxV t b g i) (scV D t b g i) j := fun j hj =>
    (wt_bounds hO hE h H hb hg hi hj).1
  have hup : ∑ j ∈ range (i + 1), wtP D tb (mxV t b g i) (scV D t b g i) j ≤ 2 ^ 22 := by
    have := Finset.sum_le_card_nsmul (range (i + 1)) _ (2 ^ 12 : ℤ) fun j hj =>
      (wt_bounds hO hE h H hb hg hi hj).2
    rw [card_range, nsmul_eq_mul] at this
    have hi' : ((i + 1 : ℕ) : ℤ) ≤ 1024 := by exact_mod_cast (by omega : i + 1 ≤ 1024)
    nlinarith
  have hlo : 2 ^ 12 ≤ ∑ j ∈ range (i + 1), wtP D tb (mxV t b g i) (scV D t b g i) j := by
    obtain ⟨js, hjs, e⟩ := H.fa6 g i hg hi
    have h1 := Finset.single_le_sum h0 (mem_range.mpr (Nat.lt_succ_of_le hjs))
    have h2 : wtP D tb (mxV t b g i) (scV D t b g i) js = 2 ^ 12 := by
      unfold wtP
      rw [e, sub_self, Int.zero_ediv, if_pos (by exact_mod_cast hO.pos)]
      exact hE0
    rw [h2] at h1
    exact h1
  have hk := h.at3 b g i hb hg hi
  have hden : denV t b g i = EF D t b g i :=
    stepA6 (h.denV_abs hb hg hi) (by rw [hEF]; exact sum_nonneg h0) (by rw [hEF]; exact hup) hk
  rw [hden, hEF]
  exact ⟨rfl, hlo, hup⟩

/-- (FA11), under the hypotheses of its statement: (PA6), and |AC| ≤ 2,047 den. -/
theorem fa11 (hE0 : tb.Exp 0 = 2 ^ 12) (hT : D.T ≤ 1024) (hin : InB D t b) {g i n : ℕ}
    (hg : g < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    AC D t b g i n =
      ∑ j ∈ range (i + 1), wtP D tb (mxV t b g i) (scV D t b g i) j * valV t (D.lamOf b) g j n ∧
    |AC D t b g i n| ≤ 2047 * denV t b g i := by
  have hAC : AC D t b g i n =
      ∑ j ∈ range (i + 1), wtP D tb (mxV t b g i) (scV D t b g i) j * valV t (D.lamOf b) g j n := by
    unfold AC
    exact rowSum_le hO hE h H hb _ hg hi
  refine ⟨hAC, ?_⟩
  rw [hAC, (fa10 hO hE h H hb hE0 hT hg hi).1, mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  have hw := (wt_bounds hO hE h H hb hg hi hj).1
  have hv := (hin.2 g hg j (lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hj)) hi) n hn).2
  rw [abs_mul, abs_of_nonneg hw, mul_comm (2047 : ℤ)]
  exact mul_le_mul_of_nonneg_left hv hw

/-! ## Part 4. Step A7 -/

/-- (FA12), under the hypotheses of its statement: (PA7), and |out| ≤ 2,047. -/
theorem fa12 (hE0 : tb.Exp 0 = 2 ^ 12) (hT : D.T ≤ 1024) (hin : InB D t b) {g i n : ℕ}
    (hg : g < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    outV t b g i n = (2 * AC D t b g i n + denV t b g i) / (2 * denV t b g i) ∧
    |outV t b g i n| ≤ 2047 := by
  obtain ⟨-, d0, d1⟩ := fa10 hO hE h H hb hE0 hT hg hi
  obtain ⟨q, q'⟩ := H.fa2 g i n hg hi hn
  obtain ⟨e0, he0, hk0⟩ := h.k3W 0 b g i n (by norm_num) hb hg hi hn
  obtain ⟨e1, he1, hk1⟩ := h.k3W 1 b g i n (by norm_num) hb hg hi hn
  have k0 : key3W D t 0 b g i n =
      (2 * AC D t b g i n + denV t b g i - 2 * denV t b g i * outV t b g i n) -
        2 ^ 16 * qhV t b g i n := by
    unfold key3W RE
    rw [if_pos rfl]
  have k1 : key3W D t 1 b g i n =
      2 * denV t b g i - 1 -
        (2 * AC D t b g i n + denV t b g i - 2 * denV t b g i * outV t b g i n) -
        2 ^ 16 * qhV' t b g i n := by
    unfold key3W RE
    rw [if_neg (by norm_num)]
  rw [k0] at hk0
  rw [k1] at hk1
  exact stepA7 d0 d1 (fa11 hO hE h H hb hE0 hT hin hg hi hn).2
    (h.outV_abs hb hg hi hn) q q' he0 he1 hk0 hk1

end Sums

/-! ## Part 5. The program -/

section Link
variable {D : Dim} {P : Params} {tb tbP : Tables} {w : LayerW} {L : ℕ} {x : ℕ → Vec}
  {lam : ℕ} {t : Raw → ℤ} {b : ℕ}

/-- (PA1) to (PA7), under the hypotheses of its statement: out holds the output of the program. tb:
the tables of the segment's look-up argument; tbP: the tables that the program reads in this layer;
they have the same exponential. -/
theorem out_link [scl : Scl] (hO : ExpOK D.sh D.u0)
    (hE : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12) (hE0 : tb.Exp 0 = 2 ^ 12)
    (hX : tbP.Exp = tb.Exp) (h : IntRel D tb p t) (H : Half1 D t b) (hT : D.T ≤ 1024) (F : Fit D P)
    (hin : InputsAre D P tbP w L x lam t) (hb : b < D.nb) (hl : D.lamOf b = lam) {g i n : ℕ}
    (hg : g < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    outV t b g i n = Att.o P tbP w L x i (D.ch * D.head g b + n) := by
  have hB := inB_of_inputs hin hb hl
  have hsc : ∀ j ≤ i, scV D t b g i j = Att.sc P tbP w L x (D.head g b) i j := fun j hj =>
    sc_link F hin hb hl hg hi (lt_of_le_of_lt hj hi)
  have hmx : mxV t b g i = Att.mx P tbP w L x (D.head g b) i := by
    rw [mx_eq hO hE h H hb hg hi]
    exact maxTo_congr i hsc
  have hwt : ∀ j ∈ range (i + 1), wtP D tb (mxV t b g i) (scV D t b g i) j =
      Att.wt P tbP w L x (D.head g b) i j := fun j hj => by
    unfold wtP Att.wt Att.u
    rw [hmx, hsc j (Nat.lt_succ_iff.mp (mem_range.mp hj)), F.exp, F.sh, hX]
  have hden : denV t b g i = Att.den P tbP w L x (D.head g b) i := by
    rw [(fa10 hO hE h H hb hE0 hT hg hi).1]
    exact sum_congr rfl hwt
  have hac : AC D t b g i n = Att.ac P tbP w L x (D.head g b) i n := by
    rw [(fa11 hO hE h H hb hE0 hT hB hg hi hn).1]
    unfold Att.ac
    rw [kvOf_head F, ← F.ch, hl]
    exact sum_congr rfl fun j hj => by
      rw [hwt j hj,
        (hin.2 g hg j (lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hj)) hi) n hn).2]
  rw [(fa12 hO hE h H hb hE0 hT hB hg hi hn).1, hac, hden]
  unfold Att.o
  rw [← F.ch, Nat.mul_add_div D.ch_pos, Nat.div_eq_of_lt hn, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hn]

end Link

/-! The statements at any lawful shift are `noWrapK`, `outBoundK` in Inst/Model/Bound/AttK.lean. -/

end NW2

end Cm.TI.AttSeg

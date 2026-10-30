-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/HonestGen.lean: the honest trace of an attention segment, for all sizes that `Adm`
  allows and arbitrary integer inputs of absolute value at most 2,047. Main statements: under `Adm`,
  `honG` satisfies the relation over the integers (`rfraw_hon`), and every valid cell is at most 128
  in absolute value (`abs_hon_le`).

  The inputs are integer functions Q (b, g, i, n), Kx and V (λ, g, j, n), and O (b, g, i, n), which
  is to be the output. From Q, Kx, V the steps (PA1) to (PA6) are written once more (`scP` ..
  `acP`), and the honest trace `honG`. `Adm` collects what is asked: the inputs are at most 2,047 in
  absolute value, O is the quotient of step (PA7) at the channels n < ch, the numbers of channels
  and of positions are at most the reference's (`ch`, `T`), the shift and the number of live rows
  are valid (`ExpOK`), the table Exp has its ranges. Parts 3 to 6 mostly assume `Adm`. Keys are
  looked-up values; (PA1) to (PA7): Inst/Model/Program.lean; (At1) to (At3): `Idn`,
  Inst/Model/Att/Trace.lean; (Tab8): `Tables.OK`, Inst/Model/Tables.lean.
  The rule of `honG` is that of `hon` in Inst/Model/Att/Trace.lean.
  Notation:
    `Q`, `Kx`, `V`, `O`: maps `ℕ → ℕ → ℕ → ℕ → ℤ`; Kx: see `Att.kx`: "the paper's qry and key are
      `q` and `kx`" (Inst/Model/Program.lean); O stands where the arrays have out.
    g, b, i, j, n, lam: natural numbers (Inst/Model/Att/Index.lean): "key/value heads g"; "pairs b =
      na λ + a of a layer λ of the segment and the number a of a query head among those of its
      key/value head"; "positions i, j"; "channels n"; λ (lam in Lean names): a layer of the
      segment.
    ρ, x: a region (`Reg`: "the two regions") and an entry of it: "the entry x of the region, for
      the pair b" (`Raw.c`, Inst/Model/Att/Trace.lean).
-/
import Inst.Model.Att.Trace
import Inst.Model.Att.HonestArith
import Inst.Model.Widened

set_option autoImplicit false

namespace Inst.Model.AttSeg.Hon

open Finset

variable [scl : Scl]
variable (D : Dim) (tb : Tables) (Q Kx V O : ℕ → ℕ → ℕ → ℕ → ℤ)

/-! ## Part 1. The program's values and the honest trace -/

/-- (PA1) -/
def scP (b g i j : ℕ) : ℤ := ∑ n ∈ range D.ch, Q b g i n * Kx (D.lamOf b) g j n
/-- (PA2) -/
def mxP (b g i : ℕ) : ℤ := maxTo (scP D Q Kx b g i) i
/-- the least index at which the greatest score is attained -/
def jStar (b g i : ℕ) : ℕ := argTo (scP D Q Kx b g i) i
/-- (PA3), (PA4) -/
def wtP (b g i j : ℕ) : ℤ := wOf D.sh D.u0 tb (mxP D Q Kx b g i - scP D Q Kx b g i j)
/-- (PA5) -/
def denP (b g i : ℕ) : ℤ := ∑ j ∈ range (i + 1), wtP D tb Q Kx b g i j
/-- (PA6) -/
def acP (b g i n : ℕ) : ℤ := ∑ j ∈ range (i + 1), wtP D tb Q Kx b g i j * V (D.lamOf b) g j n
/-- RE = 2 ac + den - 2 den out -/
def reP (b g i n : ℕ) : ℤ :=
  2 * acP D tb Q Kx V b g i n + denP D tb Q Kx b g i - 2 * denP D tb Q Kx b g i * O b g i n

/-- the extended gap, from the program's values -/
def gpP : Reg → ℕ → ℕ → ℤ
  | .M, b, x =>
    if D.EmptyM x then D.cutC
    else mxP D Q Kx b (D.mG x) (D.iM x) - scP D Q Kx b (D.mG x) (D.iM x) (D.jM x)
  | .D, b, x =>
    mxP D Q Kx b (D.dG x) (D.iD x) - scP D Q Kx b (D.dG x) (D.iD x) (D.jD x) +
      if D.MaskedD x then Om D else 0

/-- The honest trace. The names of the cells: `Raw` (Inst/Model/Att/Trace.lean); of `.c`: "cell
number jj < 5 of the entry x of the region, for the pair b: r0 - 128, r1 - 128, fl, w0 - 128, w1".
As in `hon` there, "The values mx, den, qry, out, key, val are written in cells by the rule of
Inst/Model/Widened.lean" (`cellW`). -/
def honG : Raw → ℤ
  | .c ρ 0 b x => rmOf D.sh D.u0 (gpP D Q Kx ρ b x) % 256 - 128
  | .c ρ 1 b x => rmOf D.sh D.u0 (gpP D Q Kx ρ b x) / 256 - 128
  | .c ρ 2 b x => flOf D.sh D.u0 (gpP D Q Kx ρ b x)
  | .c ρ 3 b x => wOf D.sh D.u0 tb (gpP D Q Kx ρ b x) % 256 - 128
  | .c ρ _ b x => wOf D.sh D.u0 tb (gpP D Q Kx ρ b x) / 256
  | .mx k b g i => cellW 4 (mxP D Q Kx b g i) k
  | .den k b g i => cellW 4 (denP D tb Q Kx b g i) k
  | .ib k b g i => bitZ k (jStar D Q Kx b g i)
  | .qh b g i n => reP D tb Q Kx V O b g i n / 2 ^ 16 - 128
  | .qh' b g i n => (2 * denP D tb Q Kx b g i - 1 - reP D tb Q Kx V O b g i n) / 2 ^ 16 - 128
  | .qry k b g i n => cellW 2 (Q b g i n) k
  | .out k b g i n => cellW 2 (O b g i n) k
  | .key k lam g j n => cellW 2 (Kx lam g j n) k
  | .val k lam g j n => cellW 2 (V lam g j n) k

/-- What is asked of the inputs, the sizes and the table. -/
structure Adm : Prop where
  q : ∀ b g i n, |Q b g i n| ≤ 2047
  k : ∀ lam g j n, |Kx lam g j n| ≤ 2047
  v : ∀ lam g j n, |V lam g j n| ≤ 2047
  /-- (PA7), at the channels of a head -/
  o : ∀ b g i n, n < D.ch →
    O b g i n = (2 * acP D tb Q Kx V b g i n + denP D tb Q Kx b g i) / (2 * denP D tb Q Kx b g i)
  ch : (D.ch : ℤ) * 2047 ^ 2 ≤ Smax
  T : D.T ≤ 1024
  /-- the shift and the number of live rows of the exponential are valid; (Tab8) -/
  ex : ExpOK D.sh D.u0
  exp : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12
  exp0 : tb.Exp 0 = 2 ^ 12

/-! ## Part 2. What the arrays of Inst/Model/Att/Trace.lean read -/

section Arrays

local notation "H" => honG D tb Q Kx V O

theorem r0_hon (ρ : Reg) (b x : ℕ) : r0 H ρ b x = rmOf D.sh D.u0 (gpP D Q Kx ρ b x) % 256 := by
  simp [r0, honG]
theorem r1_hon (ρ : Reg) (b x : ℕ) : r1 H ρ b x = rmOf D.sh D.u0 (gpP D Q Kx ρ b x) / 256 := by
  simp [r1, honG]
theorem fl_hon (ρ : Reg) (b x : ℕ) : flV H ρ b x = flOf D.sh D.u0 (gpP D Q Kx ρ b x) := by
  simp [flV, honG]
theorem rm_hon (ρ : Reg) (b x : ℕ) : rm H ρ b x = rmOf D.sh D.u0 (gpP D Q Kx ρ b x) := by
  rw [rm, r0_hon, r1_hon]
  omega
theorem wt_hon (ρ : Reg) (b x : ℕ) : wtV H ρ b x = wOf D.sh D.u0 tb (gpP D Q Kx ρ b x) := by
  simp only [wtV, w0, w1, honG]
  omega
theorem mxV_hon (b g i : ℕ) : mxV H b g i = mxP D Q Kx b g i := sum_cellW (by norm_num) _
theorem denV_hon (b g i : ℕ) : denV H b g i = denP D tb Q Kx b g i := sum_cellW (by norm_num) _
theorem ibV_hon (k b g i : ℕ) : ibV H k b g i = bitZ k (jStar D Q Kx b g i) := rfl
theorem qhV_hon (b g i n : ℕ) : qhV H b g i n = reP D tb Q Kx V O b g i n / 2 ^ 16 := by
  simp [qhV, honG]
theorem qhV'_hon (b g i n : ℕ) :
    qhV' H b g i n = (2 * denP D tb Q Kx b g i - 1 - reP D tb Q Kx V O b g i n) / 2 ^ 16 := by
  simp [qhV', honG]
theorem qryV_hon (b g i n : ℕ) : qryV H b g i n = Q b g i n := sum_cellW (by norm_num) _
theorem outV_hon (b g i n : ℕ) : outV H b g i n = O b g i n := sum_cellW (by norm_num) _
theorem keyV_hon (lam g j n : ℕ) : keyV H lam g j n = Kx lam g j n := sum_cellW (by norm_num) _
theorem valV_hon (lam g j n : ℕ) : valV H lam g j n = V lam g j n := sum_cellW (by norm_num) _

theorem sc_hon (b g i j : ℕ) : scV D H b g i j = scP D Q Kx b g i j := by
  simp only [scV, scP, qryV_hon, keyV_hon]

theorem gp_hon (ρ : Reg) (b x : ℕ) : gp D H ρ b x = gpP D Q Kx ρ b x := by
  cases ρ <;> simp only [gp, gpP, mxV_hon, sc_hon, Int.cast_id]

end Arrays

/-! ## Part 3. Ranges -/

section Ranges

variable {D tb Q Kx V O} (h : Adm D tb Q Kx V O)
include h

theorem abs_scP_le (b g i j : ℕ) : |scP D Q Kx b g i j| ≤ Smax :=
  (abs_dot_le D.ch _ _ 2047 (fun n _ => h.q b g i n) fun n _ => h.k _ g j n).trans h.ch

theorem abs_mxP_le (b g i : ℕ) : |mxP D Q Kx b g i| ≤ Smax :=
  abs_maxTo_le _ _ _ fun j _ => abs_scP_le h b g i j

theorem gap_le {b g i j : ℕ} (hj : j ≤ i) :
    0 ≤ mxP D Q Kx b g i - scP D Q Kx b g i j ∧ mxP D Q Kx b g i - scP D Q Kx b g i j ≤ 2 * Smax :=
  gap_causal _ _ _ (fun j _ => abs_scP_le h b g i j) hj

theorem gap_om (b g i j : ℕ) :
    D.cutC ≤ mxP D Q Kx b g i - scP D Q Kx b g i j + Om D ∧
    mxP D Q Kx b g i - scP D Q Kx b g i j + Om D ≤ 4 * Smax + D.cutC :=
  gap_masked (abs_mxP_le h b g i) (abs_scP_le h b g i j)

/-- Under `Adm` (`h`): the extended gap is in [0, 4 S_max + C], at every entry. -/
theorem gpP_range (ρ : Reg) (b x : ℕ) :
    0 ≤ gpP D Q Kx ρ b x ∧ gpP D Q Kx ρ b x ≤ 4 * Smax + D.cutC := by
  have hS := Smax_nonneg
  have hC : 0 ≤ D.cutC := cutC_nonneg D.sh D.u0
  cases ρ with
  | M =>
    simp only [gpP]
    split_ifs with he
    · constructor <;> linarith
    · have hP : D.mP x < D.hP := Nat.mod_lt _ D.hP_pos
      have hs : D.mS x < D.nBlk - 1 := by
        have h1 : D.mS x < D.nBlk := Nat.mod_lt _ D.nBlk_pos
        have h2 : D.mS x ≠ D.nBlk - 1 := he
        omega
      have h3 := (D.blk_of_slot hP hs).1
      have hJ : D.mJ x < D.B := Nat.mod_lt _ D.B_pos
      have hle : D.jM x ≤ D.iM x := by
        unfold Dim.jM Dim.iM
        have : D.B * (D.colBlk (D.mP x) (D.mS x) + 1) ≤ D.B * D.rowBlk (D.mP x) (D.mS x) :=
          Nat.mul_le_mul_left _ h3
        rw [Nat.mul_succ] at this
        omega
      obtain ⟨g1, g2⟩ := gap_le h (b := b) (g := D.mG x) hle
      constructor <;> linarith
  | D =>
    simp only [gpP]
    split_ifs with hm
    · obtain ⟨g1, g2⟩ := gap_om h b (D.dG x) (D.iD x) (D.jD x)
      constructor <;> linarith
    · have hle : D.jD x ≤ D.iD x := by
        unfold Dim.jD Dim.iD
        have : ¬ D.mI x < D.mJ x := hm
        omega
      obtain ⟨g1, g2⟩ := gap_le h (b := b) (g := D.dG x) hle
      constructor <;> linarith

end Ranges

/-! ## Part 4. The sum over the entries of a row -/

section Row

variable {D tb Q Kx V O} (h : Adm D tb Q Kx V O)

local notation "H" => honG D tb Q Kx V O

/-- the weight at the entry that represents the pair of positions (i, j) -/
theorem wtIJ_hon (b g : ℕ) {i j : ℕ} (hi : i < D.T) (hj : j < D.B * (i / D.B + 1)) :
    wtIJ D H b g i j =
      wOf D.sh D.u0 tb (mxP D Q Kx b g i - scP D Q Kx b g i j + if i < j then Om D else 0) := by
  have hI : i / D.B < D.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  have hi' : i % D.B < D.B := Nat.mod_lt _ D.B_pos
  have hj' : j % D.B < D.B := Nat.mod_lt _ D.B_pos
  have ei : D.B * (i / D.B) + i % D.B = i := Nat.div_add_mod i D.B
  have ej : D.B * (j / D.B) + j % D.B = j := Nat.div_add_mod j D.B
  have hJle : j / D.B ≤ i / D.B := Nat.lt_succ_iff.1 (Nat.div_lt_of_lt_mul hj)
  unfold wtIJ
  split_ifs with hlt hij hij
  · -- an earlier block, yet i < j: impossible
    exfalso
    have : D.B * (j / D.B + 1) ≤ D.B * (i / D.B) := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_succ] at this
    omega
  · obtain ⟨s1, s2, s3, s4⟩ := D.slot_of_blk hlt hI
    obtain ⟨p1, p2, p3, p4, p5⟩ :=
      D.parts_codeM (g := g) s1 (show D.slotS (i / D.B) (j / D.B) < D.nBlk by omega) hi' hj'
    have hne : ¬ D.EmptyM
        (D.codeM g (D.slotP (i / D.B)) (D.slotS (i / D.B) (j / D.B)) (i % D.B) (j % D.B)) := by
      unfold Dim.EmptyM
      rw [p3]
      omega
    rw [wt_hon]
    simp only [gpP, if_neg hne, Dim.iM, Dim.jM, p1, p2, p3, p4, p5, s3, s4, ei, ej, add_zero]
  · obtain ⟨p1, p2, p3, p4⟩ := D.parts_codeD (g := g) hI hi' hj'
    have eJ : j / D.B = i / D.B := by omega
    have hm : D.MaskedD (D.codeD g (i / D.B) (i % D.B) (j % D.B)) := by
      unfold Dim.MaskedD
      rw [p3, p4]
      rw [eJ] at ej
      omega
    rw [wt_hon]
    rw [eJ] at ej
    simp only [gpP, if_pos hm, Dim.iD, Dim.jD, p1, p2, p3, p4, ei, ej]
  · obtain ⟨p1, p2, p3, p4⟩ := D.parts_codeD (g := g) hI hi' hj'
    have eJ : j / D.B = i / D.B := by omega
    have hm : ¬ D.MaskedD (D.codeD g (i / D.B) (i % D.B) (j % D.B)) := by
      unfold Dim.MaskedD
      rw [p3, p4]
      rw [eJ] at ej
      omega
    rw [wt_hon]
    rw [eJ] at ej
    simp only [gpP, if_neg hm, Dim.iD, Dim.jD, p1, p2, p3, p4, ei, ej]

include h

/-- Under `Adm` (`h`), for i < T: the sum over the entries of a row is the sum over the positions
attended to: the weight of a masked entry is 0. -/
theorem rowSum_hon (G : ℕ → ℤ) (b g : ℕ) {i : ℕ} (hi : i < D.T) :
    rowSum D H G b g i = ∑ j ∈ range (i + 1), wtP D tb Q Kx b g i j * G j := by
  have hle : i + 1 ≤ D.B * (i / D.B + 1) := by
    have e := Nat.div_add_mod i D.B
    have h2 := Nat.mod_lt i D.B_pos
    rw [Nat.mul_succ]
    omega
  rw [rowSum_eq D H G b g hi]
  symm
  refine sum_subset_zero_on_sdiff (range_subset_range.2 hle) (fun j hj => ?_) fun j hj => ?_
  · rw [mem_sdiff, mem_range, mem_range] at hj
    rw [wtIJ_hon b g hi hj.1, if_pos (by omega), wOf_dead tb (gap_om h b g i j).1, zero_mul]
  · rw [mem_range] at hj
    rw [wtIJ_hon b g hi (by omega), if_neg (by omega), add_zero]
    rfl

theorem EF_hon (b g : ℕ) {i : ℕ} (hi : i < D.T) : EF D H b g i = denP D tb Q Kx b g i := by
  rw [EF, rowSum_hon h _ b g hi]
  exact sum_congr rfl fun j _ => mul_one _

theorem AC_hon (b g : ℕ) {i : ℕ} (hi : i < D.T) (n : ℕ) :
    AC D H b g i n = acP D tb Q Kx V b g i n := by
  rw [AC, rowSum_hon h _ b g hi]
  exact sum_congr rfl fun j _ => by rw [valV_hon]

theorem RE_hon (b g : ℕ) {i : ℕ} (hi : i < D.T) (n : ℕ) :
    RE D H b g i n = reP D tb Q Kx V O b g i n := by
  rw [RE, AC_hon h b g hi, denV_hon, outV_hon]
  rfl

theorem wtP_range {b g i j : ℕ} (hj : j ≤ i) :
    0 ≤ wtP D tb Q Kx b g i j ∧ wtP D tb Q Kx b g i j ≤ 2 ^ 12 :=
  wOf_range h.exp (gap_le h hj).1

/-- Under `Adm` (`h`), for i < T: the denominator is in [2^12, 2^22]. -/
theorem denP_range (b g : ℕ) {i : ℕ} (hi : i < D.T) :
    2 ^ 12 ≤ denP D tb Q Kx b g i ∧ denP D tb Q Kx b g i ≤ 2 ^ 22 := by
  constructor
  · have hs : jStar D Q Kx b g i ∈ range (i + 1) :=
      mem_range.2 (Nat.lt_succ_of_le (argTo_spec _ _).1)
    have h1 : wtP D tb Q Kx b g i (jStar D Q Kx b g i) = 2 ^ 12 := by
      unfold wtP mxP jStar
      rw [maxTo_eq_argTo, sub_self, wOf_zero h.ex.pos h.exp0]
    rw [← h1]
    exact single_le_sum (f := fun j => wtP D tb Q Kx b g i j)
      (fun j hj => (wtP_range h (Nat.lt_succ_iff.1 (mem_range.1 hj))).1) hs
  · have h1 : denP D tb Q Kx b g i ≤ ∑ _j ∈ range (i + 1), (2 : ℤ) ^ 12 :=
      sum_le_sum fun j hj => (wtP_range h (Nat.lt_succ_iff.1 (mem_range.1 hj))).2
    rw [sum_const, card_range, nsmul_eq_mul] at h1
    have h2 : ((i + 1 : ℕ) : ℤ) ≤ 1024 := by
      have := h.T
      exact_mod_cast (by omega : i + 1 ≤ 1024)
    nlinarith

/-- Under `Adm` (`h`), for i < T: the remainder of the division is in [0, 2 den), at a channel of a
head. -/
theorem reP_range (b g : ℕ) {i n : ℕ} (hi : i < D.T) (hn : n < D.ch) :
    0 ≤ reP D tb Q Kx V O b g i n ∧ reP D tb Q Kx V O b g i n < 2 * denP D tb Q Kx b g i := by
  have hd := (denP_range h b g hi).1
  have := reOf_range (acP D tb Q Kx V b g i n) (den := denP D tb Q Kx b g i) (by linarith)
  unfold reP
  rw [h.o b g i n hn]
  exact this

end Row

/-! ## Part 5. Keys and identities -/

section Keys

variable {D tb Q Kx V O} (h : Adm D tb Q Kx V O)

local notation "H" => honG D tb Q Kx V O

include h in
theorem key1_hon (ρ : Reg) (b x : ℕ) : InLut (tau1 D.sh) (key1 H ρ b x) := by
  rw [key1, r0_hon, r1_hon, fl_hon]
  exact inLut_tau1 h.ex _

omit h in
theorem key3W_hon' (χ b g i n : ℕ) (hRE : RE D H b g i n = reP D tb Q Kx V O b g i n) :
    InLut tau3 (key3W D H χ b g i n) := by
  unfold key3W
  split_ifs
  · rw [hRE, qhV_hon]
    exact inLut_tau3 _
  · rw [hRE, qhV'_hon, denV_hon]
    exact inLut_tau3 _

include h

theorem key2_hon (ρ : Reg) (b x : ℕ) : InLut (tau2 D.sh D.u0 tb) (key2 D H ρ b x) := by
  rw [key2, gp_hon, rm_hon, fl_hon, wt_hon]
  exact inLut_tau2 h.ex tb (gpP_range h ρ b x).1 (gpP_range h ρ b x).2

theorem key3W_hon (χ b g : ℕ) {i : ℕ} (hi : i < D.T) (n : ℕ) : InLut tau3 (key3W D H χ b g i n) :=
  key3W_hon' χ b g i n (RE_hon h b g hi n)

theorem lT_le : D.lT ≤ 10 := by
  have h1 := h.T
  rw [D.T_eq] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by simpa using h1)

omit h in
theorem sum_ib_hon (b g : ℕ) {i : ℕ} (hi : i < D.T) :
    ∑ k ∈ range D.lT, 2 ^ k * ibV H k b g i = (jStar D Q Kx b g i : ℤ) := by
  simp only [ibV_hon]
  exact sum_bitZ_of_lt (by rw [← D.T_eq]; exact lt_of_le_of_lt (argTo_spec _ _).1 hi)

theorem key3X_hon (b g : ℕ) {i : ℕ} (hi : i < D.T) : InLut tau3 (key3X D H b g i) := by
  rw [key3X, sum_ib_hon b g hi]
  have hl := lT_le h
  have hj : jStar D Q Kx b g i ≤ i := (argTo_spec _ _).1
  have hi' : i < 2 ^ D.lT := by rw [← D.T_eq]; exact hi
  have e : (2 : ℤ) ^ (16 - D.lT) * 2 ^ D.lT = 2 ^ 16 := by rw [← pow_add]; congr 1; omega
  have hp : (0 : ℤ) < 2 ^ (16 - D.lT) := by positivity
  have h0 : (0 : ℤ) ≤ (i : ℤ) - (jStar D Q Kx b g i : ℤ) := by
    have : (jStar D Q Kx b g i : ℤ) ≤ (i : ℤ) := by exact_mod_cast hj
    linarith
  have h1 : (i : ℤ) - (jStar D Q Kx b g i : ℤ) < 2 ^ D.lT := by
    have : (i : ℤ) < 2 ^ D.lT := by exact_mod_cast hi'
    have h2 : (0 : ℤ) ≤ (jStar D Q Kx b g i : ℤ) := Int.natCast_nonneg _
    linarith
  refine inLut_tau3_of_range (mul_nonneg hp.le h0) ?_
  rw [← e]
  exact mul_lt_mul_of_pos_left h1 hp

/-- Under `Adm` (`h`), for i < T and n < ch: the two high digits are in [0, 2^7). -/
theorem qh_range (b g : ℕ) {i n : ℕ} (hi : i < D.T) (hn : n < D.ch) :
    (0 ≤ reP D tb Q Kx V O b g i n / 2 ^ 16 ∧ reP D tb Q Kx V O b g i n / 2 ^ 16 ≤ 127) ∧
      0 ≤ (2 * denP D tb Q Kx b g i - 1 - reP D tb Q Kx V O b g i n) / 2 ^ 16 ∧
        (2 * denP D tb Q Kx b g i - 1 - reP D tb Q Kx V O b g i n) / 2 ^ 16 ≤ 127 := by
  obtain ⟨r0, r1⟩ := reP_range h b g hi hn
  have hd := (denP_range h b g hi).2
  exact ⟨high_range r0 (by linarith), high_range (by linarith) (by linarith)⟩

theorem key4_hon (b g : ℕ) {i n : ℕ} (hi : i < D.T) (hn : n < D.ch) :
    InLut tau4 (key4 H b g i n) := by
  rw [key4, qhV_hon, qhV'_hon]
  obtain ⟨⟨a0, a1⟩, b0, b1⟩ := qh_range h b g hi hn
  exact inLut_tau4 a0 (by linarith) b0 (by linarith)

omit h in
omit [scl : Scl] in
/-- a property of all keys of two families holds at every index in a piece -/
theorem twoFam_of {P : ℤ → Prop} {nb l l' : ℕ} {f f' : ℕ → ℕ → ℤ} {pad : ℤ}
    (hf : ∀ b y, y < 2 ^ l → P (f b y)) (hf' : ∀ b y, y < 2 ^ l' → P (f' b y))
    {X : ℕ} (hX : X < nb * 2 ^ l + nb * 2 ^ l') :
    P (twoFam nb l l' f f' pad X) := by
  unfold twoFam
  split_ifs with h1 h2
  · exact hf _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  · exact hf' _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  · omega

omit h in
omit [scl : Scl] in
theorem T_pos' : 0 < D.T := Nat.mul_pos D.nBlk_pos D.B_pos
omit h in
omit [scl : Scl] in
theorem ch_pos' : 0 < D.ch := Nat.two_pow_pos _

/-- Under `Adm` (`h`): every key in a piece is an entry of its table. -/
theorem keyVec_hon : ∀ (c : Fin 4) (X : ℕ), X < D.used c → InLut (lut D tb c) (keyVec D tb H c X)
  | 0, _, hX => twoFam_of (fun b y _ => key1_hon h .M b y) (fun b y _ => key1_hon h .D b y) hX
  | 1, _, hX => twoFam_of (fun b y _ => key2_hon h .M b y) (fun b y _ => key2_hon h .D b y) hX
  | 2, _, hX =>
    twoFam_of (fun b y _ => key3W_hon h _ b _ (Nat.mod_lt _ T_pos') _)
      (fun b y _ => key3X_hon h b _ (Nat.mod_lt _ T_pos')) hX
  | 3, X, hX => by
      have hX' : X < D.nb * 2 ^ D.l4 := hX
      have e : keyVec D tb H 3 X =
          key4 H (X / 2 ^ D.l4) (X % 2 ^ D.l4 / D.ch / D.T)
            (X % 2 ^ D.l4 / D.ch % D.T) (X % 2 ^ D.l4 % D.ch) := by
        simp only [keyVec, twoFam, if_pos hX']
      rw [e]
      exact key4_hon h _ _ (Nat.mod_lt _ T_pos') (Nat.mod_lt _ ch_pos')

omit h in
/-- the selected vector of attention keys is that of the least index at which the greatest score is
attained, for i < T -/
theorem sel_hon (b g : ℕ) {i : ℕ} (hi : i < D.T) (n : ℕ) :
    sel D H b g i n = Kx (D.lamOf b) g (jStar D Q Kx b g i) n := by
  have hs : jStar D Q Kx b g i < D.T := lt_of_le_of_lt (argTo_spec _ _).1 hi
  unfold sel
  have e : ∀ j ∈ range D.T, keyV H (D.lamOf b) g j n *
        ∏ k ∈ range D.lT, eq1 (ibV H k b g i) (bitR ℤ k j) =
      if j = jStar D Q Kx b g i then Kx (D.lamOf b) g j n else 0 := fun j hj => by
    have hp := prod_eq1_bitZ (l := D.lT) (j := jStar D Q Kx b g i) (j' := j)
      (by rw [← D.T_eq]; exact hs) (by rw [← D.T_eq]; exact mem_range.1 hj)
    have e2 : ∏ k ∈ range D.lT, eq1 (ibV H k b g i) (bitR ℤ k j) =
        ∏ k ∈ range D.lT, (bitZ k (jStar D Q Kx b g i) * bitZ k j +
          (1 - bitZ k (jStar D Q Kx b g i)) * (1 - bitZ k j)) := rfl
    rw [e2, hp, keyV_hon]
    split_ifs <;> simp
  rw [sum_congr rfl e, sum_ite_eq' (range D.T) (jStar D Q Kx b g i), if_pos (mem_range.2 hs)]

/-- (At1), (At2), (At3). -/
theorem idn_hon : ∀ j : Idn, j.Valid D → idnVal D H j = 0
  | .at1 k b g i, _ => by
      simp only [idnVal, ibV_hon]
      rcases bitZ_01 k (jStar D Q Kx b g i) with e | e <;> rw [e] <;> norm_num
  | .at2 b g i, hv => by
      have hi : i < D.T := hv.2.2
      simp only [idnVal, mxV_hon, qryV_hon, sel_hon b g hi]
      unfold mxP
      rw [maxTo_eq_argTo]
      exact sub_self _
  | .at3 b g i, hv => by
      have hi : i < D.T := hv.2.2
      simp only [idnVal, denV_hon, EF_hon h b g hi]
      exact sub_self _

end Keys

/-! ## Part 6. Cells, and the relation -/

section Cells

variable {D tb Q Kx V O} (h : Adm D tb Q Kx V O)
include h

local notation "H" => honG D tb Q Kx V O

/-- |ac| ≤ 2,047 den, under `Adm` (`h`) -/
theorem abs_acP_le (b g i n : ℕ) : |acP D tb Q Kx V b g i n| ≤ 2047 * denP D tb Q Kx b g i := by
  unfold acP denP
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  have hw := (wtP_range h (b := b) (g := g) (Nat.lt_succ_iff.1 (mem_range.1 hj))).1
  rw [abs_mul, abs_of_nonneg hw, mul_comm]
  exact mul_le_mul_of_nonneg_right (h.v _ g j n) hw

/-- Under `Adm` (`h`), for i < T and n < ch: the output is at most 2,047 in absolute value: it is a
rounded mean of values of val. -/
theorem abs_O_le (b g : ℕ) {i n : ℕ} (hi : i < D.T) (hn : n < D.ch) : |O b g i n| ≤ 2047 := by
  have hd := (denP_range h b g hi).1
  have ha := abs_le.1 (abs_acP_le h b g i n)
  have hpos : 0 < 2 * denP D tb Q Kx b g i := by linarith
  rw [h.o b g i n hn, abs_le]
  constructor
  · exact (Int.le_ediv_iff_mul_le hpos).2 (by nlinarith)
  · exact Int.lt_add_one_iff.1 ((Int.ediv_lt_iff_lt_mul hpos).2 (by nlinarith))

/-- Under `Adm` (`h`): every cell has absolute value at most 128. -/
theorem abs_hon_le : ∀ c : Raw, c.Valid D → |H c| ≤ 128
  | .c ρ jj b x, hv => by
      have hjj : jj < 5 := hv.1
      obtain ⟨r0, r1⟩ := rmOf_range h.ex (gpP D Q Kx ρ b x)
      obtain ⟨w0, w1⟩ := wOf_range (sh := D.sh) h.exp (gpP_range h ρ b x).1
      have hf := flOf_01 (sh := D.sh) (u0 := D.u0) (gpP D Q Kx ρ b x)
      rw [abs_le]
      interval_cases jj <;> simp only [honG]
      · constructor <;> omega
      · constructor <;> omega
      · rcases hf with e | e <;> rw [e] <;> norm_num
      · constructor <;> omega
      · constructor <;> omega
  | .mx k b g i, hv =>
      writable_of_abs_le (n := 4) _ ((abs_mxP_le h b g i).trans (by unfold Smax; norm_num)) k hv.1
  | .den k b g i, hv => by
      obtain ⟨d0, d1⟩ := denP_range h b g hv.2.2.2
      exact writable_of_abs_le (n := 4) _
        (by rw [abs_of_nonneg (by linarith)]; exact d1.trans (by norm_num)) k hv.1
  | .ib k b g i, _ => by
      show |bitZ k _| ≤ 128
      rcases bitZ_01 k (jStar D Q Kx b g i) with e | e <;> rw [e] <;> norm_num
  | .qh b g i n, hv => by
      obtain ⟨⟨a0, a1⟩, -⟩ := qh_range h b g hv.2.2.1 hv.2.2.2
      show |reP D tb Q Kx V O b g i n / 2 ^ 16 - 128| ≤ 128
      rw [abs_le]
      constructor <;> linarith
  | .qh' b g i n, hv => by
      obtain ⟨-, a0, a1⟩ := qh_range h b g hv.2.2.1 hv.2.2.2
      show |(2 * denP D tb Q Kx b g i - 1 - reP D tb Q Kx V O b g i n) / 2 ^ 16 - 128| ≤ 128
      rw [abs_le]
      constructor <;> linarith
  | .qry k b g i n, hv => writable_of_abs_le (n := 2) _ ((h.q b g i n).trans (by norm_num)) k hv.1
  | .out k b g i n, hv =>
    writable_of_abs_le (n := 2) _
      ((abs_O_le h b g hv.2.2.2.1 hv.2.2.2.2).trans (by norm_num)) k hv.1
  | .key k lam g j n, hv =>
    writable_of_abs_le (n := 2) _ ((h.k lam g j n).trans (by norm_num)) k hv.1
  | .val k lam g j n, hv =>
    writable_of_abs_le (n := 2) _ ((h.v lam g j n).trans (by norm_num)) k hv.1

/-- Under `Adm` (`h`): the honest trace satisfies the relation over the integers. -/
theorem rfraw_hon : RFraw D tb ℤ H := by
  refine ⟨fun c hc => lt_of_le_of_lt (abs_hon_le h c hc) (by norm_num),
    fun c X hX => ?_, fun j hj => ?_⟩
  · rw [castT_int]
    obtain ⟨ι, h1, h2⟩ := keyVec_hon h c X hX
    exact ⟨ι, h1, by rw [h2, Int.cast_id]⟩
  · rw [castT_int]
    exact idn_hon h j hj

end Cells

end Inst.Model.AttSeg.Hon

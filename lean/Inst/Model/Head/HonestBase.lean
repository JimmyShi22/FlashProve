-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/HonestBase.lean: the head segment's honest trace without hidden numbers, for every
valid final normalisation. It is the base of the honest trace of Inst/Model/Head/HonestN.lean.

Hidden numbers: `Hid` (Inst/Model/Head/PolicyDefs.lean). A position i is counted if r ≤ i < min(e,
1,023) (`Req.rhoC`, Inst/Model/Head/Index.lean). The honest trace takes from here the cells of the
final normalisation (x, hd, the arrays nw and rn, the ledger's bytes below 99). The arrays d1, d2,
ex and the bytes 99 to 119 as defined here (no hidden number; bytes 0) meet the field relation only
for a request without a counted position [no theorem here]. The cell rule is the widened cell
rule of Inst/Model/Widened.lean. The final normalisation is an argument np with `NormPar.OK`.
  `N.Rz`, `ywv`, `outv`, `rnv`, `lgv`, `mgv`, `K1v`, `K2v`, `d1v`, `d2v`, `exv`
      the honest values, from the residual stream x, the output matrix H and the request y (covered
      positions y.r ≤ i < y.e; checked tokens y.win i). No hidden number enters the margin
  `N.HonIn0 np x H y`      what is assumed: np is valid; NORM does not halt at any position; |H| ≤
                           2^12; every margin at a covered position below 1,024 is ≥ 0
Form: after Inst/Model/Head/Honest.lean.
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.Head.NoWrapN
import Inst.Model.Common.LedgerHonest
import Inst.Model.Common.Site
import Inst.Model.Widened
import Inst.Model.TablesSanity

set_option autoImplicit false

namespace Inst.Model.Head.N

open Finset

section Values
variable (np : NormPar) (x : ℕ → Vec) (H : Mat) (y : Req)

/-- the values of (N3), (N4), (N5) in the call NORM(x_i) of (PH1) -/
def Rz (i : ℕ) : ℤ := NORM.R np nD (x i)
def ywv (i j : ℕ) : ℤ := NORM.yw np nD (x i) j
def outv (i j : ℕ) : ℤ := NORM.out np nD (x i) j
/-- rn = ⌊(x R + 2^(K−1) − 2^K nw) / 2^16⌋: the high digit of the remainder of the rounding
(`Site.hd` of Inst/Model/Common/Site.lean, by unfolding) -/
def rnv (i j : ℕ) : ℤ := (x i j * Rz np x i + 2 ^ (np.K - 1) - 2 ^ np.K * ywv np x i j) / 2 ^ 16
/-- the logits at position i, and the margins of the checked token y.win i -/
def lgv (i v : ℕ) : ℤ := ∑ j ∈ range nD, outv np x i j * H j v
def mgv (i v : ℕ) : ℤ := lgv np x H i (y.win i) - lgv np x H i v - if v < y.win i then 1 else 0
/-- K_2 = mg mod 2^8 and mh = ⌊mg / 2^8⌋; K_1 = mh if mh < 2^15, and K_1 = 2^15 + (mh mod 2^15)
otherwise -/
def K2v (i v : ℕ) : ℤ := mgv np x H y i v % 2 ^ 8
def mhv (i v : ℕ) : ℤ := mgv np x H y i v / 2 ^ 8
def K1v (i v : ℕ) : ℤ :=
  if mhv np x H y i v < 2 ^ 15 then mhv np x H y i v else 2 ^ 15 + mhv np x H y i v % 2 ^ 15
/-- d1 = K_1 − 32,896, d2 = K_2 − 128 and ex = EX[K_1] at the covered positions y.r ≤ i < y.e.
At all other positions d1 = d2 = 0 and ex = 2^24 -/
def d1v (i v : ℕ) : ℤ := if y.r ≤ i ∧ i < y.e then K1v np x H y i v - 32896 else 0
def d2v (i v : ℕ) : ℤ := if y.r ≤ i ∧ i < y.e then K2v np x H y i v - 128 else 0
def exv (i v : ℕ) : ℤ := if y.r ≤ i ∧ i < y.e then EX (K1v np x H y i v).toNat else 2 ^ 24
/-- the five cells of x_i[j] (written by the last feed-forward segment) -/
def bX (i l j : ℕ) : ℤ := cellW 5 (x i j) l

/-- The cells without hidden numbers (the honest cells of a request without a counted position; the
base of `N.honCells`). The ledger's bytes 99 to 119 are 0, so their cells are −128; filler cells are
0. -/
def honBase : Cells ℤ where
  x := fun φ i => cellW 5 (x i (φ % 5120)) (φ / 5120)
  hd := fun φ i => cellW 2 (outv np x i (φ % 5120)) (φ / 5120)
  hr := fun n i => if n < 99 then Ledger.hon np nD (bX x i) n - 128 else -128
  hf := fun φ i =>
    if φ < 10240 then cellW 2 (ywv np x i (φ % 5120)) (φ / 5120)
    else if φ < 20480 then cellW 2 (rnv np x i ((φ - 10240) % 5120) - 32896) ((φ - 10240) / 5120)
    else if φ < 424576 then cellW 2 (d1v np x H y i ((φ - 20480) % 202048)) ((φ - 20480) / 202048)
    else if φ < 626624 then d2v np x H y i (φ - 424576)
    else if φ < 1232768 then
      cellW 3 (exv np x H y i ((φ - 626624) % 202048) - 8421505) ((φ - 626624) / 202048)
    else 0

/-! ## The arrays of the honest cells are the honest values -/

theorem rd_cellW {n : ℕ} (hn : 1 ≤ n) (a : ℤ) (c : ℕ → ℤ) (hc : ∀ l < n, c l = cellW n a l) :
    rd n c = a := by
  unfold rd
  rw [sum_congr rfl fun l hl => by rw [hc l (mem_range.1 hl)]]
  exact sum_cellW hn a

theorem hon_bl {l j : ℕ} (hj : j < nD) (i : ℕ) : bl (honBase np x H y) l j i = bX x i l j := by
  show cellW 5 (x i ((5120 * l + j) % 5120)) ((5120 * l + j) / 5120) = cellW 5 (x i j) l
  have h1 : (5120 * l + j) % 5120 = j := by unfold nD at hj; omega
  have h2 : (5120 * l + j) / 5120 = l := by unfold nD at hj; omega
  rw [h1, h2]
theorem hon_xv {j : ℕ} (hj : j < nD) (i : ℕ) : xv (honBase np x H y) j i = x i j :=
  rd_cellW (by norm_num) _ _ fun l _ => hon_bl np x H y hj i
theorem hon_nw {j : ℕ} (hj : j < nD) (i : ℕ) : nw (honBase np x H y) j i = ywv np x i j := by
  refine rd_cellW (by norm_num) _ _ fun l hl => ?_
  show (honBase np x H y).hf (5120 * l + j) i = _
  unfold nD at hj
  simp only [honBase]
  rw [if_pos (by omega), show (5120 * l + j) % 5120 = j by omega,
    show (5120 * l + j) / 5120 = l by omega]
theorem hon_rn {j : ℕ} (hj : j < nD) (i : ℕ) : rn (honBase np x H y) j i = rnv np x i j := by
  have : rd 2 (fun l => (honBase np x H y).hf (fRn l j) i) = rnv np x i j - 32896 := by
    refine rd_cellW (by norm_num) _ _ fun l hl => ?_
    show (honBase np x H y).hf (10240 + 5120 * l + j) i = _
    unfold nD at hj
    simp only [honBase]
    rw [if_neg (by omega), if_pos (by omega),
      show (10240 + 5120 * l + j - 10240) % 5120 = j by omega,
      show (10240 + 5120 * l + j - 10240) / 5120 = l by omega]
  unfold rn
  rw [this]
  ring
theorem hon_d1 {v : ℕ} (hv : v < nV) (i : ℕ) : d1 (honBase np x H y) v i = d1v np x H y i v := by
  refine rd_cellW (by norm_num) _ _ fun l hl => ?_
  show (honBase np x H y).hf (20480 + 202048 * l + v) i = _
  unfold nV at hv
  simp only [honBase]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (20480 + 202048 * l + v - 20480) % 202048 = v by omega,
    show (20480 + 202048 * l + v - 20480) / 202048 = l by omega]
theorem hon_d2 {v : ℕ} (hv : v < nV) (i : ℕ) : d2 (honBase np x H y) v i = d2v np x H y i v := by
  show (honBase np x H y).hf (424576 + v) i = _
  unfold nV at hv
  simp only [honBase]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show 424576 + v - 424576 = v by omega]
theorem hon_ex {v : ℕ} (hv : v < nV) (i : ℕ) : ex (honBase np x H y) v i = exv np x H y i v := by
  have : rd 3 (fun l => (honBase np x H y).hf (fEx l v) i) = exv np x H y i v - 8421505 := by
    refine rd_cellW (by norm_num) _ _ fun l hl => ?_
    show (honBase np x H y).hf (626624 + 202048 * l + v) i = _
    unfold nV at hv
    simp only [honBase]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega), show (626624 + 202048 * l + v - 626624) % 202048 = v by omega,
      show (626624 + 202048 * l + v - 626624) / 202048 = l by omega]
  unfold ex
  rw [this]
  ring
theorem hon_nrm {j : ℕ} (hj : j < nD) (i : ℕ) : nrm (honBase np x H y) j i = outv np x i j := by
  refine rd_cellW (by norm_num) _ _ fun l hl => ?_
  show cellW 2 (outv np x i ((5120 * l + j) % 5120)) ((5120 * l + j) / 5120) = _
  unfold nD at hj
  rw [show (5120 * l + j) % 5120 = j by omega, show (5120 * l + j) / 5120 = l by omega]
theorem hon_Dv (n i : ℕ) :
    Dv (honBase np x H y) n i = if n < 99 then Ledger.hon np nD (bX x i) n else 0 := by
  show 128 + (if n < 99 then Ledger.hon np nD (bX x i) n - 128 else -128) = _
  split_ifs <;> ring
theorem xOf_bX (i : ℕ) : Ledger.xOf (bX x i) = x i :=
  funext fun j => sum_cellW (by norm_num) (x i j)

end Values

/-! ## What is assumed, and the ranges of the honest values -/

/-- What is assumed of the run of the program: the final normalisation is valid; NORM does not halt
at any position; |H| ≤ 2^12; every margin at a covered position below 1,024 is ≥ 0. -/
structure HonIn0 (np : NormPar) (x : ℕ → Vec) (H : Mat) (y : Req) : Prop where
  /-- the final normalisation is valid -/
  nf : np.OK
  ok : ∀ i < nT, NORM.OK np nD (x i)
  hH : ∀ j v, |H j v| ≤ 2 ^ 12
  out : ∀ i < nT, y.r ≤ i → i < y.e → ∀ v < nV, 0 ≤ mgv np x H y i v

section Facts
variable {np : NormPar} {x : ℕ → Vec} {H : Mat} {y : Req} (h : HonIn0 np x H y)
include h

theorem honHyp {i : ℕ} (hi : i < nT) : Ledger.HonHyp np nD (bX x i) where
  eps_pos := h.nf.1
  eps_lt := h.nf.2.1
  M_le := h.nf.2.2.2.1
  d_le := by decide
  cell := fun l hl j hj =>
    writable_of_abs_le (n := 5) (x i j) (abs_le_of_normOK h.nf.1 (h.ok i hi) hj) l hl
  fits := by rw [xOf_bX]; exact (h.ok i hi).1

theorem yw_fits {i j : ℕ} (hi : i < nT) (hj : j < nD) : Fits16 (ywv np x i j) := (h.ok i hi).2 j hj

omit h in
theorem out_abs (i j : ℕ) : -2047 ≤ outv np x i j ∧ outv np x i j ≤ 2047 := by
  unfold outv NORM.out clamp
  omega

/-- under `HonIn0`: the high digit rn is in [0, 2^16) -/
theorem rn_range (i j : ℕ) : 0 ≤ rnv np x i j ∧ rnv np x i j < 2 ^ 16 := by
  obtain ⟨-, -, -, -, hK17, hK32, -⟩ := h.nf
  have a := Site.hd_bounds (x i j * Rz np x i) (k := np.K) (by omega)
  have b : (2 : ℤ) ^ (np.K - 16) ≤ 2 ^ 16 := pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨a.1, lt_of_lt_of_le a.2 b⟩

theorem lgv_abs (i v : ℕ) : |lgv np x H i v| ≤ 42928701440 := by
  unfold lgv
  calc
    |∑ j ∈ range nD,
      outv np x i j * H j v| ≤ ∑ j ∈ range nD, |outv np x i j * H j v| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range nD, (2047 * 2 ^ 12 : ℤ) := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_le.2 (out_abs i j)) (h.hH j v) (abs_nonneg _) (by norm_num)
    _ = 42928701440 := by simp [nD]

theorem mg_range {i : ℕ} (hi : i < nT) (hc : y.r ≤ i ∧ i < y.e) {v : ℕ} (hv : v < nV) :
    0 ≤ mgv np x H y i v ∧ mgv np x H y i v ≤ 85857402880 := by
  refine ⟨h.out i hi hc.1 hc.2 v hv, ?_⟩
  have a := abs_le.1 (lgv_abs h i (y.win i))
  have b := abs_le.1 (lgv_abs h i v)
  unfold mgv
  split_ifs <;> omega

/-- under `HonIn0`, at a covered position below 1,024 and v < V: K_2 is in [0, 2^8), K_1 in [0,
2^16), and margin − 2^8 K_1 − K_2 = 2^23 K_0 for some K_0 in [0, 2^16) -/
theorem digits {i : ℕ} (hi : i < nT) (hc : y.r ≤ i ∧ i < y.e) {v : ℕ} (hv : v < nV) :
    (0 ≤ K2v np x H y i v ∧ K2v np x H y i v < 2 ^ 8) ∧
    (0 ≤ K1v np x H y i v ∧ K1v np x H y i v < 2 ^ 16) ∧
    ∃ K0 : ℤ,
      0 ≤ K0 ∧ K0 < 2 ^ 16 ∧
      mgv np x H y i v - 2 ^ 8 * K1v np x H y i v - K2v np x H y i v = 2 ^ 23 * K0 := by
  obtain ⟨m0, m1⟩ := mg_range h hi hc hv
  unfold K1v K2v mhv
  generalize mgv np x H y i v = m at *
  refine ⟨by omega, by split_ifs <;> omega, ?_⟩
  split_ifs with hlt
  · exact ⟨0, le_refl 0, by norm_num, by omega⟩
  · exact ⟨m / 2 ^ 8 / 2 ^ 15 - 1, by omega, by omega, by omega⟩

end Facts

/-! ## `Ledger.R`, `Ledger.cs` at s ≤ 9 and the 17 identities depend only on the bytes below 99 -/

section Congr
variable {D D' : ℕ → ℤ} (hD : ∀ n < 99, D n = D' n)
include hD

theorem b256_congr {a n : ℕ} (han : a + n ≤ 99) : Ledger.b256 D a n = Ledger.b256 D' a n :=
  sum_congr rfl fun l hl => by rw [hD (a + l) (by have := mem_range.1 hl; omega)]

theorem R_congr : Ledger.R D = Ledger.R D' := by
  unfold Ledger.R Ledger.Rlo Ledger.Rhi
  rw [b256_congr hD (by norm_num), b256_congr hD (by norm_num)]

theorem cs_congr {s : ℕ} (hs : s ≤ 9) : Ledger.cs D s = Ledger.cs D' s := by
  unfold Ledger.cs
  split_ifs
  · rfl
  · exact hD 9 (by norm_num)
  · rw [b256_congr hD (by omega)]

theorem idn_congr (np : NormPar) (Ws : ℕ → ℤ) {k : ℕ} (hk : k < 17) :
    Ledger.idn np Ws D k = Ledger.idn np Ws D' k := by
  have e1 : Ledger.sa D = Ledger.sa D' := by unfold Ledger.sa; rw [hD 58 (by norm_num), hD 59 (by norm_num), hD 60 (by norm_num), hD 61 (by norm_num)]
  have e2 : Ledger.sb D = Ledger.sb D' := by
    unfold Ledger.sb; rw [hD 62 (by norm_num), hD 63 (by norm_num)]
  have e3 : Ledger.sig D = Ledger.sig D' := by unfold Ledger.sig; rw [e1, e2]
  have e4 : Ledger.s0 D = Ledger.s0 D' := hD 59 (by norm_num)
  have e5 : Ledger.kc D = Ledger.kc D' := by unfold Ledger.kc; rw [hD 79 (by norm_num)]
  by_cases hk9 : k < 9
  · rw [Ledger.idn_j1 np _ _ hk9, Ledger.idn_j1 np _ _ hk9, cs_congr hD (by omega),
      cs_congr hD (by omega), hD k (by omega)]
  · have hc : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Ledger.idn_j2, e1, e2, Ledger.Blo, Ledger.Bhi,
        b256_congr hD (show 74 + 3 ≤ 99 by norm_num), b256_congr hD (show 77 + 2 ≤ 99 by norm_num)]
    · simp only [Ledger.idn_j3, e1, e5, Ledger.Vlo, Ledger.Blo, Ledger.l1,
        b256_congr hD (show 0 + 6 ≤ 99 by norm_num), b256_congr hD (show 74 + 3 ≤ 99 by norm_num),
        b256_congr hD (show 64 + 5 ≤ 99 by norm_num)]
    · simp only [Ledger.idn_j4, e2, e5, Ledger.Vhi, Ledger.Bhi,
        b256_congr hD (show 6 + 4 ≤ 99 by norm_num), b256_congr hD (show 77 + 2 ≤ 99 by norm_num)]
    · simp only [Ledger.idn_j5, e3, Ledger.l1, Ledger.h1,
        b256_congr hD (show 64 + 5 ≤ 99 by norm_num), b256_congr hD (show 69 + 5 ≤ 99 by norm_num)]
    · simp only [Ledger.idn_j6, e1, e2, Ledger.Rlo, Ledger.Rhi, Ledger.q1,
        b256_congr hD (show 80 + 3 ≤ 99 by norm_num), b256_congr hD (show 83 + 3 ≤ 99 by norm_num),
        b256_congr hD (show 86 + 3 ≤ 99 by norm_num)]
    · simp only [Ledger.idn_j7, e2, Ledger.Rhi, b256_congr hD (show 83 + 3 ≤ 99 by norm_num)]
    · simp only [Ledger.idn_j8, e1, e3, e4, Ledger.Rlo, Ledger.q1, Ledger.rr,
        b256_congr hD (show 80 + 3 ≤ 99 by norm_num), b256_congr hD (show 86 + 3 ≤ 99 by norm_num),
        b256_congr hD (show 89 + 5 ≤ 99 by norm_num)]
    · simp only [Ledger.idn_j9, e3, Ledger.rr, Ledger.rq,
        b256_congr hD (show 89 + 5 ≤ 99 by norm_num), b256_congr hD (show 94 + 5 ≤ 99 by norm_num)]

end Congr

/-! ## Under `HonIn0` every cell of `honBase` is at most 128 in absolute value -/

section Main
variable {np : NormPar} {x : ℕ → Vec} {H : Mat} {y : Req} (h : HonIn0 np x H y)
include h

omit h in
theorem un_vals : un 1 = 1 ∧ un 2 = 257 ∧ un 3 = 65793 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [un, sum_range_succ]

theorem d1v_range {v : ℕ} (hv : v < nV) {i : ℕ} (hi : i < nT) :
    -32896 ≤ d1v np x H y i v ∧ d1v np x H y i v ≤ 32639 := by
  unfold d1v
  split_ifs with hc
  · have := (digits h hi hc hv).2.1
    omega
  · omega
theorem d2v_range {v : ℕ} (hv : v < nV) {i : ℕ} (hi : i < nT) :
    -128 ≤ d2v np x H y i v ∧ d2v np x H y i v ≤ 127 := by
  unfold d2v
  split_ifs with hc
  · have := (digits h hi hc hv).1
    omega
  · omega
omit h in
theorem exv_range (i v : ℕ) : 1 ≤ exv np x H y i v ∧ exv np x H y i v ≤ 2 ^ 24 := by
  unfold exv
  split_ifs
  · exact TablesSanity.tab9.2 _
  · norm_num

/-- Under `HonIn0`, in the widened form of the cell rule: every cell of `honBase`, and of the
borrowed x, has absolute value at most 128. -/
theorem base_cells_le {i : ℕ} (hi : i < nT) :
    (∀ φ < nFeat .hf, |(honBase np x H y).hf φ i| ≤ 128) ∧
    (∀ φ < nFeat .hd, |(honBase np x H y).hd φ i| ≤ 128) ∧
    (∀ φ < nFeat .hr, |(honBase np x H y).hr φ i| ≤ 128) ∧
    ∀ φ < nFeat .x, |(honBase np x H y).x φ i| ≤ 128 := by
  obtain ⟨u1, u2, u3⟩ := un_vals
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun n _ => ?_, fun φ hφ => ?_⟩
  · simp only [nFeat] at hφ
    simp only [honBase]
    split_ifs with c1 c2 c3 c4
    · exact writable_two_of_fits16 (yw_fits h hi (by unfold nD; omega)) _ (by omega)
    · refine (writable_iff (n := 2) (by norm_num) _).2 ?_ _ (by omega)
      have := rn_range h i ((φ - 10240) % 5120)
      simp only [u2, u1, Nat.add_one_sub_one]
      constructor <;> omega
    · refine (writable_iff (n := 2) (by norm_num) _).2 ?_ _ (by omega)
      have := d1v_range h (v := (φ - 20480) % 202048) (by unfold nV; omega) hi
      simp only [u2, u1, Nat.reduceSub]
      constructor <;> omega
    · have := d2v_range h (v := φ - 424576) (by unfold nV; omega) hi
      rw [abs_le]
      constructor <;> omega
    · refine (writable_iff (n := 3) (by norm_num) _).2 ?_ _ (by omega)
      have := exv_range (np := np) (x := x) (H := H) (y := y) i ((φ - 626624) % 202048)
      simp only [u3, u2, Nat.reduceSub]
      constructor <;> omega
  · simp only [nFeat] at hφ
    refine writable_of_abs_le (n := 2) _ ?_ _ (by omega)
    have := out_abs (np := np) (x := x) i (φ % 5120)
    rw [abs_le]
    constructor <;> omega
  · simp only [honBase]
    split_ifs with c
    · have := Ledger.hon_cell (honHyp h hi) c
      rw [abs_le]
      constructor <;> omega
    · norm_num
  · simp only [nFeat] at hφ
    exact writable_of_abs_le (n := 5) _
      (abs_le_of_normOK h.nf.1 (h.ok i hi) (by unfold nD; omega)) _ (by omega)

/-! ## Under `HonIn0`: the ledger, the logits and the digits of `honBase` -/

omit h in
theorem hon_led {i : ℕ} :
    ∀ n < 99, Dv (honBase np x H y) n i = Ledger.hon np nD (bX x i) n := fun n hn => by
  rw [hon_Dv, if_pos hn]

theorem hon_Rz {i : ℕ} (hi : i < nT) :
    Ledger.R (fun n => Dv (honBase np x H y) n i) = Rz np x i := by
  rw [R_congr hon_led, Ledger.hon_R (honHyp h hi), xOf_bX]
  rfl

omit h in
theorem hon_lg (i v : ℕ) : lg (honBase np x H y) H i v = lgv np x H i v :=
  sum_congr rfl fun j hj => by rw [hon_nrm np x H y (mem_range.1 hj)]

omit h in
theorem hon_K1 {v : ℕ} (hv : v < nV) (i : ℕ) :
    K1 (honBase np x H y) y v i = if y.r ≤ i ∧ i < y.e then K1v np x H y i v else 0 := by
  simp only [K1, hon_d1 np x H y hv, d1v, Req.rho, Int.cast_id]
  split_ifs <;> ring
omit h in
theorem hon_K2 {v : ℕ} (hv : v < nV) (i : ℕ) :
    K2 (honBase np x H y) y v i = if y.r ≤ i ∧ i < y.e then K2v np x H y i v else 0 := by
  simp only [K2, hon_d2 np x H y hv, d2v, Req.rho, Int.cast_id]
  split_ifs <;> ring
omit h in
theorem hon_mg (hc : ∀ i, y.rhoC i = 0) (v i : ℕ) :
    mg (honBase np x H y) H y v i = if y.r ≤ i ∧ i < y.e then mgv np x H y i v else 0 := by
  unfold mg Req.rho mgv
  rw [hc i]
  split_ifs <;> simp [hon_lg]

end Main

/-! ## From the last steps of the program -/

/-- If the final normalisation np is valid (hn), every entry of H is at most 2^12 in absolute value
(hH), the final normalisation of the residual stream X does not halt at any position and at every
covered position the checked token is the least index of a greatest logit at that position, then
`HonIn0` holds for X, H and y. The logits are written as in Inst/Model/Program.lean, so that the
hypotheses unfold from `Runs`, or `RunsK`, and from `lg`, or `lgK`. -/
theorem honIn0_stream {np : NormPar} (hn : np.OK) {X : ℕ → Vec} {H : Mat}
    (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {y : Req} (hok : ∀ i < nT, NORM.OK np nD (X i))
    (h1 : ∀ i < nT, y.r ≤ i → i < y.e →
      ∀ v < nV, dot nD (NORM.out np nD (X i)) (fun j => H j v) ≤
        dot nD (NORM.out np nD (X i)) fun j => H j (y.win i))
    (h2 : ∀ i < nT, y.r ≤ i → i < y.e →
      ∀ v < y.win i, dot nD (NORM.out np nD (X i)) (fun j => H j v) <
        dot nD (NORM.out np nD (X i)) fun j => H j (y.win i)) : HonIn0 np X H y where
  nf := hn
  ok := hok
  hH := hH
  out := fun i hi hr he v hv => by
    have e : ∀ v, lgv np X H i v = dot nD (NORM.out np nD (X i)) fun j => H j v := fun _ => rfl
    unfold mgv
    rw [e, e]
    split_ifs with hlt
    · have := h2 i hi hr he v hlt
      omega
    · have := h1 i hi hr he v hv
      omega

/-- At the request for the next token after 1,024 tokens: `HonIn0` from hn, hH and hok as in
`honIn0_stream`, and the hypotheses that y is the least index of a greatest logit at position 1,023.
-/
theorem honIn0_stream_last {np : NormPar} (hn : np.OK) {X : ℕ → Vec} {H : Mat}
    (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {y : ℕ} (hok : ∀ i < nT, NORM.OK np nD (X i))
    (h1 : ∀ v < nV, dot nD (NORM.out np nD (X 1023)) (fun j => H j v) ≤
      dot nD (NORM.out np nD (X 1023)) fun j => H j y)
    (h2 : ∀ v < y, dot nD (NORM.out np nD (X 1023)) (fun j => H j v) <
      dot nD (NORM.out np nD (X 1023)) fun j => H j y) : HonIn0 np X H (Req.last y) :=
  honIn0_stream hn hH hok
    (fun i _ hr he => by
      have e : i = 1023 := by
        have a : 1023 ≤ i := hr
        have b : i < 1024 := he
        omega
      subst e; exact h1)
    (fun i _ hr he => by
      have e : i = 1023 := by
        have a : 1023 ≤ i := hr
        have b : i < 1024 := he
        omega
      subst e; exact h2)

end Inst.Model.Head.N

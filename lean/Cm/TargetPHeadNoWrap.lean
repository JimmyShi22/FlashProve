-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPHeadNoWrap.lean: the plain head with the scaled table (Cm/TargetPHead.lean): no
wrap-around, for every lawful final normalisation, at a variable number p.

"No wrap-around": what holds modulo p of the cells' small integers is shown to hold over the
integers, for a variable number p with 2^61 - 1 ≤ p (the class `Big p`: Inst/Model/Bound/Base.lean;
that p is prime is not assumed). In the margin step (`step_H6`) the key of the family HD0 is
congruent to 2^23 u by the table itself; no step multiplies by 2^23. A position i is covered if
y.r ≤ i < y.e; the token that it checks is `y.win i`; the borrowed cells are `t.x`.

Main names:
  `RFz p np H y t`: the field relation of the head, as congruences modulo p between integers.
    `rfz_of_rf`, `rf_of_rfz`: it is the field relation over `ZMod p` (`RF`, Cm/TargetPHead.lean)
    for the image of an integer matrix H; for every number p.
  `step_H6` (for a trace t with `h : RFz p np H y t`, under `hH`): at every covered position the
    margin of every token is at least 0.
  `step_H4_K1`, `step_H4_K2`, `step_H3`, `step_H1`, `step_H2`, `step_H5`: digits of a margin in
    their ranges; clamp; ledger; rounding; the bound 5,120 · 2,047 · 2^12 on a logit; each under the
    hypotheses of its statement.
  `noWrap`: under `h : RFz p np H y t`, `Big p`, a lawful final normalisation (`hn`) and entries of
    H of at most 2^12 in absolute value (`hH`): see its docstring.
  `head_stream`, `head_stream_gap`: the same for a stream X that the borrowed cells hold (`hx`;
    `head_stream_gap`: `hy : y.OK` besides): see their docstrings.

Why: `Big p` gives 2^61 - 1 ≤ p among integers (`big_int`) where a congruence between small
integers is lifted to an equation, and lifts the ledger's size conditions to p
(`Cm.TI.Ledger.Adm.mono`).

Limits: what is asked: the final normalisation is lawful (`NormPar.OK`: 1 ≤ ϵ < 2^48, 24 ≤ M ≤ 47,
17 ≤ K ≤ 32, M − 14 ≤ K); every entry of H is at most 2^12 in absolute value; in
`head_stream_gap` also `y.OK`.
This file says nothing at a position that is not covered, but that the normalisation does not halt
there, that nw and nrm are its values and that |x| < 2^39 (`noWrap`, first clause), and what `hf_lt`
to `step_H5` state, which hold at every position. The namespace is `Cm.Plain.TP`.
Steps H1 and H1a (the ledger) are in Inst/Model/Common/LedgerSound.lean (`ledger_sound`); the
rounding with its high digit is in Inst/Model/Common/Site.lean. No file of this library defines the
labels H1 to H7 and (FH3) to (FH17).
Terms: lean/GLOSSARY.md.
-/
import Cm.HeadNoWrap
import Cm.TargetPHead
import Inst.Model.Bound.Base


set_option autoImplicit false

namespace Cm.Plain.TP

open Cm.TI

open Inst.Model Inst.Model.Head Finset

/-- The field relation of the head, as congruences between integers. -/
structure RFz (p : ℕ) (np : NormPar) (H : Mat) (y : Req) (t : Cells ℤ) : Prop where
  small : Small (2 ^ 18) t
  keys : ∀ s x i, x < len s → i < nT →
    ∃ u < (tableOf s).rows, key np t H y s x i ≡ (tableOf s).row u [ZMOD (p : ℤ)]
  idns : ∀ i < nT, ∀ k < 17, idn np t i k ≡ 0 [ZMOD (p : ℤ)]

section Steps
variable {p : ℕ} [Big p] {np : NormPar} {H : Mat} {y : Req} {t : Cells ℤ} (h : RFz p np H y t)
include h

/-! What condition (1) gives (Table S48), for the cells that the steps read. -/

omit [Big p] in
theorem hf_lt {φ i : ℕ} (hφ : φ < nHf) (hi : i < nT) : -2 ^ 18 < t.hf φ i ∧ t.hf φ i < 2 ^ 18 :=
  abs_lt.1 ((h.small i hi).1 φ hφ)
omit [Big p] in
theorem hd_lt {φ i : ℕ} (hφ : φ < nFeat .hd) (hi : i < nT) :
    -2 ^ 18 < t.hd φ i ∧ t.hd φ i < 2 ^ 18 :=
  abs_lt.1 ((h.small i hi).2.1 φ hφ)
omit [Big p] in
theorem hr_lt {φ i : ℕ} (hφ : φ < nHr) (hi : i < nT) : -2 ^ 18 < t.hr φ i ∧ t.hr φ i < 2 ^ 18 :=
  abs_lt.1 ((h.small i hi).2.2.1 φ hφ)
omit [Big p] in
theorem x_lt {φ i : ℕ} (hφ : φ < nFeat .x) (hi : i < nT) : -2 ^ 18 < t.x φ i ∧ t.x φ i < 2 ^ 18 :=
  abs_lt.1 ((h.small i hi).2.2.2 φ hφ)

omit [Big p] in
theorem nw_abs {j i : ℕ} (hj : j < nD) (hi : i < nT) :
    -67371008 < nw t j i ∧ nw t j i < 67371008 := by
  have a := hf_lt h (φ := fNw 0 j) (by simp only [fNw, nHf, nD] at *; omega) hi
  have b := hf_lt h (φ := fNw 1 j) (by simp only [fNw, nHf, nD] at *; omega) hi
  rw [N.nw_eq]
  norm_num at a b
  omega
omit [Big p] in
theorem rn_abs {j i : ℕ} (hj : j < nD) (hi : i < nT) :
    -67403904 < rn t j i ∧ rn t j i < 67403904 := by
  have a := hf_lt h (φ := fRn 0 j) (by simp only [fRn, nHf, nD] at *; omega) hi
  have b := hf_lt h (φ := fRn 1 j) (by simp only [fRn, nHf, nD] at *; omega) hi
  rw [N.rn_eq]
  norm_num at a b
  omega
omit [Big p] in
theorem nrm_abs {j i : ℕ} (hj : j < nD) (hi : i < nT) :
    -67371008 < nrm t j i ∧ nrm t j i < 67371008 := by
  have a := hd_lt h (φ := fNrm 0 j) (by simp only [fNrm, nFeat, nD] at *; omega) hi
  have b := hd_lt h (φ := fNrm 1 j) (by simp only [fNrm, nFeat, nD] at *; omega) hi
  rw [N.nrm_eq]
  norm_num at a b
  omega
omit [Big p] in
theorem K1_abs {v i : ℕ} (hv : v < nV) (hi : i < nT) :
    -67403904 < K1 t y v i ∧ K1 t y v i < 67403904 := by
  have a := hf_lt h (φ := fD1 0 v) (by simp only [fD1, nHf, nV] at *; omega) hi
  have b := hf_lt h (φ := fD1 1 v) (by simp only [fD1, nHf, nV] at *; omega) hi
  have r := y.rho_01 i
  simp only [K1, N.d1_eq, Int.cast_id]
  norm_num at a b
  rcases r with r | r <;> rw [r] <;> omega
omit [Big p] in
theorem K2_abs {v i : ℕ} (hv : v < nV) (hi : i < nT) :
    -262272 < K2 t y v i ∧ K2 t y v i < 262272 := by
  have a := hf_lt h (φ := fD2 v) (by simp only [fD2, nHf, nV] at *; omega) hi
  have r := y.rho_01 i
  simp only [K2, d2, Int.cast_id]
  norm_num at a
  rcases r with r | r <;> rw [r] <;> omega

/-- Step H4, (FH4), under the hypotheses of its statement: 0 ≤ K_1 < 2^16 and 0 ≤ K_2 < 2^8
(`step_H4_K2`). -/
theorem step_H4_K1 {v i : ℕ} (hv : v < nV) (hi : i < nT) :
    0 ≤ K1 t y v i ∧ K1 t y v i < 2 ^ 16 := by
  obtain ⟨u, hu, hk⟩ := h.keys .HD1 v i hv hi
  have a := K1_abs h hv hi
  have hu' : (u : ℤ) < 65536 := by exact_mod_cast hu
  have e : K1 t y v i = u := Ledger.lift_eq hk (by
    show |K1 t y v i - (u : ℤ)| < (p : ℤ)
    rw [abs_lt]; have hpB := big_int p; constructor <;> omega)
  omega
theorem step_H4_K2 {v i : ℕ} (hv : v < nV) (hi : i < nT) : 0 ≤ K2 t y v i ∧ K2 t y v i < 2 ^ 8 := by
  obtain ⟨u, hu, hk⟩ := h.keys .HD2 v i hv hi
  have a := K2_abs h hv hi
  have hu' : (u : ℤ) < 256 := by exact_mod_cast hu
  have e : K2 t y v i = u := Ledger.lift_eq hk (by
    show |K2 t y v i - (u : ℤ)| < (p : ℤ)
    rw [abs_lt]; have hpB := big_int p; constructor <;> omega)
  omega

/-- Step H3, (FH5), (FH6), under the hypotheses of its statement: nw fits 16 bits, and nrm =
clamp_2047(nw). -/
theorem step_H3 {j i : ℕ} (hj : j < nD) (hi : i < nT) :
    Fits16 (nw t j i) ∧ nrm t j i = clamp 2047 (nw t j i) := by
  obtain ⟨u, hu, hk⟩ := h.keys .CNF j i hj hi
  have a := nw_abs h hj hi
  have b := nrm_abs h hj hi
  have hu' : (u : ℤ) < 65536 := by exact_mod_cast hu
  have hu0 : (0 : ℤ) ≤ u := Int.natCast_nonneg u
  have hc : -2047 ≤ clamp 2047 ((u : ℤ) - 2 ^ 15) ∧ clamp 2047 ((u : ℤ) - 2 ^ 15) ≤ 2047 := by
    unfold clamp
    omega
  have e : (nw t j i + 2 ^ 15) + 2 ^ 28 * (nrm t j i + 2 ^ 11) =
      (u : ℤ) + 2 ^ 28 * (clamp 2047 ((u : ℤ) - 2 ^ 15) + 2 ^ 11) :=
    Ledger.lift_eq hk (by
      rw [abs_lt]; have hpB := big_int p; constructor <;> omega)
  have e1 : nw t j i + 2 ^ 15 = u := by omega
  have e2 : nrm t j i = clamp 2047 ((u : ℤ) - 2 ^ 15) := by omega
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rw [e2, ← e1]
  congr 1
  ring

/-- Steps H1, H1a (Inst/Model/Common/LedgerSound.lean) at position i, under the hypotheses of its
statement: R is the reciprocal of the program, V + ϵ < 2^78, |x| < 2^39, |x R| < 2^M + 2^38. -/
theorem step_H1 (hn : np.OK) {i : ℕ} (hi : i < nT) :
    Ledger.R (fun n => Dv t n i) = NORM.R np nD (xAt t i) ∧
    NORM.V nD (xAt t i) + np.eps < 2 ^ 78 ∧
    (∀ j < nD, |xAt t i j| < 2 ^ 39) ∧
    ∀ j < nD, |xAt t i j * Ledger.R (fun n => Dv t n i)| < 2 ^ np.M + 2 ^ 38 := by
  have hb : ∀ l < 5, ∀ j < nD, |bl t l j i| ≤ 2 ^ 18 := fun l hl j hj => by
    have := (h.small i hi).2.2.2 (fX l j) (by simp only [fX, nFeat, nD] at *; omega)
    exact le_of_lt this
  have hD : ∀ n < 99, |Dv t n i - 128| ≤ 2 ^ 18 := fun n hn => by
    have := (h.small i hi).2.2.1 n (by simp only [nHr]; omega)
    simp only [Dv, add_sub_cancel_left]
    exact le_of_lt this
  have hk : ∀ n < 99,
      ∃ u : ℤ, 0 ≤ u ∧ u < 256 ∧ Ledger.mu n * Dv t n i ≡ u [ZMOD (p : ℤ)] := fun n hn => by
    obtain ⟨u, hu, hk⟩ := h.keys .ROW n i (by simp only [len]; omega) hi
    refine ⟨u, Int.natCast_nonneg u, by exact_mod_cast hu, ?_⟩
    simpa [key, tableOf, R8] using hk
  obtain ⟨-, -, -, hR, hV, -, -, hx, hxR⟩ :=
    Ledger.ledger_sound (np := np) (d := nD)
      (Cm.TI.Ledger.Adm.mono (N.adm hn) (big_pow p)) hb hD hk (h.idns i hi)
  exact ⟨hR, hV, hx, hxR⟩

/-- Steps H4 and H2, (FH3), (FH12), under the hypotheses of its statement: nw = rhu(x R, K), and 0
≤ rn < 2^(K − 16). -/
theorem step_H2' (hn : np.OK) {j i : ℕ} (hj : j < nD) (hi : i < nT) :
    nw t j i = NORM.yw np nD (xAt t i) j ∧ 0 ≤ rn t j i ∧ rn t j i < 2 ^ (np.K - 16) := by
  obtain ⟨hR, -, -, hxR⟩ := step_H1 h hn hi
  obtain ⟨-, -, -, hM, hK17, hK32, -⟩ := hn
  obtain ⟨u, hu, hk⟩ := h.keys .NF j i hj hi
  obtain ⟨u', hu', hk'⟩ := h.keys .NFH j i hj hi
  have a := (step_H3 h hj hi).1
  have b := rn_abs h hj hi
  have p1 : (2 : ℤ) ^ np.M ≤ 2 ^ 47 := pow_le_pow_right₀ (by norm_num) hM
  have p2 : (2 : ℤ) ^ (32 - np.K) ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) (by omega)
  have p3 : (2 : ℤ) ^ (np.K - 1) ≤ 2 ^ 31 := pow_le_pow_right₀ (by norm_num) (by omega)
  have p4 : (2 : ℤ) ^ np.K ≤ 2 ^ 32 := pow_le_pow_right₀ (by norm_num) hK32
  have hH : Site.high (rn t j i) np.K 32 ≡ (u' : ℤ) [ZMOD (p : ℤ)] := by
    have e : Site.high (rn t j i) np.K 32 = key np t H y .NFH j i := by
      show (2 : ℤ) ^ (32 - np.K) * rn t j i = (((2 ^ (32 - np.K) : ℕ) : ℤ)) * rn t j i
      push_cast
      rfl
    rw [e]
    exact hk'
  unfold NORM.yw
  rw [← hR]
  refine Site.site_high (p := (p : ℤ)) (top := 32) (w := 16) rfl (by omega) hK32
    (Ab := 2 ^ 47 + 2 ^ 38) (Qb := 2 ^ 15) (Rb := 67403904)
    (le_of_lt (lt_of_lt_of_le (hxR j hj) (by linarith))) (abs_le.2 ⟨a.1, le_of_lt a.2⟩)
    (abs_le.2 ⟨le_of_lt b.1, le_of_lt b.2⟩) ?_ ?_
    ⟨u', Int.natCast_nonneg u', by exact_mod_cast hu', hH⟩
    ⟨u, Int.natCast_nonneg u, by exact_mod_cast hu, hk⟩
  · have hpB := big_int p
    nlinarith
  · have hpB := big_int p
    nlinarith

theorem step_H2 (hn : np.OK) {j i : ℕ} (hj : j < nD) (hi : i < nT) :
    nw t j i = NORM.yw np nD (xAt t i) j :=
  (step_H2' h hn hj hi).1

/-- Under the hypotheses of its statement. Lemma S15.8 (a): at every position NORM does not halt,
and nw, nrm are its values. -/
theorem norm_ok (hn : np.OK) {i : ℕ} (hi : i < nT) : NORM.OK np nD (xAt t i) ∧
    ∀ j < nD, nw t j i = NORM.yw np nD (xAt t i) j ∧ nrm t j i = NORM.out np nD (xAt t i) j := by
  refine ⟨⟨(step_H1 h hn hi).2.1, fun j hj => ?_⟩, fun j hj => ⟨step_H2 h hn hj hi, ?_⟩⟩
  · rw [← step_H2 h hn hj hi]
    exact (step_H3 h hj hi).1
  · unfold NORM.out
    rw [← step_H2 h hn hj hi]
    exact (step_H3 h hj hi).2

/-- Step H5, (FH13), under the hypotheses of its statement: |lg| ≤ 5,120 · 2,047 · 2^12. -/
theorem step_H5 (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {i : ℕ} (hi : i < nT) (v : ℕ) :
    |lg t H i v| ≤ 42928701440 := by
  unfold Head.lg
  calc
    |∑ j ∈ range nD,
      nrm t j i * H j v| ≤ ∑ j ∈ range nD, |nrm t j i * H j v| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range nD, (2047 * 2 ^ 12 : ℤ) := by
        refine sum_le_sum fun j hj => ?_
        have h1 : |nrm t j i| ≤ 2047 := by
          rw [(step_H3 h (mem_range.1 hj) hi).2, abs_le]
          unfold clamp
          omega
        rw [abs_mul]
        exact mul_le_mul h1 (hH j v) (abs_nonneg _) (by norm_num)
    _ = 42928701440 := by simp [nD]

/-- The margin step, at every covered position, under the hypotheses of its statement: the margin
of every token is at least 0. -/
theorem step_H6 (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {i : ℕ} (hi : i < nT) (hr : y.r ≤ i)
    (he : i < y.e) {v : ℕ} (hv : v < nV) :
    0 ≤ lg t H i (y.win i) - lg t H i v - if v < y.win i then 1 else 0 := by
  obtain ⟨u, hu, hk⟩ := h.keys .HD0 v i hv hi
  have hu' : (u : ℤ) < 65536 := by exact_mod_cast hu
  have hu0 : (0 : ℤ) ≤ u := Int.natCast_nonneg u
  have k1 := step_H4_K1 h hv hi
  have k2 := step_H4_K2 h hv hi
  have l1 := abs_le.1 (step_H5 h hH hi (y.win i))
  have l2 := abs_le.1 (step_H5 h hH hi v)
  have hmg : mg t H y v i =
    lg t H i (y.win i) - lg t H i v - if v < y.win i then 1 else 0 := by simp [mg, Req.rho, hr, he]
  have hk' : mg t H y v i - 2 ^ 8 * K1 t y v i - K2 t y v i ≡ 2 ^ 23 * (u : ℤ) [ZMOD (p : ℤ)] := hk
  set A := mg t H y v i - 2 ^ 8 * K1 t y v i - K2 t y v i with hA
  have h1 : A ≡ 2 ^ 23 * (u : ℤ) [ZMOD (p : ℤ)] := hk'
  have hb : (if v < y.win i then (1 : ℤ) else 0) = 0 ∨
      (if v < y.win i then (1 : ℤ) else 0) = 1 := by
    split_ifs <;> simp
  have e : A = 2 ^ 23 * (u : ℤ) := Ledger.lift_eq h1 (by
    rw [abs_lt, hA, hmg]; have hpB := big_int p
    rcases hb with hb | hb <;> rw [hb] <;> constructor <;> omega)
  rw [← hmg]
  omega

/-- No wrap-around in the plain head, for an arbitrary stream (the borrowed cells), under the
hypotheses of its statement: the final normalisation does not halt at any position, nw and nrm are
its values, |x| < 2^39, and at every covered position i the logit of the checked token is at least
that of every token and greater than that of every smaller token.
(The clause on smaller tokens speaks of v < V only; with `y.OK`, every checked token below V, the
two clauses at a covered position are "the gap is 0": `head_stream_gap`.) -/
theorem noWrap (hn : np.OK) (hH : ∀ j v, |H j v| ≤ 2 ^ 12) :
    (∀ i < nT,
      NORM.OK np nD (xAt t i) ∧
      (∀ j < nD, nw t j i = NORM.yw np nD (xAt t i) j ∧ nrm t j i = NORM.out np nD (xAt t i) j) ∧
      ∀ j < nD, |xAt t i j| < 2 ^ 39) ∧
    ∀ i < nT, y.r ≤ i → i < y.e →
      (∀ v < nV, lg t H i v ≤ lg t H i (y.win i)) ∧
      ∀ v < y.win i, v < nV → lg t H i v < lg t H i (y.win i) := by
  refine ⟨fun i hi => ⟨(norm_ok h hn hi).1, (norm_ok h hn hi).2, (step_H1 h hn hi).2.2.1⟩,
    fun i hi hr he => ⟨fun v hv => ?_, fun v hvy hv => ?_⟩⟩
  · have := step_H6 h hH hi hr he hv
    split_ifs at this <;> omega
  · have := step_H6 h hH hi hr he hv
    rw [if_pos hvy] at this
    omega

end Steps

section Map
variable {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (np : NormPar) (t : Cells K)
  (H : ℕ → ℕ → K) (y : Req)

/-- A ring homomorphism commutes with the keys. -/
theorem map_key (s : Fam) (x i : ℕ) :
    f (key np t H y s x i) = key np (t.map f) (fun j v => f (H j v)) y s x i := by
  cases s
  · simp only [key, map_sub, map_add, map_mul, map_pow, map_ofNat, map_xv, map_nw,
      map_rn, Ledger.map_R, map_Dv]
  · simp only [key, map_mul, map_natCast, map_rn]
  · simp only [key, map_sub, map_mul, map_pow, map_ofNat, map_mg', map_K1, map_K2]
  · exact map_K1 f t y x i
  · simp only [key, map_mul, map_intCast, map_Dv]
  · exact map_K2 f t y x i
  · simp only [key, map_add, map_mul, map_pow, map_ofNat, map_nw, map_nrm]

end Map

variable {p : ℕ} {np : NormPar}

theorem rfz_of_rf {H : Mat} {y : Req} {t : Cells ℤ}
    (h : RF (F := ZMod p) np (fun j v => (H j v : ZMod p)) y t) : RFz p np H y t where
  small := h.small
  keys := fun s x i hx hi => by
    obtain ⟨u, hu, e⟩ := h.keys s x i hx hi
    refine ⟨u, hu, ?_⟩
    have e1 := map_key (Int.castRingHom (ZMod p)) np t H y s x i
    refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
    exact e1.trans e
  idns := fun i hi k hk => by
    have e := h.idns i hi k hk
    have e1 := map_idn' (Int.castRingHom (ZMod p)) np t i k
    refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
    rw [Int.cast_zero]
    exact e1.trans e

theorem rf_of_rfz {H : Mat} {y : Req} {t : Cells ℤ} (h : RFz p np H y t) :
    RF (F := ZMod p) np (fun j v => (H j v : ZMod p)) y t where
  small := h.small
  keys := fun s x i hx hi => by
    obtain ⟨u, hu, e⟩ := h.keys s x i hx hi
    refine ⟨u, hu, ?_⟩
    exact (map_key (Int.castRingHom (ZMod p)) np t H y s x i).symm.trans
      ((ZMod.intCast_eq_intCast_iff _ _ _).2 e)
  idns := fun i hi k hk => by
    have e := h.idns i hi k hk
    have e2 := (ZMod.intCast_eq_intCast_iff _ _ _).2 e
    rw [Int.cast_zero] at e2
    exact (map_idn' (Int.castRingHom (ZMod p)) np t i k).symm.trans e2

/-- No wrap-around in the plain head, for a stream X that the borrowed cells hold, under the
hypotheses of its statement: the final normalisation of X does not halt at any position, and at
every covered position the checked token is the least index of a greatest logit (among tokens v <
V: see the bracket at `noWrap`). The logits are written as Inst/Model/Program.lean writes them
(`dot`, `NORM.out`), so that the statement unfolds to the last clause of `RunsK` and to `lgK`. -/
theorem head_stream [Big p] (hn : np.OK) {H : Mat} (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {y : Req}
    {t : Cells ℤ} {X : ℕ → Vec} (hx : ∀ i < nT, ∀ j < nD, xv t j i = X i j) (h : RFz p np H y t) :
    (∀ pos < nT, NORM.OK np nD (X pos)) ∧
    ∀ i < nT, y.r ≤ i → i < y.e →
      (∀ v < nV, dot nD (NORM.out np nD (X i)) (fun j => H j v) ≤
        dot nD (NORM.out np nD (X i)) fun j => H j (y.win i)) ∧
      ∀ v < y.win i, v < nV →
        dot nD (NORM.out np nD (X i)) (fun j => H j v) <
          dot nD (NORM.out np nD (X i)) fun j => H j (y.win i) := by
  obtain ⟨h1, h2⟩ := noWrap h hn hH
  have hlg : ∀ i < nT, ∀ v, dot nD (NORM.out np nD (X i)) (fun j => H j v) = lg t H i v := by
    intro i hi v
    unfold dot Head.lg
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < nD := mem_range.1 hj
    rw [((h1 i hi).2.1 j hj').2,
      NORM_out_congr np nD (x := X i) (x' := xAt t i) (fun j hj => (hx i hi j hj).symm) hj']
  refine ⟨fun pos hpos => ?_, fun i hi hr he => ⟨fun v hv => ?_, fun v hvy hv => ?_⟩⟩
  · exact (NORM_OK_congr np nD fun j hj => (hx pos hpos j hj).symm).2 (h1 pos hpos).1
  · rw [hlg i hi, hlg i hi]
    exact (h2 i hi hr he).1 v hv
  · rw [hlg i hi, hlg i hi]
    exact (h2 i hi hr he).2 v hvy hv

/-- The same in the words of Inst/Model/ProgramR.lean, with `hy : y.OK` besides: the logit gap of
the checked token is 0 at every covered position. -/
theorem head_stream_gap [Big p] (hn : np.OK) {H : Mat} (hH : ∀ j v, |H j v| ≤ 2 ^ 12)
    {y : Req} (hy : y.OK) {t : Cells ℤ} {X : ℕ → Vec}
    (hx : ∀ i < nT, ∀ j < nD, xv t j i = X i j) (h : RFz p np H y t) :
    ∀ i < nT, y.r ≤ i → i < y.e →
      gapOf nV (fun v => dot nD (NORM.out np nD (X i)) fun j => H j v) (y.win i) =
        0 := fun i hi hr he =>
  (gapOf_eq_zero_iff nV _ (hy i)).2
    ⟨((head_stream hn hH hx h).2 i hi hr he).1,
      fun v hv => ((head_stream hn hH hx h).2 i hi hr he).2 v hv (lt_trans hv (hy i))⟩

end Cm.Plain.TP

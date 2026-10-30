-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/TableKeys.lean: what a key (looked-up value) in R8, R16, FC, FL or FS implies, and
the honest keys.

Everything is about integers at one position, with bounds as hypotheses (`inLut_iff_cast` also
speaks of a ring of characteristic p); no cells, no layout. The tables: Inst/Model/Tables.lean; the
families of keys (G0, UT, ..): `Fam`, Inst/Model/FF/Index.lean. Each row holds under the hypotheses
of its statement.
  `InLut p L key`      the key is congruent modulo p to an entry of the table L; `InLutZ L key`: it
                       is an entry
  `g0_key`, `ut_key`, `lt_key`, `sel_key`, `l3_key`      Step L1: (FL4) −128 ≤ g0 ≤ 127; (FL6) up
                       fits 16 bits; (FL5) −2^14 ≤ lr < 2^14; (FL2) sel is 0 or 1; (FL3) 0 ≤ l3 ≤ 7
  `fc_key`             Step L2, FC: (FL8) yw fits 16 bits and (FL9) y = clamp_2047(yw)
  `fl_key`             Step L2, FL: (FL8) gk = 256 gc + g0 fits 16 bits and (FL10) sl = SILU[gk +
                       2^15], |sl| ≤ 4,095
  `cg_key`             Step L3, FS: (FL11) −2^14 ≤ gh < 2^14 and gc = clamp_127(gh)
  `clr_key`            Step L10a, FC: (FL22) ly fits 16 bits and lr = 8 clamp_2047(ly) + l3
  `mr_key`             Step L10d, FS: (FL26) sc = SIGM[mr + 2^15], 0 ≤ sc ≤ 2^16
  `fc_hon`, ..         under range hypotheses the honest keys are entries of their tables, over the
                       integers
The modulus p and all bounds are parameters. B1, B2, B3 bound values of one, two and three cells.
Labels such as (FL4) and "Step L1" link one docstring to another.

Notation: `L`: a `Lut`: "A table: its number of rows, the entry τ(ι) of each row, and its padding
value." (Inst/Model/Tables.lean); `R8`, `R16`, `FC`, `FL tb`, `FS tb`: such tables, defined there;
`tb`: `Tables`, "The five table functions that the program reads." (Inst/Model/Program.lean), SILU
and SIGM among them; `g0`, `gh`, `gc`, `sl`, `up`, `yw`, `y`, `ly`, `l3`, `lr`, `mr`, `sc`, `sel`:
integers; all but y and sel have the names of values of the integer program (`UNIT`, `NORM`, `FF`,
Inst/Model/Program.lean); gk: 256 gc + g0; `hp`, `guard`: hypotheses: an inequality between the
bounds and p, and one between a bound and the radix (in `fc_key`, `fl_key`, `clr_key`: the R of
`split_radix`).
-/
import Inst.Model.Common.Site
import Inst.Model.Tables

set_option autoImplicit false

namespace Inst.Model.TableKeys

open Inst.Model.Ledger (lift_eq)

/-! ## 0. Keys in tables -/

/-- the key is congruent modulo p to an entry of the table -/
def InLut (p : ℤ) (L : Lut) (key : ℤ) : Prop := ∃ ι : ℕ, ι < L.rows ∧ key ≡ L.row ι [ZMOD p]

/-- the key is an entry of the table -/
def InLutZ (L : Lut) (key : ℤ) : Prop := ∃ ι : ℕ, ι < L.rows ∧ key = L.row ι

theorem InLutZ.inLut {L : Lut} {key : ℤ} (h : InLutZ L key) (p : ℤ) : InLut p L key := by
  obtain ⟨ι, h1, h2⟩ := h
  exact ⟨ι, h1, h2 ▸ Int.ModEq.refl _⟩

/-- In a ring of characteristic p: `InLut p L key` holds if and only if the image of the key is the
image of an entry. -/
theorem inLut_iff_cast (K : Type) [CommRing K] (p : ℕ) [CharP K p] (L : Lut) (key : ℤ) :
    InLut (p : ℤ) L key ↔ ∃ ι : ℕ, ι < L.rows ∧ ((key : ℤ) : K) = ((L.row ι : ℤ) : K) := by
  unfold InLut
  simp only [CharP.intCast_eq_intCast K p]

theorem clamp_bounds {c : ℤ} (hc : 0 ≤ c) (a : ℤ) : -c ≤ clamp c a ∧ clamp c a ≤ c := by
  unfold clamp
  omega

/-- One radix: if lo + u = t + g, where R divides u and g, and |lo − t| < R, then lo = t and u =
g. -/
theorem split_radix {R lo u t g : ℤ} (hu : R ∣ u) (hg : R ∣ g)
    (hlt : |lo - t| < R) (h : lo + u = t + g) : lo = t ∧ u = g := by
  have hd : R ∣ lo - t := by
    have : lo - t = g - u := by linarith
    rw [this]
    exact dvd_sub hg hu
  have h0 := Int.eq_zero_of_abs_lt_dvd hd hlt
  constructor <;> omega

/-! ## 1. The range tables (Step L1) -/

theorem r8_key {p key B : ℤ} (hB : |key| ≤ B) (hp : B + 2 ^ 8 ≤ p) (h : InLut p R8 key) :
    0 ≤ key ∧ key < 2 ^ 8 := by
  obtain ⟨ι, h1, h2⟩ := h
  have h1' : ι < 2 ^ 8 := h1
  exact Site.range_of_key hB hp ⟨(ι : ℤ), by positivity, by exact_mod_cast h1', h2⟩

theorem r16_key {p key B : ℤ} (hB : |key| ≤ B) (hp : B + 2 ^ 16 ≤ p) (h : InLut p R16 key) :
    0 ≤ key ∧ key < 2 ^ 16 := by
  obtain ⟨ι, h1, h2⟩ := h
  have h1' : ι < 2 ^ 16 := h1
  exact Site.range_of_key hB hp ⟨(ι : ℤ), by positivity, by exact_mod_cast h1', h2⟩

/-- A key in R8 (for R16: `InLut.r16`), in the form of the hypotheses of
Inst/Model/Common/Site.lean. -/
theorem InLut.r8 {p key : ℤ} (h : InLut p R8 key) :
    ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ 8 ∧ key ≡ t [ZMOD p] := by
  obtain ⟨ι, h1, h2⟩ := h
  have h1' : ι < 2 ^ 8 := h1
  exact ⟨(ι : ℤ), by positivity, by exact_mod_cast h1', h2⟩

theorem InLut.r16 {p key : ℤ} (h : InLut p R16 key) :
    ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ 16 ∧ key ≡ t [ZMOD p] := by
  obtain ⟨ι, h1, h2⟩ := h
  have h1' : ι < 2 ^ 16 := h1
  exact ⟨(ι : ℤ), by positivity, by exact_mod_cast h1', h2⟩

theorem inLutZ_r8 {key : ℤ} (h0 : 0 ≤ key) (h1 : key < 2 ^ 8) : InLutZ R8 key :=
  ⟨key.toNat, by show key.toNat < 2 ^ 8; omega, by show key = (key.toNat : ℤ); omega⟩

theorem inLutZ_r16 {key : ℤ} (h0 : 0 ≤ key) (h1 : key < 2 ^ 16) : InLutZ R16 key :=
  ⟨key.toNat, by show key.toNat < 2 ^ 16; omega, by show key = (key.toNat : ℤ); omega⟩

/-- G0: g0 + 128 in R8 modulo p gives (FL4), −128 ≤ g0 ≤ 127, under the bounds below. -/
theorem g0_key {p g0 B1 : ℤ} (hb : |g0| ≤ B1)
    (hp : B1 + 128 + 2 ^ 8 ≤ p) (h : InLut p R8 (g0 + 128)) : -128 ≤ g0 ∧ g0 ≤ 127 := by
  have hb' := abs_le.mp hb
  have := r8_key (B := B1 + 128) (by rw [abs_le]; constructor <;> linarith) hp h
  omega

/-- UT: up + 2^15 in R16 modulo p gives (FL6), up fits 16 bits, the range condition of (U5)
(`UNIT.OK`, Inst/Model/Program.lean), under the bounds below. -/
theorem ut_key {p up B2 : ℤ} (hb : |up| ≤ B2)
    (hp : B2 + 2 ^ 15 + 2 ^ 16 ≤ p) (h : InLut p R16 (up + 2 ^ 15)) : Fits16 up := by
  have hb' := abs_le.mp hb
  have := r16_key (B := B2 + 2 ^ 15) (by rw [abs_le]; constructor <;> linarith) hp h
  unfold Fits16
  omega

/-- LT: 2 (lr + 2^14) in R16 modulo p gives (FL5), −2^14 ≤ lr < 2^14, under the bounds below. -/
theorem lt_key {p lr B2 : ℤ} (hb : |lr| ≤ B2)
    (hp : 2 * (B2 + 2 ^ 14) + 2 ^ 16 ≤ p) (h : InLut p R16 (2 * (lr + 2 ^ 14))) :
    -2 ^ 14 ≤ lr ∧ lr < 2 ^ 14 := by
  have hb' := abs_le.mp hb
  have := r16_key (B := 2 * (B2 + 2 ^ 14)) (by rw [abs_le]; constructor <;> linarith) hp h
  omega

/-- SEL: 128 sel in R8 modulo p gives (FL2), sel is 0 or 1, under the bounds below. -/
theorem sel_key {p sel B1 : ℤ} (hb : |sel| ≤ B1)
    (hp : 128 * B1 + 2 ^ 8 ≤ p) (h : InLut p R8 (128 * sel)) : sel = 0 ∨ sel = 1 := by
  have hb' := abs_le.mp hb
  have := r8_key (B := 128 * B1) (by rw [abs_le]; constructor <;> linarith) hp h
  omega

/-- L3: 32 l3 in R8 modulo p gives (FL3), 0 ≤ l3 ≤ 7, under the bounds below. -/
theorem l3_key {p l3 B1 : ℤ} (hb : |l3| ≤ B1)
    (hp : 32 * B1 + 2 ^ 8 ≤ p) (h : InLut p R8 (32 * l3)) : 0 ≤ l3 ∧ l3 ≤ 7 := by
  have hb' := abs_le.mp hb
  have := r8_key (B := 32 * B1) (by rw [abs_le]; constructor <;> linarith) hp h
  omega

/-! ## 2. The clamp table FC and the activation table FL (Step L2) -/

/-- Table FC (CN1, CN2, CQK, CV): under the hypotheses below, (FL8) yw fits 16 bits and (FL9) y =
clamp_2047(yw). -/
theorem fc_key {p yw y B2 : ℤ} (hyw : |yw| ≤ B2) (hy : |y| ≤ B2)
    (hp : (B2 + 2 ^ 15) + 2 ^ 28 * (B2 + 2 ^ 11) + 2 ^ 41 ≤ p)
    (guard : B2 + 2 ^ 15 + 2 ^ 16 < 2 ^ 28)
    (h : InLut p FC ((yw + 2 ^ 15) + 2 ^ 28 * (y + 2 ^ 11))) :
    Fits16 yw ∧ y = clamp 2047 yw := by
  obtain ⟨ι, h1, ht⟩ := h
  have h1' : (ι : ℤ) < 2 ^ 16 := by exact_mod_cast (show ι < 2 ^ 16 from h1)
  have h0' : (0 : ℤ) ≤ ι := by positivity
  have ht' : (yw + 2 ^ 15) + 2 ^ 28 * (y + 2 ^ 11) ≡
      (ι : ℤ) + 2 ^ 28 * (clamp 2047 ((ι : ℤ) - 2 ^ 15) + 2 ^ 11) [ZMOD p] := ht
  have hc := clamp_bounds (c := 2047) (by norm_num) ((ι : ℤ) - 2 ^ 15)
  have hyw' := abs_le.mp hyw
  have hy' := abs_le.mp hy
  have e := lift_eq ht' (by rw [abs_lt]; constructor <;> linarith)
  obtain ⟨e1, e2⟩ := split_radix (R := 2 ^ 28) (dvd_mul_right _ _) (dvd_mul_right _ _)
    (by rw [abs_lt]; constructor <;> linarith) e
  have e3 : (ι : ℤ) - 2 ^ 15 = yw := by linarith
  rw [e3] at e2
  exact ⟨by unfold Fits16; omega, by linarith⟩

theorem fc_hon {yw : ℤ} (h : Fits16 yw) :
    InLutZ FC ((yw + 2 ^ 15) + 2 ^ 28 * (clamp 2047 yw + 2 ^ 11)) := by
  unfold Fits16 at h
  refine ⟨(yw + 2 ^ 15).toNat, by show (yw + 2 ^ 15).toNat < 2 ^ 16; omega, ?_⟩
  show _ = (((yw + 2 ^ 15).toNat : ℕ) : ℤ) +
      2 ^ 28 * (clamp 2047 ((((yw + 2 ^ 15).toNat : ℕ) : ℤ) - 2 ^ 15) + 2 ^ 11)
  have e : (((yw + 2 ^ 15).toNat : ℕ) : ℤ) = yw + 2 ^ 15 := Int.toNat_of_nonneg (by omega)
  rw [e, add_sub_cancel_right]

/-- Table FL (F): under the hypotheses below, (FL8) gk = 256 gc + g0 fits 16 bits and (FL10) sl =
SILU[gk + 2^15], |sl| ≤ 4,095. -/
theorem fl_key {p : ℤ} {tb : Tables} {g0 gc sl B2 : ℤ} (hgk : |256 * gc + g0| ≤ B2)
    (hsl : |sl| ≤ B2) (hT : ∀ ι < 2 ^ 16, -4095 ≤ tb.SILU (ι : ℕ) ∧ tb.SILU (ι : ℕ) ≤ 4095)
    (hp : (B2 + 2 ^ 15) + 2 ^ 28 * (B2 + 2 ^ 12) + 2 ^ 42 ≤ p)
    (guard : B2 + 2 ^ 15 + 2 ^ 16 < 2 ^ 28)
    (h : InLut p (FL tb) ((g0 + 256 * gc + 2 ^ 15) + 2 ^ 28 * (sl + 2 ^ 12))) :
    Fits16 (256 * gc + g0) ∧ sl = tb.SILU (256 * gc + g0 + 2 ^ 15) ∧ |sl| ≤ 4095 := by
  obtain ⟨ι, h1, ht⟩ := h
  have h1n : ι < 2 ^ 16 := h1
  have h1' : (ι : ℤ) < 2 ^ 16 := by exact_mod_cast h1n
  have h0' : (0 : ℤ) ≤ ι := by positivity
  have ht' : (g0 + 256 * gc + 2 ^ 15) + 2 ^ 28 * (sl + 2 ^ 12) ≡
      (ι : ℤ) + 2 ^ 28 * (tb.SILU (ι : ℤ) + 2 ^ 12) [ZMOD p] := ht
  have hc := hT ι h1n
  have hgk' := abs_le.mp hgk
  have hsl' := abs_le.mp hsl
  have e := lift_eq ht' (by rw [abs_lt]; constructor <;> linarith)
  obtain ⟨e1, e2⟩ := split_radix (R := 2 ^ 28) (dvd_mul_right _ _) (dvd_mul_right _ _)
    (by rw [abs_lt]; constructor <;> linarith) e
  have e3 : (ι : ℤ) = 256 * gc + g0 + 2 ^ 15 := by linarith
  have e4 : sl = tb.SILU (ι : ℤ) := by linarith
  refine ⟨by unfold Fits16; omega, by rw [← e3]; exact e4, ?_⟩
  rw [e4, abs_le]
  exact hc

theorem fl_hon (tb : Tables) {g0 gc : ℤ} (h : Fits16 (256 * gc + g0)) :
    InLutZ (FL tb)
      ((g0 + 256 * gc + 2 ^ 15) + 2 ^ 28 * (tb.SILU (256 * gc + g0 + 2 ^ 15) + 2 ^ 12)) := by
  unfold Fits16 at h
  refine ⟨(256 * gc + g0 + 2 ^ 15).toNat,
    by show (256 * gc + g0 + 2 ^ 15).toNat < 2 ^ 16; omega,
    ?_⟩
  show _ = (((256 * gc + g0 + 2 ^ 15).toNat : ℕ) : ℤ) +
      2 ^ 28 * (tb.SILU (((256 * gc + g0 + 2 ^ 15).toNat : ℕ) : ℤ) + 2 ^ 12)
  have e : (((256 * gc + g0 + 2 ^ 15).toNat : ℕ) : ℤ) = 256 * gc + g0 + 2 ^ 15 :=
    Int.toNat_of_nonneg (by omega)
  rw [e]
  ring

/-! ## 3. The table FS: clamp of the gate (Step L3) and sigmoid (Step L10d) -/

theorem fs_row_lo (tb : Tables) {ι : ℕ} (h : ι < 2 ^ 15) :
    (FS tb).row ι = (ι : ℤ) + 2 ^ 17 * tb.SIGM ((ι : ℤ) + 2 ^ 14) := by
  show (if ι < 2 ^ 15 then _ else _) = _
  rw [if_pos h]

theorem fs_row_hi (tb : Tables) {ι : ℕ} (h : ¬ ι < 2 ^ 15) :
    (FS tb).row ι = (ι : ℤ) + 2 ^ 28 * (clamp 127 ((ι : ℤ) - 49152) + 128) + 2 ^ 40 := by
  show (if ι < 2 ^ 15 then _ else _) = _
  rw [if_neg h]

/-- Table FS, the family CG: under the hypotheses below, (FL11) −2^14 ≤ gh < 2^14 and gc =
clamp_127(gh). Among them: g0 is a balanced byte (G0) and gk = 256 gc + g0 fits 16 bits (F, for the
same gc); so the entry is not a row of the sigmoid. -/
theorem cg_key {p : ℤ} {tb : Tables} {g0 gc gh B1 B2 : ℤ} (hgh : |gh| ≤ B2) (hgc : |gc| ≤ B1)
    (hS : ∀ ι < 2 ^ 15, 0 ≤ tb.SIGM ((ι : ℕ) + 2 ^ 14) ∧ tb.SIGM ((ι : ℕ) + 2 ^ 14) ≤ 2 ^ 16)
    (hp : (B2 + 49152) + 2 ^ 28 * (B1 + 128) + 2 ^ 40 + 2 ^ 41 ≤ p)
    (guard : B2 + 49152 + 2 ^ 16 < 2 ^ 28) (hg0 : -128 ≤ g0 ∧ g0 ≤ 127)
    (hgk : Fits16 (256 * gc + g0))
    (h : InLut p (FS tb) ((gh + 49152) + 2 ^ 28 * (gc + 128) + 2 ^ 40)) :
    (-2 ^ 14 ≤ gh ∧ gh < 2 ^ 14) ∧ gc = clamp 127 gh := by
  obtain ⟨ι, h1, ht⟩ := h
  have h1n : ι < 2 ^ 16 := h1
  have h1' : (ι : ℤ) < 2 ^ 16 := by exact_mod_cast h1n
  have h0' : (0 : ℤ) ≤ ι := by positivity
  have hgh' := abs_le.mp hgh
  have hgc' := abs_le.mp hgc
  unfold Fits16 at hgk
  by_cases hrow : ι < 2 ^ 15
  · -- a row of the sigmoid: impossible
    exfalso
    have hSι := hS ι hrow
    rw [fs_row_lo tb hrow] at ht
    have e := lift_eq ht (by rw [abs_lt]; constructor <;> linarith)
    omega
  · -- a row of the clamp
    have hc := clamp_bounds (c := 127) (by norm_num) ((ι : ℤ) - 49152)
    rw [fs_row_hi tb hrow] at ht
    have e := lift_eq ht (by rw [abs_lt]; constructor <;> linarith)
    have hι : (2 : ℤ) ^ 15 ≤ ι := by exact_mod_cast Nat.le_of_not_lt hrow
    have e1 : gh + 49152 = ι := by omega
    have e2 : gc = clamp 127 ((ι : ℤ) - 49152) := by omega
    have e3 : (ι : ℤ) - 49152 = gh := by omega
    rw [e3] at e2
    exact ⟨by omega, e2⟩

theorem cg_hon (tb : Tables) {gh : ℤ} (h0 : -2 ^ 14 ≤ gh) (h1 : gh < 2 ^ 14) :
    InLutZ (FS tb) ((gh + 49152) + 2 ^ 28 * (clamp 127 gh + 128) + 2 ^ 40) := by
  have hn : ¬ (gh + 49152).toNat < 2 ^ 15 := by omega
  refine ⟨(gh + 49152).toNat, by show (gh + 49152).toNat < 2 ^ 16; omega, ?_⟩
  rw [fs_row_hi tb hn]
  have e : (((gh + 49152).toNat : ℕ) : ℤ) = gh + 49152 := Int.toNat_of_nonneg (by omega)
  rw [e, add_sub_cancel_right]

/-- Table FS, the family MR: under the hypotheses below, (FL26) sc = SIGM[mr + 2^15], 0 ≤ sc ≤ 2^16.
The hypothesis 0 ≤ mr + 2^14 < 2^15 is (FL24). -/
theorem mr_key {p : ℤ} {tb : Tables} {mr sc B3 : ℤ} (hmr : -2 ^ 14 ≤ mr ∧ mr < 2 ^ 14)
    (hsc : |sc| ≤ B3)
    (hS : ∀ ι < 2 ^ 15, 0 ≤ tb.SIGM ((ι : ℕ) + 2 ^ 14) ∧ tb.SIGM ((ι : ℕ) + 2 ^ 14) ≤ 2 ^ 16)
    (hp : 2 ^ 15 + 2 ^ 17 * B3 + 2 ^ 41 ≤ p) (h : InLut p (FS tb) ((mr + 2 ^ 14) + 2 ^ 17 * sc)) :
    sc = tb.SIGM (mr + 2 ^ 15) ∧ 0 ≤ sc ∧ sc ≤ 2 ^ 16 := by
  obtain ⟨ι, h1, ht⟩ := h
  have h1n : ι < 2 ^ 16 := h1
  have h1' : (ι : ℤ) < 2 ^ 16 := by exact_mod_cast h1n
  have h0' : (0 : ℤ) ≤ ι := by positivity
  have hsc' := abs_le.mp hsc
  by_cases hrow : ι < 2 ^ 15
  · have hSι := hS ι hrow
    have hι : (ι : ℤ) < 2 ^ 15 := by exact_mod_cast hrow
    rw [fs_row_lo tb hrow] at ht
    have e := lift_eq ht (by rw [abs_lt]; constructor <;> linarith)
    obtain ⟨e1, e2⟩ := split_radix (R := 2 ^ 17) (dvd_mul_right _ _) (dvd_mul_right _ _)
      (by rw [abs_lt]; constructor <;> linarith) e
    have e3 : (ι : ℤ) + 2 ^ 14 = mr + 2 ^ 15 := by linarith
    have e4 : sc = tb.SIGM ((ι : ℤ) + 2 ^ 14) := by linarith
    refine ⟨by rw [← e3]; exact e4, ?_, ?_⟩ <;> rw [e4]
    · exact hSι.1
    · exact hSι.2
  · -- a row of the clamp: impossible
    exfalso
    have hc := clamp_bounds (c := 127) (by norm_num) ((ι : ℤ) - 49152)
    have hι : (2 : ℤ) ^ 15 ≤ ι := by exact_mod_cast Nat.le_of_not_lt hrow
    rw [fs_row_hi tb hrow] at ht
    have e := lift_eq ht (by rw [abs_lt]; constructor <;> linarith)
    have e' : (mr + 2 ^ 14) + 2 ^ 17 * sc =
        (ι : ℤ) + 2 ^ 17 * (2 ^ 11 * (clamp 127 ((ι : ℤ) - 49152) + 128) + 2 ^ 23) := by
      rw [e]
      ring
    obtain ⟨e1, _⟩ := split_radix (R := 2 ^ 17) (dvd_mul_right _ _) (dvd_mul_right _ _)
      (by rw [abs_lt]; constructor <;> linarith) e'
    omega

theorem mr_hon (tb : Tables) {mr : ℤ} (h0 : -2 ^ 14 ≤ mr) (h1 : mr < 2 ^ 14) :
    InLutZ (FS tb) ((mr + 2 ^ 14) + 2 ^ 17 * tb.SIGM (mr + 2 ^ 15)) := by
  have hn : (mr + 2 ^ 14).toNat < 2 ^ 15 := by omega
  refine ⟨(mr + 2 ^ 14).toNat, by show (mr + 2 ^ 14).toNat < 2 ^ 16; omega, ?_⟩
  rw [fs_row_lo tb hn]
  have e : (((mr + 2 ^ 14).toNat : ℕ) : ℤ) = mr + 2 ^ 14 := Int.toNat_of_nonneg (by omega)
  rw [e]
  have e2 : mr + 2 ^ 14 + 2 ^ 14 = mr + 2 ^ 15 := by ring
  rw [e2]

/-! ## 4. The clamp of a router logit (Step L10a) -/

/-- Table FC, the family CLR: under the hypotheses below, (FL22) ly fits 16 bits and lr = 8
clamp_2047(ly) + l3. The bound Bl on ly is the one that the rounding gives ((FL21)); the bound that
condition (1) (every cell is below 2^18 in absolute value) alone gives would be above the radix
2^25. -/
theorem clr_key {p ly lr l3 Bl : ℤ} (hly : |ly| ≤ Bl) (hlr : -2 ^ 14 ≤ lr ∧ lr < 2 ^ 14)
    (hl3 : 0 ≤ l3 ∧ l3 ≤ 7) (hp : Bl + 2 ^ 15 + 2 ^ 42 ≤ p) (guard : Bl + 2 ^ 15 + 2 ^ 16 < 2 ^ 25)
    (h : InLut p FC ((ly + 2 ^ 15) + 2 ^ 25 * (lr - l3) + 2 ^ 39)) :
    Fits16 ly ∧ lr = 8 * clamp 2047 ly + l3 := by
  obtain ⟨ι, h1, ht⟩ := h
  have h1' : (ι : ℤ) < 2 ^ 16 := by exact_mod_cast (show ι < 2 ^ 16 from h1)
  have h0' : (0 : ℤ) ≤ ι := by positivity
  have ht' : (ly + 2 ^ 15) + 2 ^ 25 * (lr - l3) + 2 ^ 39 ≡
      (ι : ℤ) + 2 ^ 28 * (clamp 2047 ((ι : ℤ) - 2 ^ 15) + 2 ^ 11) [ZMOD p] := ht
  have hc := clamp_bounds (c := 2047) (by norm_num) ((ι : ℤ) - 2 ^ 15)
  have hly' := abs_le.mp hly
  have e := lift_eq ht' (by rw [abs_lt]; constructor <;> linarith)
  have e' : (ly + 2 ^ 15) + 2 ^ 25 * (lr - l3) =
      (ι : ℤ) + 2 ^ 25 * (8 * clamp 2047 ((ι : ℤ) - 2 ^ 15)) := by linarith
  obtain ⟨e1, e2⟩ := split_radix (R := 2 ^ 25) (dvd_mul_right _ _) (dvd_mul_right _ _)
    (by rw [abs_lt]; constructor <;> linarith) e'
  have e3 : (ι : ℤ) - 2 ^ 15 = ly := by linarith
  rw [e3] at e2
  exact ⟨by unfold Fits16; omega, by linarith⟩

theorem clr_hon {ly l3 : ℤ} (h : Fits16 ly) :
    InLutZ FC ((ly + 2 ^ 15) + 2 ^ 25 * ((8 * clamp 2047 ly + l3) - l3) + 2 ^ 39) := by
  obtain ⟨ι, h1, h2⟩ := fc_hon h
  exact ⟨ι, h1, by rw [← h2]; ring⟩

end Inst.Model.TableKeys

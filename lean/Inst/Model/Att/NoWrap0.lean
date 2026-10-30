-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/NoWrap0.lean: the field relation of an attention segment as congruences between
  integers, and tools.

  * `IntRel`: conditions (1) to (3) of the field relation (`RFraw`, Inst/Model/Att/Trace.lean) for
    the segment, family by family, read over ℤ: a looked-up value (key) is congruent modulo p to a
    row of its table, an identity is congruent to 0.
  * `intRel_of_rfraw`: from `RFraw` over ZMod p to `IntRel` at p.
  * `IntRel.mxV_abs`, ..: the bounds of the values that follow from condition (1) alone.
  * `twoFam_fst`, `twoFam_snd`, `Dim.idxW`, `Dim.idxX`, `Dim.idx4`: the index of the looked-up value
    of a family in the vector of its call.
  * `InB`, `Half1`: the interface between the two halves of the proof of `noWrapK`
    (Inst/Model/Bound/Att1.lean, Inst/Model/Bound/Att2.lean): the bound (FL9') for one pair b, and
    what Steps A1 to A4 give for it.
  Labels such as (FL9'), (FA1) and Step A1 link docstrings.
  Notation: `scl : Scl`: the scales of one segment, and the final normalisation
  (Inst/Model/Scl.lean); `D : Dim`: the sizes of an attention segment (Inst/Model/Att/Index.lean;
  there: key/value heads g, below `D.nG`; positions i, j, below `D.T`; channels n, below `D.ch`;
  pairs b = na λ + a of a layer λ of the segment and the number a of a query head among those of its
  key/value head, below `D.nb`); `tb : Tables`: the five table functions that the program reads
  (Inst/Model/Program.lean); `t : Raw → ℤ`: an integer for each of the names of the cells (`Raw`);
  ρ : `Reg`: the two regions (Inst/Model/Att/Trace.lean); `p : ℕ`: the modulus of the congruences.
-/
import Inst.Model.Att.Trace

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset

/-- The field relation of the segment, as congruences between integers. -/
structure IntRel [scl : Scl] (D : Dim) (tb : Tables) (p : ℕ) (t : Raw → ℤ) : Prop where
  cell : ∀ c : Raw, c.Valid D → |t c| < 2 ^ 18
  k1 : ∀ ρ b x,
    b < D.nb → x < 2 ^ D.lReg ρ → ∃ ι < 2 ^ 16, (p : ℤ) ∣ key1 t ρ b x - (tau1 D.sh).row ι
  k2 : ∀ ρ b x,
    b < D.nb → x < 2 ^ D.lReg ρ → ∃ ι < 2 ^ 16, (p : ℤ) ∣ key2 D t ρ b x - (tau2 D.sh D.u0 tb).row ι
  k3W : ∀ χ b g i n, χ < 2 → b < D.nb → g < D.nG → i < D.T → n < D.ch →
    ∃ ι < 2 ^ 16, (p : ℤ) ∣ key3W D t χ b g i n - (ι : ℕ)
  k3X : ∀ b g i, b < D.nb → g < D.nG → i < D.T → ∃ ι < 2 ^ 16, (p : ℤ) ∣ key3X D t b g i - (ι : ℕ)
  k4 : ∀ b g i n,
    b < D.nb → g < D.nG → i < D.T → n < D.ch → ∃ ι < 2 ^ 16, (p : ℤ) ∣ key4 t b g i n - tau4.row ι
  at1 : ∀ k b g i,
    k < D.lT → b < D.nb → g < D.nG → i < D.T → (p : ℤ) ∣ ibV t k b g i * (ibV t k b g i - 1)
  at2 : ∀ b g i, b < D.nb → g < D.nG → i < D.T →
    (p : ℤ) ∣ mxV t b g i - ∑ n ∈ range D.ch, qryV t b g i n * sel D t b g i n
  at3 : ∀ b g i, b < D.nb → g < D.nG → i < D.T → (p : ℤ) ∣ denV t b g i - EF D t b g i

namespace NW

/-- A multiple of p that is smaller than p in absolute value is 0. -/
theorem eq_of_dvd {p a b : ℤ} (h : p ∣ a - b) (hlt : |a - b| < p) : a = b := by
  have := Int.eq_zero_of_abs_lt_dvd h hlt
  omega

/-- Two digits. -/
theorem split2 {k : ℕ} {a0 a1 e0 e1 : ℤ}
    (h : a0 + 2 ^ k * a1 = e0 + 2 ^ k * e1) (hlt : |a0 - e0| < 2 ^ k) : a0 = e0 ∧ a1 = e1 := by
  have hd : (2 ^ k : ℤ) ∣ a0 - e0 := ⟨e1 - a1, by linarith [mul_sub (2 ^ k : ℤ) e1 a1]⟩
  have h0 : a0 = e0 := eq_of_dvd hd hlt
  refine ⟨h0, ?_⟩
  subst h0
  exact mul_left_cancel₀ (pow_ne_zero k (by norm_num : (2 : ℤ) ≠ 0)) (add_left_cancel h)

end NW

/-! ## The bounds that follow from condition (1) -/

namespace IntRel
variable [scl : Scl]
variable {D : Dim} {tb : Tables} {p : ℕ} {t : Raw → ℤ} (h : IntRel D tb p t)
include h

theorem cell' {c : Raw} (hc : c.Valid D) : -262143 ≤ t c ∧ t c ≤ 262143 := by
  have := abs_lt.mp (h.cell c hc)
  constructor <;> omega

theorem mxV_abs {b g i : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) :
    |mxV t b g i| ≤ 4415276908287 := by
  have c0 := h.cell' (c := .mx 0 b g i) ⟨by norm_num, hb, hg, hi⟩
  have c1 := h.cell' (c := .mx 1 b g i) ⟨by norm_num, hb, hg, hi⟩
  have c2 := h.cell' (c := .mx 2 b g i) ⟨by norm_num, hb, hg, hi⟩
  have c3 := h.cell' (c := .mx 3 b g i) ⟨by norm_num, hb, hg, hi⟩
  simp only [mxV, sum_range_succ, sum_range_zero]
  rw [abs_le]
  constructor <;> omega

theorem denV_abs {b g i : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) :
    |denV t b g i| ≤ 4415276908287 := by
  have c0 := h.cell' (c := .den 0 b g i) ⟨by norm_num, hb, hg, hi⟩
  have c1 := h.cell' (c := .den 1 b g i) ⟨by norm_num, hb, hg, hi⟩
  have c2 := h.cell' (c := .den 2 b g i) ⟨by norm_num, hb, hg, hi⟩
  have c3 := h.cell' (c := .den 3 b g i) ⟨by norm_num, hb, hg, hi⟩
  simp only [denV, sum_range_succ, sum_range_zero]
  rw [abs_le]
  constructor <;> omega

theorem outV_abs {b g i n : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    |outV t b g i n| ≤ 67370751 := by
  have c0 := h.cell' (c := .out 0 b g i n) ⟨by norm_num, hb, hg, hi, hn⟩
  have c1 := h.cell' (c := .out 1 b g i n) ⟨by norm_num, hb, hg, hi, hn⟩
  simp only [outV, sum_range_succ, sum_range_zero]
  rw [abs_le]
  constructor <;> omega

theorem ibV_abs {k b g i : ℕ} (hk : k < D.lT) (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) :
    -262143 ≤ ibV t k b g i ∧ ibV t k b g i ≤ 262143 :=
  h.cell' (c := .ib k b g i) ⟨hk, hb, hg, hi⟩

theorem qhV_abs {b g i n : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    (-262015 ≤ qhV t b g i n ∧ qhV t b g i n ≤ 262271) ∧
    (-262015 ≤ qhV' t b g i n ∧ qhV' t b g i n ≤ 262271) := by
  have c0 := h.cell' (c := .qh b g i n) ⟨hb, hg, hi, hn⟩
  have c1 := h.cell' (c := .qh' b g i n) ⟨hb, hg, hi, hn⟩
  simp only [qhV, qhV']
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

/-- the five cells of an entry of a region: r0, r1 (a cell plus 128), the flag, and the weight w0 +
256 w1 -/
theorem place_abs {ρ : Reg} {b x : ℕ} (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    (-262015 ≤ r0 t ρ b x ∧ r0 t ρ b x ≤ 262271) ∧
    (-262015 ≤ r1 t ρ b x ∧ r1 t ρ b x ≤ 262271) ∧
    (-262143 ≤ flV t ρ b x ∧ flV t ρ b x ≤ 262143) ∧
    |wtV t ρ b x| ≤ 67370879 := by
  have c0 := h.cell' (c := .c ρ 0 b x) ⟨by norm_num, hb, hx⟩
  have c1 := h.cell' (c := .c ρ 1 b x) ⟨by norm_num, hb, hx⟩
  have c2 := h.cell' (c := .c ρ 2 b x) ⟨by norm_num, hb, hx⟩
  have c3 := h.cell' (c := .c ρ 3 b x) ⟨by norm_num, hb, hx⟩
  have c4 := h.cell' (c := .c ρ 4 b x) ⟨by norm_num, hb, hx⟩
  simp only [r0, r1, flV, wtV, w0, w1]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> first | omega | (rw [abs_le]; constructor <;> omega)

end IntRel

/-! ## The index of the looked-up value of a family in the vector of its call -/

section Idx
variable [scl : Scl]
variable {R : Type}

omit [scl : Scl] in
theorem twoFam_fst {nb l l' : ℕ} {f f' : ℕ → ℕ → R} {pad : R} {b x : ℕ}
    (hb : b < nb) (hx : x < 2 ^ l) :
    b * 2 ^ l + x < nb * 2 ^ l ∧ twoFam nb l l' f f' pad (b * 2 ^ l + x) = f b x := by
  have hlt : b * 2 ^ l + x < nb * 2 ^ l := by
    have : (b + 1) * 2 ^ l ≤ nb * 2 ^ l := Nat.mul_le_mul_right _ hb
    rw [Nat.succ_mul] at this
    omega
  refine ⟨hlt, ?_⟩
  unfold twoFam
  rw [if_pos hlt, (Dim.div_step (Nat.two_pow_pos l) hx).1, (Dim.div_step (Nat.two_pow_pos l) hx).2]

omit [scl : Scl] in
theorem twoFam_snd {nb l l' : ℕ} {f f' : ℕ → ℕ → R} {pad : R} {b x : ℕ}
    (hb : b < nb) (hx : x < 2 ^ l') :
    nb * 2 ^ l + (b * 2 ^ l' + x) < nb * 2 ^ l + nb * 2 ^ l' ∧
    twoFam nb l l' f f' pad (nb * 2 ^ l + (b * 2 ^ l' + x)) = f' b x := by
  have hlt : b * 2 ^ l' + x < nb * 2 ^ l' := by
    have : (b + 1) * 2 ^ l' ≤ nb * 2 ^ l' := Nat.mul_le_mul_right _ hb
    rw [Nat.succ_mul] at this
    omega
  refine ⟨by omega, ?_⟩
  unfold twoFam
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos hlt,
    (Dim.div_step (Nat.two_pow_pos l') hx).1, (Dim.div_step (Nat.two_pow_pos l') hx).2]

end Idx

namespace Dim
variable (D : Dim)

theorem ch_pos : 0 < D.ch := Nat.two_pow_pos _
theorem nG_pos : 0 < D.nG := Nat.two_pow_pos _
theorem T_pos : 0 < D.T := Nat.mul_pos D.nBlk_pos D.B_pos

/-- the inner index (χ | g | i | n) of a piece (3W, b) -/
theorem idxW {χ g i n : ℕ} (hχ : χ < 2) (hg : g < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    ((χ * D.nG + g) * D.T + i) * D.ch + n < 2 ^ D.lW ∧
    (((χ * D.nG + g) * D.T + i) * D.ch + n) / D.ch / D.T / D.nG = χ ∧
    (((χ * D.nG + g) * D.T + i) * D.ch + n) / D.ch / D.T % D.nG = g ∧
    (((χ * D.nG + g) * D.T + i) * D.ch + n) / D.ch % D.T = i ∧
    (((χ * D.nG + g) * D.T + i) * D.ch + n) % D.ch = n := by
  rw [(div_step D.ch_pos hn).1, (div_step D.ch_pos hn).2, (div_step D.T_pos hi).1,
    (div_step D.T_pos hi).2, (div_step D.nG_pos hg).1, (div_step D.nG_pos hg).2]
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  have e : 2 ^ D.lW = 2 * D.nG * D.T * D.ch := by
    unfold lW
    rw [pow_add, pow_add, pow_add, ← D.T_eq]
    rfl
  rw [e]
  have h1 : χ * D.nG + g + 1 ≤ 2 * D.nG := by nlinarith
  have h2 : (χ * D.nG + g) * D.T + i + 1 ≤ 2 * D.nG * D.T := by nlinarith
  nlinarith

/-- the inner index (g | i) of a piece (3X, b) -/
theorem idxX {g i : ℕ} (hg : g < D.nG) (hi : i < D.T) :
    g * D.T + i < 2 ^ D.lX ∧ (g * D.T + i) / D.T = g ∧ (g * D.T + i) % D.T = i := by
  refine ⟨?_, (div_step D.T_pos hi).1, (div_step D.T_pos hi).2⟩
  have e : 2 ^ D.lX = D.nG * D.T := by
    unfold lX
    rw [pow_add, ← D.T_eq]
    rfl
  rw [e]
  nlinarith

/-- the inner index (g | i | n) of a piece (4, b) -/
theorem idx4 {g i n : ℕ} (hg : g < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    (g * D.T + i) * D.ch + n < 2 ^ D.l4 ∧
    ((g * D.T + i) * D.ch + n) / D.ch / D.T = g ∧
    ((g * D.T + i) * D.ch + n) / D.ch % D.T = i ∧
    ((g * D.T + i) * D.ch + n) % D.ch = n := by
  rw [(div_step D.ch_pos hn).1, (div_step D.ch_pos hn).2,
    (div_step D.T_pos hi).1, (div_step D.T_pos hi).2]
  refine ⟨?_, rfl, rfl, rfl⟩
  have e : 2 ^ D.l4 = D.nG * D.T * D.ch := by
    unfold l4
    rw [pow_add, pow_add, ← D.T_eq]
    rfl
  rw [e]
  have h1 : g * D.T + i + 1 ≤ D.nG * D.T := by nlinarith
  nlinarith

end Dim

/-! ## From the relation over ZMod p -/

section Bridge
variable {D : Dim} {tb : Tables} {p : ℕ} {t : Raw → ℤ}

/-- Under the field relation over ZMod p (`h`), a looked-up value in a piece is congruent modulo p
to a row of its table. -/
theorem key_dvd [scl : Scl] (h : RFraw D tb (ZMod p) t) (c : Fin 4) {X : ℕ} (hX : X < D.used c) :
    ∃ ι < (lut D tb c).rows, (p : ℤ) ∣ keyVec D tb t c X - (lut D tb c).row ι := by
  obtain ⟨ι, hι, he⟩ := h.2.1 c X hX
  rw [key_cast] at he
  exact ⟨ι, hι, (dvd_sub_comm).mp ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp he)⟩

theorem idn_dvd [scl : Scl] (h : RFraw D tb (ZMod p) t) {j : Idn} (hj : j.Valid D) :
    (p : ℤ) ∣ idnVal D t j := by
  have he := h.2.2 j hj
  rw [idn_cast] at he
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp he

/-- The field relation over ZMod p, read over the integers. -/
theorem intRel_of_rfraw [scl : Scl] (h : RFraw D tb (ZMod p) t) : IntRel D tb p t where
  cell := h.1
  k1 := fun ρ b x hb hx => by
    cases ρ with
    | M =>
      obtain ⟨h1, h2⟩ := twoFam_fst
        (l' := D.lD) (f := key1 t .M) (f' := key1 t .D) (pad := (((lut D tb 0).pad : ℤ) : ℤ)) hb hx
      have := key_dvd h 0 (X := b * 2 ^ D.lM + x) (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
      rwa [show keyVec D tb t 0 (b * 2 ^ D.lM + x) = key1 t .M b x from h2] at this
    | D =>
      obtain ⟨h1, h2⟩ := twoFam_snd
        (l := D.lM) (f := key1 t .M) (f' := key1 t .D) (pad := (((lut D tb 0).pad : ℤ) : ℤ)) hb hx
      have := key_dvd h 0 (X := D.nb * 2 ^ D.lM + (b * 2 ^ D.lD + x)) h1
      rwa [show keyVec D tb t 0 (D.nb * 2 ^ D.lM + (b * 2 ^ D.lD + x)) = key1 t .D b x
          from h2] at this
  k2 := fun ρ b x hb hx => by
    cases ρ with
    | M =>
      obtain ⟨h1, h2⟩ := twoFam_fst (l' := D.lD) (f := key2 D t .M) (f' := key2 D t .D)
        (pad := (((lut D tb 1).pad : ℤ) : ℤ)) hb hx
      have := key_dvd h 1 (X := b * 2 ^ D.lM + x) (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
      rwa [show keyVec D tb t 1 (b * 2 ^ D.lM + x) = key2 D t .M b x from h2] at this
    | D =>
      obtain ⟨h1, h2⟩ := twoFam_snd (l := D.lM) (f := key2 D t .M) (f' := key2 D t .D)
        (pad := (((lut D tb 1).pad : ℤ) : ℤ)) hb hx
      have := key_dvd h 1 (X := D.nb * 2 ^ D.lM + (b * 2 ^ D.lD + x)) h1
      rwa [show keyVec D tb t 1 (D.nb * 2 ^ D.lM + (b * 2 ^ D.lD + x)) = key2 D t .D b x
          from h2] at this
  k3W := fun χ b g i n hχ hb hg hi hn => by
    obtain ⟨y0, y1, y2, y3, y4⟩ := D.idxW hχ hg hi hn
    obtain ⟨h1, h2⟩ := twoFam_fst (l' := D.lX)
      (f := fun b y =>
          key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG) (y / D.ch % D.T) (y % D.ch))
      (f' := fun b y => key3X D t b (y / D.T) (y % D.T)) (pad := (((lut D tb 2).pad : ℤ) : ℤ)) hb y0
    have := key_dvd h 2 (X := b * 2 ^ D.lW + (((χ * D.nG + g) * D.T + i) * D.ch + n))
      (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
    rw [show keyVec D tb t 2 (b * 2 ^ D.lW + (((χ * D.nG + g) * D.T + i) * D.ch + n)) = _
        from h2] at this
    simp only [y1, y2, y3, y4] at this
    exact this
  k3X := fun b g i hb hg hi => by
    obtain ⟨y0, y1, y2⟩ := D.idxX hg hi
    obtain ⟨h1, h2⟩ := twoFam_snd (l := D.lW)
      (f := fun b y =>
          key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG) (y / D.ch % D.T) (y % D.ch))
      (f' := fun b y => key3X D t b (y / D.T) (y % D.T)) (pad := (((lut D tb 2).pad : ℤ) : ℤ)) hb y0
    have := key_dvd h 2 (X := D.nb * 2 ^ D.lW + (b * 2 ^ D.lX + (g * D.T + i))) h1
    rw [show keyVec D tb t 2 (D.nb * 2 ^ D.lW + (b * 2 ^ D.lX + (g * D.T + i))) = _ from h2] at this
    simp only [y1, y2] at this
    exact this
  k4 := fun b g i n hb hg hi hn => by
    obtain ⟨y0, y1, y2, y3⟩ := D.idx4 hg hi hn
    obtain ⟨h1, h2⟩ := twoFam_fst (l' := 0)
      (f := fun b y => key4 t b (y / D.ch / D.T) (y / D.ch % D.T) (y % D.ch))
      (f' := fun _ _ => (((lut D tb 3).pad : ℤ) : ℤ)) (pad := (((lut D tb 3).pad : ℤ) : ℤ)) hb y0
    have := key_dvd h 3 (X := b * 2 ^ D.l4 + ((g * D.T + i) * D.ch + n)) h1
    rw [show keyVec D tb t 3 (b * 2 ^ D.l4 + ((g * D.T + i) * D.ch + n)) = _ from h2] at this
    simp only [y1, y2, y3] at this
    exact this
  at1 := fun k b g i hk hb hg hi => idn_dvd h (j := .at1 k b g i) ⟨hk, hb, hg, hi⟩
  at2 := fun b g i hb hg hi => idn_dvd h (j := .at2 b g i) ⟨hb, hg, hi⟩
  at3 := fun b g i hb hg hi => idn_dvd h (j := .at3 b g i) ⟨hb, hg, hi⟩

end Bridge

/-! ## The interface between the two halves -/

/-- (FL9') for the pair b: qry_b, and key, val of its layer, are at most 2,047 in absolute value. -/
def InB (D : Dim) (t : Raw → ℤ) (b : ℕ) : Prop :=
  (∀ g < D.nG, ∀ i < D.T, ∀ n < D.ch, |qryV t b g i n| ≤ 2047) ∧
  ∀ g < D.nG,
    ∀ j < D.T, ∀ n < D.ch, |keyV t (D.lamOf b) g j n| ≤ 2047 ∧ |valV t (D.lamOf b) g j n| ≤ 2047

/-- What Steps A1 to A4 give for the pair b: (FA1), (FA2), (FA5), (FA6) with (FA4). -/
structure Half1 [scl : Scl] (D : Dim) (t : Raw → ℤ) (b : ℕ) : Prop where
  fa1 : ∀ ρ x, x < 2 ^ D.lReg ρ →
    0 ≤ rm t ρ b x ∧ rm t ρ b x < 2 ^ 16 ∧ flV t ρ b x = if 2 ^ D.sh ≤ rm t ρ b x then 1 else 0
  fa2 : ∀ g i n, g < D.nG → i < D.T → n < D.ch →
    (0 ≤ qhV t b g i n ∧ qhV t b g i n ≤ 255) ∧ (0 ≤ qhV' t b g i n ∧ qhV' t b g i n ≤ 255)
  fa5 : ∀ g i j, g < D.nG → i < D.T → j < D.T → |scV D t b g i j| ≤ Smax
  fa6 : ∀ g i, g < D.nG → i < D.T → ∃ js ≤ i, mxV t b g i = scV D t b g i js

end Inst.Model.AttSeg

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/Unit.lean: one hidden unit of a feed-forward block: its values, its eight keys
(looked-up values), what the keys imply, and the honest values.

Everything is about the numbers of one hidden unit at one position: seven integers (the values of
the arrays, offsets included: `val`, Inst/Model/FF/Trace.lean) and the two accumulators Ag, Au. No
cells, no layout, no layer. The same statements serve a dense layer, the shared expert and the
routed expert: only the accumulators and the shifts differ.
  `UnitV`                the seven values; `UnitV.gw` = g0 + 256 gh, `UnitV.hh` = sl · up
  `keyG`, .., `keyCG`    the eight keys
  `Gate p tb v`, `gate_sound`    the keys G0, F, CG, UT only, under `Adm`, `TabOK`, `Small`; among
                         the conclusions |gw| ≤ 2^22 + 128, |sl| ≤ 4,095. No accumulator is read.
  `Keys p tb kg ku Ag Au v`, `unit_sound`    all eight keys, under `Adm`, `TabOK`, `Small` and |Ag|,
                         |Au| ≤ Ab: g0, gh, gc, sl, up and the derived gw, hh are those of the
                         integer model's `UNIT` on every input (z, wg, wu) with Ag = Σ z wg and Au =
                         Σ z wu, rg and ru are the honest high digits, and `UNIT.OK` holds
  `hon tb d z wg wu kg ku`       the honest values; `hon_keys`, `hon_ranges`
The modulus p and the bounds B1, B2 (values of one and of two cells) and Ab (accumulators) are
parameters; the size conditions are the structure `Adm`. `adm_ref`: they hold at the reference
sizes (the numbers: its docstring), for shifts up to 24. The keys G, U, GH, UH are the two keys of a
rounding for every shift (Inst/Model/Common/Site.lean, Sections 5 to 8: `ssite`, `shigh`), as in the
implementation. (U1) to (U6): the docstrings of `UNIT`, Inst/Model/Program.lean; labels such as
(FL4) and "Step L1" link one docstring to another.
Notation:
  `Adm p B1 B2 Ab kg ku`: a record of inequalities: kg, ku ≤ 24, and lower bounds on p in terms of
    B1, B2, Ab, kg, ku, and two upper bounds on B2 (`flG`, `cgG`); the doc comments over the fields
    name the steps.
  `InLut p L key`: "the key is congruent modulo p to an entry of the table"; `InLutZ L key`: "the
    key is an entry of the table" (Inst/Model/Common/TableKeys.lean).
  `R8`, `R16`, `FL tb`, `FS tb`: tables (`Lut`, Inst/Model/Tables.lean): "ι, for ι < 2^8"; "ι, for ι
    < 2^16"; "FL (SiLU)"; "FS (sigmoid; clamp of the gate)".
  `dn k`: "dn(k) = max(0, 16 − k): the remainder of a rounding by k is scaled by 2^dn(k), so that it
    fills 16 bits at least."; `Site.up k`: "up(k) = max(k, 16): the number of bits of the scaled
    remainder."; `hd A k`: of the remainder of a rounding, `rem A k`: "Its high digit: hd(A, k) =
    ⌊rem(A, k) / 2^16⌋."; `ssite`: "The low key for every shift: the scaled remainder without its
    high digit."; `shigh`: "The high key for every shift." (Inst/Model/Common/Site.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Common.TableKeys

set_option autoImplicit false

namespace Inst.Model.Unit

open Inst.Model.Site Inst.Model.TableKeys

/-- The values of one hidden unit at one position (offsets included): the balanced low byte and the
high part of the gate, its clamp, the activation, the up projection, and the high digits of the two
roundings. -/
structure UnitV where
  g0 : ℤ
  gh : ℤ
  gc : ℤ
  sl : ℤ
  up : ℤ
  rg : ℤ
  ru : ℤ

namespace UnitV
variable (v : UnitV)
/-- gw = g0 + 256 gh -/
def gw : ℤ := v.g0 + 256 * v.gh
/-- hh = sl · up -/
def hh : ℤ := v.sl * v.up
end UnitV

/-! ## 1. The eight keys -/

section Keys
variable (v : UnitV) (kg ku : ℕ) (Ag Au : ℤ)
def keyG : ℤ := ssite Ag v.gw v.rg kg
def keyU : ℤ := ssite Au v.up v.ru ku
def keyUT : ℤ := v.up + 2 ^ 15
def keyGH : ℤ := shigh v.rg kg 24
def keyUH : ℤ := shigh v.ru ku 24
def keyG0 : ℤ := v.g0 + 128
def keyF : ℤ := (v.g0 + 256 * v.gc + 2 ^ 15) + 2 ^ 28 * (v.sl + 2 ^ 12)
def keyCG : ℤ := (v.gh + 49152) + 2 ^ 28 * (v.gc + 128) + 2 ^ 40
end Keys

/-- the four keys G0, F, CG, UT, which read no accumulator, are congruent to entries of their tables
-/
structure Gate (p : ℤ) (tb : Tables) (v : UnitV) : Prop where
  G0 : InLut p R8 (keyG0 v)
  F : InLut p (FL tb) (keyF v)
  CG : InLut p (FS tb) (keyCG v)
  UT : InLut p R16 (keyUT v)

/-- all eight keys are congruent to entries of their tables -/
structure Keys (p : ℤ) (tb : Tables) (kg ku : ℕ) (Ag Au : ℤ) (v : UnitV) :
    Prop extends Gate p tb v where
  G : InLut p R16 (keyG v kg Ag)
  GH : InLut p R8 (keyGH v kg)
  U : InLut p R16 (keyU v ku Au)
  UH : InLut p R8 (keyUH v ku)

/-- Condition (1) (every valid cell is below a bound in absolute value: `RFraw`,
Inst/Model/FF/Cast.lean) for these values: B1 bounds a value of one cell, B2 a value of two cells; a
high digit of one cell has the offset 128. -/
structure Small (B1 B2 : ℤ) (v : UnitV) : Prop where
  g0 : |v.g0| ≤ B1
  gh : |v.gh| ≤ B2
  gc : |v.gc| ≤ B1
  gk : |256 * v.gc + v.g0| ≤ B2
  sl : |v.sl| ≤ B2
  up : |v.up| ≤ B2
  rg : |v.rg| ≤ B1 + 128
  ru : |v.ru| ≤ B1 + 128

/-- The size conditions. -/
structure Adm (p B1 B2 Ab : ℤ) (kg ku : ℕ) : Prop where
  kg24 : kg ≤ 24
  ku24 : ku ≤ 24
  /-- Step L1: G0, UT, and a high digit of one cell -/
  g0 : B1 + 128 + 2 ^ 8 ≤ p
  ut : B2 + 2 ^ 15 + 2 ^ 16 ≤ p
  hi : 2 ^ 8 * (B1 + 128) + 2 ^ 8 ≤ p
  /-- Step L2 -/
  fl : (B2 + 2 ^ 15) + 2 ^ 28 * (B2 + 2 ^ 12) + 2 ^ 42 ≤ p
  flG : B2 + 2 ^ 15 + 2 ^ 16 < 2 ^ 28
  /-- Step L3 -/
  cg : (B2 + 49152) + 2 ^ 28 * (B1 + 128) + 2 ^ 40 + 2 ^ 41 ≤ p
  cgG : B2 + 49152 + 2 ^ 16 < 2 ^ 28
  /-- Steps L7, L7r -/
  g : 2 ^ dn kg * (Ab + 2 ^ (kg - 1) + 2 ^ kg * (2 ^ 22 + 128)) + 2 ^ 16 * (B1 + 128) + 2 ^ 16 ≤ p
  u : 2 ^ dn ku * (Ab + 2 ^ (ku - 1) + 2 ^ ku * 2 ^ 15) + 2 ^ 16 * (B1 + 128) + 2 ^ 16 ≤ p

/-- The two bounds on the public tables that are used: (Tab3), (Tab4). -/
structure TabOK (tb : Tables) : Prop where
  silu : ∀ ι < 2 ^ 16, -4095 ≤ tb.SILU (ι : ℕ) ∧ tb.SILU (ι : ℕ) ≤ 4095
  sigm : ∀ ι < 2 ^ 15, 0 ≤ tb.SIGM ((ι : ℕ) + 2 ^ 14) ∧ tb.SIGM ((ι : ℕ) + 2 ^ 14) ≤ 2 ^ 16

theorem TabOK.of_ok {P : Params} {tb : Tables} (h : tb.OK P) : TabOK tb := ⟨h.1, h.2.1⟩

/-! ## 2. What the keys imply -/

/-- If g0 is a balanced byte, then g0 and gh are the balanced low byte and the high part of gw =
g0 + 256 gh. -/
theorem gate_writing {g0 gh : ℤ} (hg0 : -128 ≤ g0 ∧ g0 ≤ 127) :
    lowByte (g0 + 256 * gh) = g0 ∧ (g0 + 256 * gh - g0) / 256 = gh := by
  refine ⟨by unfold lowByte; omega, by omega⟩

/-- The gate without its rounding (Steps L1, L2, L3), under the hypotheses below: (FL6) up fits 16
bits; (FL10) sl = SILU[gk + 2^15], |sl| ≤ 4,095, gk = 256 gc + g0; (FL11) −2^14 ≤ gh < 2^14 and gc =
clamp_127(gh); and |gw| ≤ 2^22 + 128; (FL4) and (FL8) follow from the conclusions (the labels'
words: Inst/Model/Common/TableKeys.lean). (U2), (U3), (U4) as functions of gw, with the range
conditions of (U2) and (U5). -/
theorem gate_sound {p B1 B2 Ab : ℤ} {kg ku : ℕ} {tb : Tables} {v : UnitV}
    (adm : Adm p B1 B2 Ab kg ku) (tab : TabOK tb) (sm : Small B1 B2 v) (h : Gate p tb v) :
    v.g0 = lowByte v.gw ∧ v.gh = (v.gw - lowByte v.gw) / 256 ∧ (-2 ^ 14 ≤ v.gh ∧ v.gh < 2 ^ 14) ∧
    v.gc = clamp 127 v.gh ∧ v.sl = tb.SILU (256 * v.gc + v.g0 + 2 ^ 15) ∧ Fits16 v.up ∧
    |v.gw| ≤ 2 ^ 22 + 128 ∧ |v.sl| ≤ 4095 := by
  have hg0 := g0_key sm.g0 adm.g0 h.G0
  obtain ⟨f1, f2, f3⟩ := fl_key sm.gk sm.sl tab.silu adm.fl adm.flG h.F
  obtain ⟨c1, c2⟩ := cg_key sm.gh sm.gc tab.sigm adm.cg adm.cgG hg0 f1 h.CG
  obtain ⟨w1, w2⟩ := gate_writing (gh := v.gh) hg0
  refine ⟨w1.symm, ?_, c1, c2, f2, ut_key sm.up adm.ut h.UT, ?_, f3⟩
  · show v.gh = (v.g0 + 256 * v.gh - lowByte (v.g0 + 256 * v.gh)) / 256
    rw [w1, w2]
  · unfold UnitV.gw
    rw [abs_le]
    omega

/-- One hidden unit is sound (Steps L1, L2, L3, L7 or L7r): under the hypotheses below, g0, gh, gc,
sl, up, gw, hh are those of the model's UNIT, on every input whose two accumulators are Ag and Au;
rg, ru are the honest high digits; no range condition of UNIT fails. -/
theorem unit_sound {p B1 B2 Ab : ℤ} {kg ku : ℕ} {tb : Tables} {v : UnitV} {Ag Au : ℤ}
    (adm : Adm p B1 B2 Ab kg ku) (tab : TabOK tb) (sm : Small B1 B2 v) (hAg : |Ag| ≤ Ab)
    (hAu : |Au| ≤ Ab) (h : Keys p tb kg ku Ag Au v) {d : ℕ} {z wg wu : Vec}
    (eg : Ag = dot d z wg) (eu : Au = dot d z wu) :
    v.gw = UNIT.gw d z wg kg ∧ v.g0 = UNIT.g0 d z wg kg ∧ v.gh = UNIT.gh d z wg kg ∧
    v.gc = UNIT.gc d z wg kg ∧ v.sl = UNIT.sl tb d z wg kg ∧
    v.up = UNIT.up d z wu ku ∧ v.hh = UNIT.hh tb d z wg wu kg ku ∧
    UNIT.OK d z wg wu kg ku ∧ v.rg = hd Ag kg ∧ v.ru = hd Au ku := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, _⟩ := gate_sound adm tab sm h.toGate
  have hup : |v.up| ≤ 2 ^ 15 := by
    unfold Fits16 at a6
    rw [abs_le]
    omega
  have hmul : ∀ k : ℕ, (2 : ℤ) ^ (24 - Site.up k) * (B1 + 128) + 2 ^ 8 ≤ p := fun k => by
    have h1 : (2 : ℤ) ^ (24 - Site.up k) ≤ 2 ^ 8 := two_pow_top_sub_le k rfl
    have h2 : (0 : ℤ) ≤ B1 + 128 := le_trans (abs_nonneg _) sm.rg
    have := mul_le_mul_of_nonneg_right h1 h2
    have := adm.hi
    linarith
  obtain ⟨rg0, rg1⟩ := shigh_sound (w := 8) rfl adm.kg24 sm.rg (hmul kg) h.GH.r8
  obtain ⟨ru0, ru1⟩ := shigh_sound (w := 8) rfl adm.ku24 sm.ru (hmul ku) h.UH.r8
  obtain ⟨g1, g2, g3⟩ := ssite_sound hAg a7 sm.rg rg0 rg1 adm.g h.G.r16
  obtain ⟨u1, u2, u3⟩ := ssite_sound hAu hup sm.ru ru0 ru1 adm.u h.U.r16
  have egw : v.gw = UNIT.gw d z wg kg := by
    unfold UNIT.gw
    rw [← eg]
    exact g1
  have eg0 : v.g0 = UNIT.g0 d z wg kg := by
    unfold UNIT.g0
    rw [← egw]
    exact a1
  have egh : v.gh = UNIT.gh d z wg kg := by
    unfold UNIT.gh
    rw [← egw, ← eg0, a1]
    exact a2
  have egc : v.gc = UNIT.gc d z wg kg := by
    unfold UNIT.gc
    rw [← egh]
    exact a4
  have esl : v.sl = UNIT.sl tb d z wg kg := by
    unfold UNIT.sl
    rw [← egc, ← eg0]
    exact a5
  have eup : v.up = UNIT.up d z wu ku := by
    unfold UNIT.up
    rw [← eu]
    exact u1
  refine ⟨egw, eg0, egh, egc, esl, eup, ?_,
    ⟨by rw [← egh]; exact a3, by rw [← eup]; exact a6⟩, ?_, ?_⟩
  · unfold UnitV.hh UNIT.hh
    rw [esl, eup]
  · rw [g1] at g2 g3
    exact hd_unique_s g2 g3
  · rw [u1] at u2 u3
    exact hd_unique_s u2 u3

/-- At the reference sizes the size conditions hold, for all shifts up to 24: p = 2^61 − 1, c = 2^18
(the bound on a cell), a value of two cells at most 257 c, accumulators at most 5,120 · 2^11 · 2^12.
-/
theorem adm_ref {kg ku : ℕ} (h2 : kg ≤ 24) (h4 : ku ≤ 24) :
    Adm (2 ^ 61 - 1) (2 ^ 18) (257 * 2 ^ 18) (5120 * 2 ^ 11 * 2 ^ 12) kg ku := by
  have a1 := scaled_le (top := 24) (by norm_num) h2 (5120 * 2 ^ 11 * 2 ^ 12)
    (Qb := 2 ^ 22 + 128) (by norm_num)
  have a2 := two_pow_dn_le kg
  have a3 :=
    scaled_le (top := 24) (by norm_num) h4 (5120 * 2 ^ 11 * 2 ^ 12) (Qb := 2 ^ 15) (by norm_num)
  have a4 := two_pow_dn_le ku
  refine ⟨h2, h4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_⟩
  · linarith
  · linarith

/-! ## 3. The honest values -/

/-- The honest values of a hidden unit: those of the model's UNIT, and the high digits of the two
remainders. -/
def hon (tb : Tables) (d : ℕ) (z wg wu : Vec) (kg ku : ℕ) : UnitV where
  g0 := UNIT.g0 d z wg kg
  gh := UNIT.gh d z wg kg
  gc := UNIT.gc d z wg kg
  sl := UNIT.sl tb d z wg kg
  up := UNIT.up d z wu ku
  rg := hd (dot d z wg) kg
  ru := hd (dot d z wu) ku

section Honest
variable (tb : Tables) (d : ℕ) (z wg wu : Vec) (kg ku : ℕ)

theorem lowByte_bounds (a : ℤ) :
    -128 ≤ lowByte a ∧ lowByte a ≤ 127 ∧ (a - lowByte a) % 256 = 0 := by
  unfold lowByte
  omega

/-- The honest gw is the model's. -/
theorem hon_gw : (hon tb d z wg wu kg ku).gw = UNIT.gw d z wg kg := by
  show UNIT.g0 d z wg kg + 256 * UNIT.gh d z wg kg = _
  unfold UNIT.gh UNIT.g0
  have := lowByte_bounds (UNIT.gw d z wg kg)
  omega

theorem hon_hh : (hon tb d z wg wu kg ku).hh = UNIT.hh tb d z wg wu kg ku := rfl

variable {tb d z wg wu kg ku}

/-- The ranges of the honest values, under `TabOK` and if no range condition of UNIT fails. -/
theorem hon_ranges (tab : TabOK tb) (ok : UNIT.OK d z wg wu kg ku) :
    (-128 ≤ (hon tb d z wg wu kg ku).g0 ∧ (hon tb d z wg wu kg ku).g0 ≤ 127) ∧
    (-2 ^ 14 ≤ (hon tb d z wg wu kg ku).gh ∧ (hon tb d z wg wu kg ku).gh < 2 ^ 14) ∧
    (-127 ≤ (hon tb d z wg wu kg ku).gc ∧ (hon tb d z wg wu kg ku).gc ≤ 127) ∧
    (-4095 ≤ (hon tb d z wg wu kg ku).sl ∧ (hon tb d z wg wu kg ku).sl ≤ 4095) ∧
    Fits16 (hon tb d z wg wu kg ku).up ∧
    (0 ≤ (hon tb d z wg wu kg ku).rg ∧ (hon tb d z wg wu kg ku).rg < 2 ^ (Site.up kg - 16)) ∧
    (0 ≤ (hon tb d z wg wu kg ku).ru ∧ (hon tb d z wg wu kg ku).ru < 2 ^ (Site.up ku - 16)) := by
  have b0 := lowByte_bounds (UNIT.gw d z wg kg)
  have bc := clamp_bounds (c := 127) (by norm_num) (UNIT.gh d z wg kg)
  have hι : 0 ≤ 256 * UNIT.gc d z wg kg + UNIT.g0 d z wg kg + 2 ^ 15 ∧
      256 * UNIT.gc d z wg kg + UNIT.g0 d z wg kg + 2 ^ 15 < 2 ^ 16 := by
    have e1 : UNIT.gc d z wg kg = clamp 127 (UNIT.gh d z wg kg) := rfl
    have e2 : UNIT.g0 d z wg kg = lowByte (UNIT.gw d z wg kg) := rfl
    rw [e1, e2]
    omega
  have hs := tab.silu (256 * UNIT.gc d z wg kg + UNIT.g0 d z wg kg + 2 ^ 15).toNat (by omega)
  rw [Int.toNat_of_nonneg hι.1] at hs
  exact ⟨⟨b0.1, b0.2.1⟩, ok.1, bc, hs, ok.2, hd_bounds_up _ _, hd_bounds_up _ _⟩

/-- All eight honest keys are entries of their tables, over the integers, for shifts up to 24 and if
no range condition of UNIT fails. -/
theorem hon_keys (ok : UNIT.OK d z wg wu kg ku) (hg' : kg ≤ 24) (hu' : ku ≤ 24) :
    InLutZ R8 (keyG0 (hon tb d z wg wu kg ku)) ∧
    InLutZ (FL tb) (keyF (hon tb d z wg wu kg ku)) ∧
    InLutZ (FS tb) (keyCG (hon tb d z wg wu kg ku)) ∧
    InLutZ R16 (keyUT (hon tb d z wg wu kg ku)) ∧
    InLutZ R16 (keyG (hon tb d z wg wu kg ku) kg (dot d z wg)) ∧
    InLutZ R8 (keyGH (hon tb d z wg wu kg ku) kg) ∧
    InLutZ R16 (keyU (hon tb d z wg wu kg ku) ku (dot d z wu)) ∧
    InLutZ R8 (keyUH (hon tb d z wg wu kg ku) ku) := by
  have b0 := lowByte_bounds (UNIT.gw d z wg kg)
  have bc := clamp_bounds (c := 127) (by norm_num) (UNIT.gh d z wg kg)
  have e1 : UNIT.gc d z wg kg = clamp 127 (UNIT.gh d z wg kg) := rfl
  have e2 : UNIT.g0 d z wg kg = lowByte (UNIT.gw d z wg kg) := rfl
  have hfit : Fits16 (256 * UNIT.gc d z wg kg + UNIT.g0 d z wg kg) := by
    unfold Fits16
    rw [e1, e2]
    omega
  have ok2 := ok.2
  unfold Fits16 at ok2
  refine ⟨inLutZ_r8 ?_ ?_, fl_hon tb hfit, cg_hon tb ok.1.1 ok.1.2,
    inLutZ_r16 ?_ ?_, ?_, ?_, ?_, ?_⟩
  · show 0 ≤ UNIT.g0 d z wg kg + 128
    rw [e2]
    omega
  · show UNIT.g0 d z wg kg + 128 < 2 ^ 8
    rw [e2]
    omega
  · show 0 ≤ UNIT.up d z wu ku + 2 ^ 15
    omega
  · show UNIT.up d z wu ku + 2 ^ 15 < 2 ^ 16
    omega
  · have h := ssite_hon (dot d z wg) kg
    have e : keyG (hon tb d z wg wu kg ku) kg (dot d z wg) =
        ssite (dot d z wg) (rhu (dot d z wg) kg) (hd (dot d z wg) kg) kg := by
      unfold keyG
      rw [hon_gw]
      rfl
    rw [e]
    exact inLutZ_r16 h.2.1 h.2.2
  · have h := shigh_hon (dot d z wg) (w := 8) rfl hg'
    exact inLutZ_r8 h.1 h.2
  · have h := ssite_hon (dot d z wu) ku
    exact inLutZ_r16 h.2.1 h.2.2
  · have h := shigh_hon (dot d z wu) (w := 8) rfl hu'
    exact inLutZ_r8 h.1 h.2

end Honest

end Inst.Model.Unit

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/Router.lean: the router of the experts at one position: its values, its keys
(looked-up values) and one identity, what these imply, and the honest values.

Everything is about the numbers of one router at one position: for each of the nx experts the
integers ly, l3, lr, sel, rl and the accumulator Ar e (any integer here; in the model it is
(m W_r)_e); the scale sc; for each channel the input m j and xr j (the letters: Notation, below).
No cells, no layout.
  `RouterV`              the values; `RouterV.lw` e = 8 ly e + l3 e, `RouterV.mr` nx = Σ_e sel e ·
                         lr e
  `keyLR`, .., `keyXR`, `idnJ10`
                         the keys and the identity (J10)
  `one_hot`, `first_max`   Steps L10b, L10c: under the hypotheses of their statements, sel is the
                         indicator of the least index at which lr is greatest: (R4); (FL23) to
                         (FL25)
  `router_sound`         all steps: (R1) to (R6), in the integer model's terms: `rhu`, % 8, `clamp`,
                         `argTo`, SIGM
  `hon tb kr nx m Ar`    the honest values; `hon_keys`, `hon_ranges`
  `argTo_congr`, `argTo_eq`  on the first maximum
The modulus p and the bounds are parameters: B1, B2, B3 for values of one, two, three cells, Ab for
the accumulators, Lb + 1 for the quotients ly; the size conditions are the structure `Adm`.
`adm_ref`: they hold at the reference sizes for all shifts from 8 to 24. The keys LR, LH are the two
keys of a rounding for every shift (Inst/Model/Common/Site.lean, Sections 5 to 8: `ssite`, `shigh`),
as in the implementation. (R1) to (R6), `rhu`: Inst/Model/Program.lean; labels such as (FL22) and
"Step L9" link one docstring to another.
Notation:
  ly, l3, lr, xr, lw, m (maps `ℕ → ℤ`), sc, mr (integers): free values here (fields of `RouterV`; m:
    a binder; lw, mr: formed from them, above), with the names of values of the integer program
    (`FF.lw` .., Inst/Model/Program.lean): "(R1) lw_e = rhu((m Wr)_e, kr)"; "(R2) l3_e = lw_e mod
    8"; "(R2) ly_e = (lw_e − l3_e)/8"; "(R3) lr_e = 8 clamp_2047(ly_e) + l3_e"; "(R4) e* is the
    least e with lr_e = max_{e'} lr_{e'}."; "(R4) mr = lr_{e*}"; "(R5) sc = SIGM[mr + 2^15]"; "(R6)
    xr[j] = rhu(sc · m[j], 16)"; "(PL8) m = NORM(x')".
  sel, rl: maps `ℕ → ℤ`, fields of `RouterV` without a namesake in the program; in `router_sound`'s
    conclusion sel e is 1 at `argTo v.lr (nx - 1)` and 0 elsewhere, and rl e is `hd (Ar e) kr`
    (`hd`, of the remainder `rem (Ar e) kr`: "Its high digit: hd(A, k) = ⌊rem(A, k) / 2^16⌋.",
    Inst/Model/Common/Site.lean).
  kr, nx, d: natural numbers: the shift of (R1); experts e < nx; channels j < d.
  `InLut p L key`: "the key is congruent modulo p to an entry of the table"
    (Inst/Model/Common/TableKeys.lean); `R8`, `R16`, `FC`, `FS tb`: the tables
    (Inst/Model/Tables.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Common.TableKeys

set_option autoImplicit false

namespace Inst.Model.Router

open Finset Inst.Model.Site Inst.Model.TableKeys
open Inst.Model.Ledger (lift_eq)

/-- The values of the router at one position (offsets included: `val`, Inst/Model/FF/Trace.lean). -/
structure RouterV where
  ly : ℕ → ℤ
  l3 : ℕ → ℤ
  lr : ℕ → ℤ
  sel : ℕ → ℤ
  rl : ℕ → ℤ
  sc : ℤ
  xr : ℕ → ℤ

namespace RouterV
variable (v : RouterV)
/-- lw = 8 ly + l3 -/
def lw (e : ℕ) : ℤ := 8 * v.ly e + v.l3 e
/-- mr = Σ_e sel_e lr_e -/
def mr (nx : ℕ) : ℤ := ∑ e ∈ range nx, v.sel e * v.lr e
end RouterV

/-! ## 1. The keys and the identity (J10) -/

section Keys
variable (v : RouterV) (kr nx : ℕ) (m Ar : ℕ → ℤ)
def keyLR (e : ℕ) : ℤ := ssite (Ar e) (v.lw e) (v.rl e) kr
def keyLH (e : ℕ) : ℤ := shigh (v.rl e) kr 24
def keyL3 (e : ℕ) : ℤ := 32 * v.l3 e
def keyCLR (e : ℕ) : ℤ := (v.ly e + 2 ^ 15) + 2 ^ 25 * (v.lr e - v.l3 e) + 2 ^ 39
def keyLT (e : ℕ) : ℤ := 2 * (v.lr e + 2 ^ 14)
def keySEL (e : ℕ) : ℤ := 128 * v.sel e
def keyDD (x : ℕ) : ℤ := v.mr nx - v.lr x - ∑ e ∈ (range nx).filter (x < ·), v.sel e
def keyMR : ℤ := (v.mr nx + 2 ^ 14) + 2 ^ 17 * v.sc
def keyXR (j : ℕ) : ℤ := v.sc * m j + 2 ^ 15 - 2 ^ 16 * v.xr j
def idnJ10 : ℤ := ∑ e ∈ range nx, v.sel e - 1
end Keys

/-- all keys are congruent to entries of their tables, and (J10) holds modulo p -/
structure Keys (p : ℤ) (tb : Tables) (kr nx d : ℕ) (m Ar : ℕ → ℤ) (v : RouterV) : Prop where
  LR : ∀ e < nx, InLut p R16 (keyLR v kr Ar e)
  LH : ∀ e < nx, InLut p R8 (keyLH v kr e)
  L3 : ∀ e < nx, InLut p R8 (keyL3 v e)
  CLR : ∀ e < nx, InLut p FC (keyCLR v e)
  LT : ∀ e < nx, InLut p R16 (keyLT v e)
  SEL : ∀ e < nx, InLut p R8 (keySEL v e)
  DD : ∀ x < nx, InLut p R16 (keyDD v nx x)
  MR : InLut p (FS tb) (keyMR v nx)
  XR : ∀ j < d, InLut p R16 (keyXR v m j)
  J10 : idnJ10 v nx ≡ 0 [ZMOD p]

/-- Condition (1) (every valid cell is below a bound in absolute value: `RFraw`,
Inst/Model/FF/Cast.lean) for these values: B1, B2, B3 bound values of one, two, three cells; the
high digit rl has B1 + 128. -/
structure Small (B1 B2 B3 : ℤ) (nx d : ℕ) (v : RouterV) : Prop where
  ly : ∀ e < nx, |v.ly e| ≤ B2
  l3 : ∀ e < nx, |v.l3 e| ≤ B1
  lr : ∀ e < nx, |v.lr e| ≤ B2
  sel : ∀ e < nx, |v.sel e| ≤ B1
  rl : ∀ e < nx, |v.rl e| ≤ B1 + 128
  sc : |v.sc| ≤ B3
  xr : ∀ j < d, |v.xr j| ≤ B2

/-- The size conditions. Ab bounds the accumulators, Lb + 1 the quotients ly, Mb the inputs m. With
Lb = ⌊(Ab + 2^(kr−1)) / 2^(kr+3)⌋ the fields `quot` and `clrG` are the implementation's condition
(guard-radix-clamp). -/
structure Adm (p B1 B2 B3 Ab Lb Mb : ℤ) (kr nx : ℕ) : Prop where
  kr24 : kr ≤ 24
  b1pos : 0 ≤ B1
  /-- Step L1 -/
  l3 : 32 * B1 + 2 ^ 8 ≤ p
  sel : 128 * B1 + 2 ^ 8 ≤ p
  lt : 2 * (B2 + 2 ^ 14) + 2 ^ 16 ≤ p
  hi : 2 ^ 8 * (B1 + 128) + 2 ^ 8 ≤ p
  /-- Step L9 -/
  lr : 2 ^ dn kr * (Ab + 2 ^ (kr - 1) + 2 ^ kr * (8 * B2 + 7)) + 2 ^ 16 * (B1 + 128) + 2 ^ 16 ≤ p
  quot : Ab + 2 ^ (kr - 1) < 2 ^ kr * (8 * (Lb + 1))
  /-- Step L10a: no wrap-around; `clrG` is the only radix condition that depends on a matrix
  product -/
  clr : Lb + 1 + 2 ^ 15 + 2 ^ 42 ≤ p
  clrG : Lb + 1 + 2 ^ 15 + 2 ^ 16 < 2 ^ 25
  /-- Steps L10b, L10c -/
  j10 : (nx : ℤ) + 1 < p
  dd : 2 ^ 15 + 1 + 2 ^ 16 ≤ p
  /-- Steps L10d, L10e -/
  mr : 2 ^ 15 + 2 ^ 17 * B3 + 2 ^ 41 ≤ p
  xr : 2 ^ 16 * Mb + 2 ^ 15 + 2 ^ 16 * B2 + 2 ^ 16 ≤ p

/-! ## 2. Tools -/

/-- Under the hypotheses below, a rounded quotient is bounded through the accumulator. -/
theorem rhu_lt {A Ab M : ℤ} {k : ℕ} (hA : |A| ≤ Ab) (h : Ab + 2 ^ (k - 1) < 2 ^ k * M) :
    -M < rhu A k ∧ rhu A k < M := by
  have hA' := abs_le.mp hA
  have hk : (0 : ℤ) < 2 ^ k := by positivity
  have h2 : (2 : ℤ) ^ k ≤ 2 * 2 ^ (k - 1) := by
    rcases k with _ | k
    · norm_num
    · rw [Nat.add_sub_cancel, pow_succ]
      linarith
  unfold rhu
  constructor
  · have : -M + 1 ≤ (A + 2 ^ (k - 1)) / 2 ^ k := (Int.le_ediv_iff_mul_le hk).mpr (by nlinarith)
    omega
  · exact Int.ediv_lt_of_lt_mul hk (by nlinarith)

/-- The first maximum depends only on the values up to n. -/
theorem argTo_congr {f g : Vec} : ∀ {n : ℕ}, (∀ j ≤ n, f j = g j) → argTo f n = argTo g n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := argTo_congr (f := f) (g := g) (n := n) fun j hj => h j (by omega)
    have hle : ∀ n : ℕ, argTo g n ≤ n := fun n => by
      induction n with
      | zero => exact le_rfl
      | succ n ihn =>
        simp only [argTo]
        split_ifs <;> omega
    simp only [argTo]
    rw [ih, h (argTo g n) (by have := hle n; omega), h (n + 1) le_rfl]

theorem argTo_spec' (f : Vec) (n : ℕ) :
    argTo f n ≤ n ∧ (∀ j ≤ n, f j ≤ f (argTo f n)) ∧ ∀ j < argTo f n, f j < f (argTo f n) := by
  induction n with
  | zero =>
    exact ⟨le_rfl,
      fun j hj => by rw [Nat.le_zero.1 hj]; exact le_rfl,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    simp only [argTo]
    split_ifs with h
    · refine ⟨le_rfl, fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_ge j (n + 1) with h' | h'
        · exact ((h1 j (by omega)).trans_lt h).le
        · rw [show j = n + 1 by omega]
      · exact (h1 j (by omega)).trans_lt h
    · refine ⟨by omega, fun j hj => ?_, h2⟩
      rcases Nat.lt_or_ge j (n + 1) with h' | h'
      · exact h1 j (by omega)
      · rw [show j = n + 1 by omega]; exact not_lt.1 h

/-- An index e ≤ n at which no value up to n is greater and before which every value is smaller is
the first maximum up to n. -/
theorem argTo_eq {f : Vec} {n e : ℕ} (he : e ≤ n)
    (hmax : ∀ x ≤ n, f x ≤ f e) (hfirst : ∀ x < e, f x < f e) : argTo f n = e := by
  obtain ⟨h1, h2, h3⟩ := argTo_spec' f n
  rcases lt_trichotomy (argTo f n) e with h | h | h
  · have := hfirst _ h
    have := h2 e he
    omega
  · exact h
  · have := h3 e h
    have := hmax _ h1
    omega

/-- Bits that add up to 1 are the indicator of one index. -/
theorem indicator_of_bits (n : ℕ) (s : ℕ → ℤ)
    (hbit : ∀ e < n, s e = 0 ∨ s e = 1) (hsum : ∑ e ∈ range n, s e = 1) :
    ∃ es < n, ∀ e < n, s e = if e = es then 1 else 0 := by
  induction n with
  | zero => simp at hsum
  | succ n ih =>
    rw [sum_range_succ] at hsum
    have hb' : ∀ e < n, s e = 0 ∨ s e = 1 := fun e he => hbit e (by omega)
    rcases hbit n (by omega) with h0 | h1
    · obtain ⟨es, hes, h⟩ := ih hb' (by omega)
      refine ⟨es, by omega, fun e he => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with he' | rfl
      · exact h e he'
      · rw [h0, if_neg (by omega)]
    · have hz : ∑ e ∈ range n, s e = 0 := by omega
      have hall := (sum_eq_zero_iff_of_nonneg (fun e he => by
        rcases hb' e (mem_range.mp he) with h | h <;> omega)).mp hz
      refine ⟨n, by omega, fun e he => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with he' | rfl
      · rw [hall e (mem_range.mpr he'), if_neg (by omega)]
      · rw [h1, if_pos rfl]

/-- For es < n, a sum weighted by the indicator of es is the term at es. -/
theorem sum_indicator_mul {n es : ℕ} {s : ℕ → ℤ} (hes : es < n)
    (hs : ∀ e < n, s e = if e = es then 1 else 0) (f : ℕ → ℤ) :
    ∑ e ∈ range n, s e * f e = f es := by
  rw [sum_congr rfl (fun e he => by
      rw [hs e (mem_range.mp he)] : ∀ e ∈ range n, s e * f e = (if e = es then 1 else 0) * f e)]
  simp [ite_mul, hes]

/-- For es < n, the part after x of the sum of the indicator of es is [x < es]. -/
theorem sum_indicator_after {n es : ℕ} {s : ℕ → ℤ} (hes : es < n)
    (hs : ∀ e < n, s e = if e = es then 1 else 0) (x : ℕ) :
    ∑ e ∈ (range n).filter (x < ·), s e = if x < es then 1 else 0 := by
  rw [sum_filter, sum_congr rfl (fun e he => by
    rw [hs e (mem_range.mp he)]
    by_cases h : e = es
    · subst h; simp
    · simp [h] : ∀ e ∈ range n,
        (if x < e then s e else 0) = if e = es then (if x < es then (1 : ℤ) else 0) else 0)]
  simp [hes]

theorem sum_indicator {n es : ℕ} {s : ℕ → ℤ} (hes : es < n)
    (hs : ∀ e < n, s e = if e = es then 1 else 0) : ∑ e ∈ range n, s e = 1 := by
  have := sum_indicator_mul hes hs fun _ => 1
  simpa using this

/-! ## 3. What the keys imply -/

section Sound
variable {p B1 B2 B3 Ab Lb Mb : ℤ} {kr nx d : ℕ} {tb : Tables} {m Ar : ℕ → ℤ} {v : RouterV}

/-- One logit (Steps L1, L9, L10a): under the hypotheses below, (FL3), (FL5), (FL20), (FL21), (FL22)
hold: (R1), (R2) with its range condition, (R3). -/
theorem logit_sound (adm : Adm p B1 B2 B3 Ab Lb Mb kr nx) (sm : Small B1 B2 B3 nx d v)
    (hA : ∀ e < nx, |Ar e| ≤ Ab) (h : Keys p tb kr nx d m Ar v) {e : ℕ} (he : e < nx) :
    v.lw e = rhu (Ar e) kr ∧
    v.l3 e = rhu (Ar e) kr % 8 ∧
    v.ly e = (rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8 ∧
    Fits16 (v.ly e) ∧
    v.lr e = 8 * clamp 2047 (v.ly e) + v.l3 e ∧
    (-2 ^ 14 ≤ v.lr e ∧ v.lr e < 2 ^ 14) ∧
    v.rl e = hd (Ar e) kr := by
  have hl3 := l3_key (sm.l3 e he) adm.l3 (h.L3 e he)
  have hlr := lt_key (sm.lr e he) adm.lt (h.LT e he)
  have hQ : |v.lw e| ≤ 8 * B2 + 7 := by
    have := abs_le.mp (sm.ly e he)
    unfold RouterV.lw
    rw [abs_le]
    constructor <;> omega
  have hmul : (2 : ℤ) ^ (24 - up kr) * (B1 + 128) + 2 ^ 8 ≤ p := by
    have h1 : (2 : ℤ) ^ (24 - up kr) ≤ 2 ^ 8 := two_pow_top_sub_le kr rfl
    have h2 : (0 : ℤ) ≤ B1 + 128 := by have := adm.b1pos; linarith
    have := mul_le_mul_of_nonneg_right h1 h2
    have := adm.hi
    linarith
  obtain ⟨r0, r1⟩ := shigh_sound (w := 8) rfl adm.kr24 (sm.rl e he) hmul (h.LH e he).r8
  obtain ⟨q1, q2, q3⟩ := ssite_sound (hA e he) hQ (sm.rl e he) r0 r1 adm.lr (h.LR e he).r16
  have hLb := rhu_lt (hA e he) adm.quot
  have hlw : 8 * v.ly e + v.l3 e = rhu (Ar e) kr := q1
  have hly : |v.ly e| ≤ Lb + 1 := by
    rw [abs_le]
    constructor <;> omega
  obtain ⟨c1, c2⟩ := clr_key hly hlr hl3 adm.clr adm.clrG (h.CLR e he)
  refine ⟨q1, by omega, by omega, c1, c2, hlr, ?_⟩
  rw [q1] at q2 q3
  exact hd_unique_s q2 q3

/-- Under the hypotheses below the selection bits are the indicator of one expert (Steps L1, L10b):
(FL2), (FL23). -/
theorem one_hot (adm : Adm p B1 B2 B3 Ab Lb Mb kr nx)
    (sm : Small B1 B2 B3 nx d v) (h : Keys p tb kr nx d m Ar v) :
    ∃ es < nx, ∀ e < nx, v.sel e = if e = es then 1 else 0 := by
  have hbit : ∀ e < nx, v.sel e = 0 ∨ v.sel e = 1 := fun e he =>
    sel_key (sm.sel e he) adm.sel (h.SEL e he)
  refine indicator_of_bits nx v.sel hbit ?_
  have h0 : 0 ≤ ∑ e ∈ range nx, v.sel e :=
    sum_nonneg fun e he => by rcases hbit e (mem_range.mp he) with h | h <;> omega
  have h1 : ∑ e ∈ range nx, v.sel e ≤ ∑ _e ∈ range nx, (1 : ℤ) :=
    sum_le_sum fun e he => by rcases hbit e (mem_range.mp he) with h | h <;> omega
  rw [sum_const, card_range, nsmul_eq_mul, mul_one] at h1
  have hz : idnJ10 v nx = 0 := Ledger.lift_zero h.J10 (by
    have := adm.j10
    unfold idnJ10
    rw [abs_lt]
    constructor <;> linarith)
  unfold idnJ10 at hz
  linarith

/-- Under the hypotheses below the selected logit is the first maximum (Step L10c): (FL24), (FL25).
-/
theorem first_max (adm : Adm p B1 B2 B3 Ab Lb Mb kr nx)
    (hlr : ∀ e < nx, -2 ^ 14 ≤ v.lr e ∧ v.lr e < 2 ^ 14) (h : Keys p tb kr nx d m Ar v) {es : ℕ}
    (hes : es < nx) (hsel : ∀ e < nx, v.sel e = if e = es then 1 else 0) :
    argTo v.lr (nx - 1) = es ∧ v.mr nx = v.lr es := by
  have hmr : v.mr nx = v.lr es := sum_indicator_mul hes hsel _
  have key : ∀ x < nx, 0 ≤ v.lr es - v.lr x - (if x < es then 1 else 0) := by
    intro x hx
    have hk := h.DD x hx
    unfold keyDD at hk
    rw [hmr, sum_indicator_after hes hsel] at hk
    have h1 := hlr x hx
    have h2 := hlr es hes
    refine (r16_key (B := 2 ^ 15 + 1) ?_ adm.dd hk).1
    rw [abs_le]
    split <;> constructor <;> omega
  refine ⟨argTo_eq (by omega) (fun x hx => ?_) (fun x hx => ?_), hmr⟩
  · have := key x (by omega)
    split at this <;> omega
  · have := key x (by omega)
    rw [if_pos hx] at this
    omega

/-- The router is sound (Steps L1, L9, L10a to L10e): under the hypotheses below, (R1) to (R6), in
the integer model's terms. -/
theorem router_sound (adm : Adm p B1 B2 B3 Ab Lb Mb kr nx)
    (hS : ∀ ι < 2 ^ 15, 0 ≤ tb.SIGM ((ι : ℕ) + 2 ^ 14) ∧ tb.SIGM ((ι : ℕ) + 2 ^ 14) ≤ 2 ^ 16)
    (sm : Small B1 B2 B3 nx d v) (hA : ∀ e < nx, |Ar e| ≤ Ab)
    (hm : ∀ j < d, |m j| ≤ Mb) (h : Keys p tb kr nx d m Ar v) :
    (∀ e < nx,
      v.lw e = rhu (Ar e) kr ∧
      v.l3 e = rhu (Ar e) kr % 8 ∧
      v.ly e = (rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8 ∧
      Fits16 (v.ly e) ∧
      v.lr e = 8 * clamp 2047 (v.ly e) + v.l3 e ∧
      v.rl e = hd (Ar e) kr) ∧
    argTo v.lr (nx - 1) < nx ∧
    (∀ e < nx, v.sel e = if e = argTo v.lr (nx - 1) then 1 else 0) ∧
    v.mr nx = v.lr (argTo v.lr (nx - 1)) ∧
    v.sc = tb.SIGM (v.mr nx + 2 ^ 15) ∧
    (0 ≤ v.sc ∧ v.sc ≤ 2 ^ 16) ∧
    ∀ j < d, v.xr j = rhu (v.sc * m j) 16 ∧ |v.xr j| ≤ |m j| := by
  have hlog := fun e he => logit_sound adm sm hA h (e := e) he
  have hlr : ∀ e < nx, -2 ^ 14 ≤ v.lr e ∧ v.lr e < 2 ^ 14 := fun e he => (hlog e he).2.2.2.2.2.1
  obtain ⟨es, hes, hsel⟩ := one_hot adm sm h
  obtain ⟨harg, hmr⟩ := first_max adm hlr h hes hsel
  obtain ⟨s1, s2, s3⟩ := mr_key (by rw [hmr]; exact hlr es hes) sm.sc hS adm.mr h.MR
  rw [harg]
  refine ⟨fun e he =>
      ⟨(hlog e he).1, (hlog e he).2.1, (hlog e he).2.2.1, (hlog e he).2.2.2.1,
        (hlog e he).2.2.2.2.1, (hlog e he).2.2.2.2.2.2⟩,
    hes, hsel, hmr, s1, ⟨s2, s3⟩, fun j hj => ?_⟩
  have hprod : |v.sc * m j| ≤ 2 ^ 16 * |m j| := by
    rw [abs_mul, abs_of_nonneg s2]
    exact mul_le_mul_of_nonneg_right s3 (abs_nonneg _)
  have hprod' : |v.sc * m j| ≤ 2 ^ 16 * Mb :=
    le_trans hprod (mul_le_mul_of_nonneg_left (hm j hj) (by norm_num))
  have e : v.xr j = rhu (v.sc * m j) 16 := site_low hprod' (sm.xr j hj) adm.xr (h.XR j hj).r16
  refine ⟨e, ?_⟩
  have hp := abs_le.mp hprod
  rw [e]
  unfold rhu
  rw [abs_le]
  constructor <;> omega

end Sound

/-- At the reference sizes the size conditions hold for all shifts from 8 to 24: p = 2^61 − 1, c =
2^18, 128 experts, accumulators at most 5,120 · 2,047 · 2^12, quotients ly at most 20,961,281,
inputs at most 2,047.
Below 8 the quotient ly may exceed the radix 2^25 of the key CLR: the implementation refuses such a
shift too (guard-radix-clamp; by a reading of a protocol text of the implementation, which is
not in this repository; no Lean statement of this file is about the implementation). -/
theorem adm_ref {kr : ℕ} (h8 : 8 ≤ kr) (h24 : kr ≤ 24) :
    Adm (2 ^ 61 - 1) (2 ^ 18) (257 * 2 ^ 18) (65793 * 2 ^ 18) (5120 * 2047 * 2 ^ 12)
      20961280 2047 kr 128 := by
  have a1 := scaled_le (top := 24) (by norm_num) h24 (5120 * 2047 * 2 ^ 12)
    (Qb := 8 * (257 * 2 ^ 18) + 7) (by norm_num)
  have a2 := two_pow_dn_le kr
  have a3 : (2 : ℤ) ^ 7 ≤ 2 ^ (kr - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have a4 : (2 : ℤ) ^ kr = 2 * 2 ^ (kr - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨h24, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · linarith
  · rw [a4]
    linarith

/-! ## 4. The honest values -/

/-- The honest values of the router: those of the model's steps (R1) to (R6) on the accumulators
Ar and the input m, and the high digits of the remainders. -/
def hon (tb : Tables) (kr nx : ℕ) (m Ar : ℕ → ℤ) : RouterV :=
  let lw : ℕ → ℤ := fun e => rhu (Ar e) kr
  let l3 : ℕ → ℤ := fun e => lw e % 8
  let ly : ℕ → ℤ := fun e => (lw e - l3 e) / 8
  let lr : ℕ → ℤ := fun e => 8 * clamp 2047 (ly e) + l3 e
  let es : ℕ := argTo lr (nx - 1)
  let sc : ℤ := tb.SIGM (lr es + 2 ^ 15)
  { ly := ly, l3 := l3, lr := lr, sel := fun e => if e = es then 1 else 0,
    rl := fun e => hd (Ar e) kr, sc := sc, xr := fun j => rhu (sc * m j) 16 }

section Honest
variable (tb : Tables) (kr nx : ℕ) (m Ar : ℕ → ℤ)

/-- the expert that the honest router selects -/
def honEs : ℕ := argTo (hon tb kr nx m Ar).lr (nx - 1)

theorem hon_lw (e : ℕ) : (hon tb kr nx m Ar).lw e = rhu (Ar e) kr := by
  show 8 * ((rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8) + rhu (Ar e) kr % 8 = _
  omega

theorem hon_lr_range (e : ℕ) :
    -2 ^ 14 ≤ (hon tb kr nx m Ar).lr e ∧ (hon tb kr nx m Ar).lr e < 2 ^ 14 := by
  show -2 ^ 14 ≤ 8 * clamp 2047 ((rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8) + rhu (Ar e) kr % 8 ∧
    8 * clamp 2047 ((rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8) + rhu (Ar e) kr % 8 < 2 ^ 14
  have := clamp_bounds (c := 2047) (by norm_num) ((rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8)
  omega

variable {nx}

theorem honEs_lt (hnx : 0 < nx) : honEs tb kr nx m Ar < nx := by
  have := (argTo_spec' (hon tb kr nx m Ar).lr (nx - 1)).1
  unfold honEs
  omega

theorem hon_sel (e : ℕ) :
    (hon tb kr nx m Ar).sel e = if e = honEs tb kr nx m Ar then 1 else 0 := rfl

theorem hon_mr (hnx : 0 < nx) :
    (hon tb kr nx m Ar).mr nx = (hon tb kr nx m Ar).lr (honEs tb kr nx m Ar) :=
  sum_indicator_mul (honEs_lt tb kr m Ar hnx) (fun e _ => hon_sel tb kr m Ar e) _

theorem hon_sc :
    (hon tb kr nx m Ar).sc = tb.SIGM ((hon tb kr nx m Ar).lr (honEs tb kr nx m Ar) + 2 ^ 15) := rfl

variable {tb kr m Ar}

/-- For 0 < nx, kr ≤ 24, every honest key is an entry of its table, over the integers, and (J10)
holds, if the range condition of (R2) does not fail. -/
theorem hon_keys (hnx : 0 < nx) (hk' : kr ≤ 24) (ok : ∀ e < nx, Fits16 ((hon tb kr nx m Ar).ly e)) :
    (∀ e < nx,
      InLutZ R16 (keyLR (hon tb kr nx m Ar) kr Ar e) ∧
      InLutZ R8 (keyLH (hon tb kr nx m Ar) kr e) ∧
      InLutZ R8 (keyL3 (hon tb kr nx m Ar) e) ∧
      InLutZ FC (keyCLR (hon tb kr nx m Ar) e) ∧
      InLutZ R16 (keyLT (hon tb kr nx m Ar) e) ∧
      InLutZ R8 (keySEL (hon tb kr nx m Ar) e) ∧
      InLutZ R16 (keyDD (hon tb kr nx m Ar) nx e)) ∧
    InLutZ (FS tb) (keyMR (hon tb kr nx m Ar) nx) ∧
    (∀ j, InLutZ R16 (keyXR (hon tb kr nx m Ar) m j)) ∧
    idnJ10 (hon tb kr nx m Ar) nx = 0 := by
  have hes := honEs_lt tb kr m Ar hnx
  have hsel : ∀ e < nx, (hon tb kr nx m Ar).sel e =
    if e = honEs tb kr nx m Ar then 1 else 0 := fun e _ => hon_sel tb kr m Ar e
  have hmr := hon_mr tb kr m Ar hnx
  obtain ⟨_, a2, a3⟩ := argTo_spec' (hon tb kr nx m Ar).lr (nx - 1)
  refine ⟨fun e he => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun j => ?_, ?_⟩
  · have h := ssite_hon (Ar e) kr
    have e1 : keyLR (hon tb kr nx m Ar) kr Ar e =
        ssite (Ar e) (rhu (Ar e) kr) (hd (Ar e) kr) kr := by
      unfold keyLR
      rw [hon_lw]
      rfl
    rw [e1]
    exact inLutZ_r16 h.2.1 h.2.2
  · have h := shigh_hon (Ar e) (w := 8) rfl hk'
    exact inLutZ_r8 h.1 h.2
  · refine inLutZ_r8 ?_ ?_
    · show 0 ≤ 32 * (rhu (Ar e) kr % 8)
      omega
    · show 32 * (rhu (Ar e) kr % 8) < 2 ^ 8
      omega
  · exact clr_hon (ok e he)
  · have := hon_lr_range tb kr nx m Ar e
    refine inLutZ_r16 ?_ ?_ <;> unfold keyLT <;> omega
  · refine inLutZ_r8 ?_ ?_ <;> unfold keySEL <;> rw [hon_sel] <;> split <;> norm_num
  · have h1 := hon_lr_range tb kr nx m Ar e
    have h2 := hon_lr_range tb kr nx m Ar (honEs tb kr nx m Ar)
    have h3 : (hon tb kr nx m Ar).lr e ≤ (hon tb kr nx m Ar).lr (honEs tb kr nx m Ar) :=
      a2 e (by omega)
    have e1 : keyDD (hon tb kr nx m Ar) nx e =
        (hon tb kr nx m Ar).lr (honEs tb kr nx m Ar) - (hon tb kr nx m Ar).lr e -
          if e < honEs tb kr nx m Ar then 1 else 0 := by
      unfold keyDD
      rw [hmr, sum_indicator_after hes hsel]
    rw [e1]
    by_cases hlt : e < honEs tb kr nx m Ar
    · have h4 : (hon tb kr nx m Ar).lr e < (hon tb kr nx m Ar).lr (honEs tb kr nx m Ar) := a3 e hlt
      rw [if_pos hlt]
      exact inLutZ_r16 (by omega) (by omega)
    · rw [if_neg hlt]
      exact inLutZ_r16 (by omega) (by omega)
  · have h2 := hon_lr_range tb kr nx m Ar (honEs tb kr nx m Ar)
    unfold keyMR
    rw [hmr, hon_sc]
    exact mr_hon tb h2.1 h2.2
  · have h := rem_bounds ((hon tb kr nx m Ar).sc * m j) 16
    have e1 : keyXR (hon tb kr nx m Ar) m j = rem ((hon tb kr nx m Ar).sc * m j) 16 := by
      unfold keyXR rem
      norm_num
      rfl
    rw [e1]
    exact inLutZ_r16 h.1 h.2
  · unfold idnJ10
    rw [sum_indicator hes hsel]
    norm_num

/-- The ranges of the honest values, under (Tab4). -/
theorem hon_ranges
    (hS : ∀ ι < 2 ^ 15, 0 ≤ tb.SIGM ((ι : ℕ) + 2 ^ 14) ∧ tb.SIGM ((ι : ℕ) + 2 ^ 14) ≤ 2 ^ 16) :
    (∀ e, 0 ≤ (hon tb kr nx m Ar).l3 e ∧ (hon tb kr nx m Ar).l3 e ≤ 7) ∧
    (∀ e, -16376 ≤ (hon tb kr nx m Ar).lr e ∧ (hon tb kr nx m Ar).lr e ≤ 16383) ∧
    (∀ e, (hon tb kr nx m Ar).sel e = 0 ∨ (hon tb kr nx m Ar).sel e = 1) ∧
    (∀ e, 0 ≤ (hon tb kr nx m Ar).rl e ∧ (hon tb kr nx m Ar).rl e < 2 ^ (up kr - 16)) ∧
    (0 ≤ (hon tb kr nx m Ar).sc ∧ (hon tb kr nx m Ar).sc ≤ 2 ^ 16) ∧
    ∀ j, |(hon tb kr nx m Ar).xr j| ≤ |m j| := by
  have hsc : 0 ≤ (hon tb kr nx m Ar).sc ∧ (hon tb kr nx m Ar).sc ≤ 2 ^ 16 := by
    have h2 := hon_lr_range tb kr nx m Ar (honEs tb kr nx m Ar)
    have h := hS ((hon tb kr nx m Ar).lr (honEs tb kr nx m Ar) + 2 ^ 14).toNat (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at h
    have e : (hon tb kr nx m Ar).lr (honEs tb kr nx m Ar) + 2 ^ 14 + 2 ^ 14 =
        (hon tb kr nx m Ar).lr (honEs tb kr nx m Ar) + 2 ^ 15 := by ring
    rw [e] at h
    exact h
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => hd_bounds_up _ _, hsc, fun j => ?_⟩
  · show 0 ≤ rhu (Ar e) kr % 8 ∧ rhu (Ar e) kr % 8 ≤ 7
    omega
  · show -16376 ≤ 8 * clamp 2047 ((rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8) + rhu (Ar e) kr % 8 ∧
      8 * clamp 2047 ((rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8) + rhu (Ar e) kr % 8 ≤ 16383
    have := clamp_bounds (c := 2047) (by norm_num) ((rhu (Ar e) kr - rhu (Ar e) kr % 8) / 8)
    omega
  · rw [hon_sel]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · have hprod : |(hon tb kr nx m Ar).sc * m j| ≤ 2 ^ 16 * |m j| := by
      rw [abs_mul, abs_of_nonneg hsc.1]
      exact mul_le_mul_of_nonneg_right hsc.2 (abs_nonneg _)
    have hp := abs_le.mp hprod
    show |rhu ((hon tb kr nx m Ar).sc * m j) 16| ≤ _
    unfold rhu
    rw [abs_le]
    constructor <;> omega

end Honest

end Inst.Model.Router

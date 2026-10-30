-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/HonestCells.lean: the honest trace (`hon`, Inst/Model/FF/Trace.lean) of a
  feed-forward segment, part 3: under `Par`, `Unit.TabOK`, `Runs`, every valid cell has absolute
  value at most 128.

  The widened cell rule of Inst/Model/Widened.lean: for n ≥ 1, n cells can hold a value a exactly if
  −128 u_n ≤ a ≤ 127 u_(n−1) + 128 · 256^(n−1) (u_n = Σ_(l<n) 256^l: `un`). So a quotient that fits
  16 bits is held by two cells, also between 32,640 and 32,767, where the top cell is 128.
    `wr_hon`       the honest value of every array, minus its offset, can be held by the cells of
                   the array (`Writable`), at every instance, channel and position of the array
    `abs_hon_le`   every valid cell of the honest trace is at most 128 in absolute value
  Both are for arbitrary sizes, under `Par`, `Unit.TabOK` and `Runs`.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.

  Notation: `D`: a `Dim`: the sizes of a feed-forward segment; g0, gc, sl, ..: the arrays (`Arr`)
  (Inst/Model/FF/Index.lean); `tb`: `Tables`: the five table functions that the program reads;
  `w l`: a `LayerW`: the weight matrices of one layer; `clamp c a`: min(max(a, −c), c)
  (Inst/Model/Program.lean); `L0`: a natural number: the first layer of the segment; `x`, `o`:
  ℕ → ℕ → `Vec`: in `hv`: x s is state s of the stream in the segment, o ℓ the output of attention
  in layer ℓ; H, HV: `hon D tb w L0 x o`, `hv D tb w L0 x o`: the honest trace, the honest value of
  every array (Inst/Model/FF/Trace.lean); `cellW n a l`: the widened cell rule: cell l of the value
  a in an array of n cells: balanced low bytes, and the rest in the top cell; `Writable n a`: every
  cell has absolute value at most 128 (Inst/Model/Widened.lean); `hd A k`: ⌊rem(A, k) / 2^16⌋, the
  high digit; `Site.up k`: max(k, 16) (Inst/Model/Common/Site.lean).
-/
import Inst.Model.FF.HonestKeys

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg.Hon

variable [scl : Scl]

open Finset
open Inst.Model.Site (hd hd_bounds_up)
open Inst.Model.TableKeys (clamp_bounds)

variable {D : Dim} {tb : Tables} {w : ℕ → LayerW} {L0 : ℕ} {x o : ℕ → ℕ → Vec}

local notation "H" => hon D tb w L0 x o
local notation "HV" => hv D tb w L0 x o

omit scl in
/-- one cell -/
theorem wr1 {a : ℤ} (h0 : -128 ≤ a) (h1 : a ≤ 128) : Writable 1 a :=
  writable_of_abs_le a (abs_le.2 ⟨by norm_num; exact h0, by norm_num; exact h1⟩)

omit scl in
/-- two cells -/
theorem wr2 {a : ℤ} (h0 : -32768 ≤ a) (h1 : a ≤ 32768) : Writable 2 a :=
  writable_of_abs_le a (abs_le.2 ⟨by norm_num; exact h0, by norm_num; exact h1⟩)

omit scl in
/-- One cell can hold a high digit below 2^8 (shift k ≤ 24), with the offset 128. -/
theorem wr_hd8 (A : ℤ) {k : ℕ} (hk : k ≤ 24) : Writable 1 (hd A k - 128) := by
  obtain ⟨h0, h1⟩ := hd_bounds_up A k
  have h2 : (2 : ℤ) ^ (Site.up k - 16) ≤ 2 ^ 8 :=
    pow_le_pow_right₀ (by norm_num) (by have := Site.up_le (top := 24) (by norm_num) hk; omega)
  exact wr1 (by linarith) (by norm_num at h2; linarith)

omit scl in
/-- Two cells can hold a high digit below 2^16 (shift k ≤ 32), with the offset 32,896 = 128 · 257.
-/
theorem wr_hd16 (A : ℤ) {k : ℕ} (hk : k ≤ 32) : Writable 2 (hd A k - 32896) := by
  obtain ⟨h0, h1⟩ := hd_bounds_up A k
  have h2 : (2 : ℤ) ^ (Site.up k - 16) ≤ 2 ^ 16 :=
    pow_le_pow_right₀ (by norm_num) (by have := Site.up_le (top := 32) (by norm_num) hk; omega)
  rw [writable_iff (by norm_num)]
  have e2 : un 2 = 257 := by simp [un, sum_range_succ]
  have e1 : un (2 - 1) = 1 := by simp [un]
  rw [e2, e1]
  norm_num at h2 ⊢
  constructor <;> linarith

omit scl in
theorem wr_clamp (a : ℤ) : Writable 2 (clamp 2047 a) := by
  have h := clamp_bounds (c := 2047) (by norm_num) a
  exact wr2 (by linarith [h.1]) (by linarith [h.2])

section Cells

variable (hp : Par D L0) (tab : Unit.TabOK tb) (R : Runs D tb w L0 x o)
include hp tab R

/-- Under `Par`, `Unit.TabOK` and `Runs`, the honest value of every array, at every instance,
channel and position of the array (`hn`, `hj`, `hi`), minus its offset, can be held by the cells of
the array. -/
theorem wr_hon (X : Arr) {n j i : ℕ} (hn : n < X.cnt D) (hj : j < X.width D) (hi : i < D.T) :
    Writable X.nCell (HV X n j i - X.off) := by
  have hi' : i < D.P.T := lt_of_lt_of_le hi hp.T
  have UR := fun (hn' : n < D.nl) (hj' : j < D.f) =>
    Unit.hon_ranges tab (unit_ok hp R hn' hj' hi)
  have RR := Router.hon_ranges (tb := tb) (kr := (D.Pl (2 * n + 1)).kr) (nx := D.nx)
    (m := FF.m (D.Pl (2 * n + 1)) (x (4 * n + 3)) i)
    (Ar := fun e =>
        dot D.d (FF.m (D.Pl (2 * n + 1)) (x (4 * n + 3)) i) fun t => (w (2 * n + 1)).Wr t e)
    tab.sigm
  cases X with
  | g0 =>
    rw [show HV .g0 n j i - Arr.off .g0 = HV .g0 n j i from sub_zero _]
    have h := (UR hn hj).1
    exact wr1 h.1 (h.2.trans (by norm_num))
  | gc =>
    rw [show HV .gc n j i - Arr.off .gc = HV .gc n j i from sub_zero _]
    have h := (UR hn hj).2.2.1
    exact wr1 (le_trans (by norm_num) h.1) (h.2.trans (by norm_num))
  | sl =>
    rw [show HV .sl n j i - Arr.off .sl = HV .sl n j i from sub_zero _]
    have h := (UR hn hj).2.2.2.1
    exact wr2 (le_trans (by norm_num) h.1) (h.2.trans (by norm_num))
  | up =>
    rw [show HV .up n j i - Arr.off .up = HV .up n j i from sub_zero _]
    exact writable_two_of_fits16 (UR hn hj).2.2.2.2.1
  | gh =>
    rw [show HV .gh n j i - Arr.off .gh = HV .gh n j i from sub_zero _]
    have h := (UR hn hj).2.1
    exact wr2 (le_trans (by norm_num) h.1) (h.2.le.trans (by norm_num))
  | rg => exact wr_hd8 _ (hp.kG _ (L0 + n) j)
  | ru => exact wr_hd8 _ (hp.kU _ (L0 + n) j)
  | ro => exact wr_hd8 _ (hp.ko _)
  | rd => exact wr_hd8 _ (hp.kd _)
  | rv => exact wr_hd8 _ (hp.kv _)
  | rl => exact wr_hd8 _ (hp.kr _)
  | ra => exact wr_hd16 _ (hp.n1 n).2.2.2.2.2.1
  | rm => exact wr_hd16 _ (hp.n2 n).2.2.2.2.2.1
  | rqk => exact wr_hd16 _ (hp.kQK _ j)
  | xs =>
    rw [show HV .xs n j i - Arr.off .xs = HV .xs n j i from sub_zero _]
    have hn' : n < 2 * D.nl - 1 := hn
    exact R.wr (n + 1) (by omega) i hi j hj
  | x0 =>
    rw [show HV .x0 n j i - Arr.off .x0 = HV .x0 n j i from sub_zero _]
    exact R.wr 0 (Nat.zero_le _) i hi j hj
  | x8 =>
    rw [show HV .x8 n j i - Arr.off .x8 = HV .x8 n j i from sub_zero _]
    exact R.wr (2 * D.nl) le_rfl i hi j hj
  | aw =>
    rw [show HV .aw n j i - Arr.off .aw = HV .aw n j i from sub_zero _]
    exact writable_two_of_fits16 ((R.att n hn i hi').1.2 j hj)
  | mw =>
    rw [show HV .mw n j i - Arr.off .mw = HV .mw n j i from sub_zero _]
    exact writable_two_of_fits16 ((R.ff n hn i hi').1.2 j hj)
  | qkw =>
    rw [show HV .qkw n j i - Arr.off .qkw = HV .qkw n j i from sub_zero _]
    exact writable_two_of_fits16 ((R.att n hn i hi').2.1 j hj)
  | vw =>
    rw [show HV .vw n j i - Arr.off .vw = HV .vw n j i from sub_zero _]
    exact writable_two_of_fits16 ((R.att n hn i hi').2.2 j hj)
  | a =>
    rw [show HV .a n j i - Arr.off .a = HV .a n j i from sub_zero _]
    exact wr_clamp _
  | m =>
    rw [show HV .m n j i - Arr.off .m = HV .m n j i from sub_zero _]
    exact wr_clamp _
  | q =>
    rw [show HV .q n j i - Arr.off .q = HV .q n j i from sub_zero _]
    exact wr_clamp _
  | kx =>
    rw [show HV .kx n j i - Arr.off .kx = HV .kx n j i from sub_zero _]
    exact wr_clamp _
  | v =>
    rw [show HV .v n j i - Arr.off .v = HV .v n j i from sub_zero _]
    exact wr_clamp _
  | o =>
    rw [show HV .o n j i - Arr.off .o = HV .o n j i from sub_zero _]
    have h := abs_le.1 (R.o n hn i hi j hj)
    exact wr2 (le_trans (by norm_num) h.1) (h.2.trans (by norm_num))
  | xr =>
    rw [show HV .xr n j i - Arr.off .xr = HV .xr n j i from sub_zero _]
    have h1 := RR.2.2.2.2.2 j
    have h2 := clamp_bounds (c := 2047) (by norm_num)
      (NORM.yw (D.Pl (2 * n + 1)).n2 D.P.d (x (4 * n + 3) i) j)
    have h3 : |FF.m (D.Pl (2 * n + 1)) (x (4 * n + 3)) i j| ≤ 2047 := abs_le.2 h2
    have h4 := abs_le.1 (h1.trans h3)
    exact wr2 (le_trans (by norm_num) h4.1) (h4.2.trans (by norm_num))
  | lr =>
    rw [show HV .lr n j i - Arr.off .lr = HV .lr n j i from sub_zero _]
    have h := RR.2.1 j
    exact wr2 (le_trans (by norm_num) h.1) (h.2.trans (by norm_num))
  | sel =>
    rw [show HV .sel n j i - Arr.off .sel = HV .sel n j i from sub_zero _]
    rcases RR.2.2.1 j with e | e
    · rw [show HV .sel n j i = 0 from e]
      exact wr1 (by norm_num) (by norm_num)
    · rw [show HV .sel n j i = 1 from e]
      exact wr1 (by norm_num) (by norm_num)
  | sc =>
    rw [show HV .sc n j i - Arr.off .sc = HV .sc n j i from sub_zero _]
    have h := RR.2.2.2.2.1
    exact writable_of_abs_le (n := 3) _
      (abs_le.2 ⟨le_trans (by norm_num) h.1, h.2.trans (by norm_num)⟩)
  | D =>
    have hn' : n < 2 * D.nl := hn
    have h := Ledger.hon_cell (honHyp hp R hn' hi) (n := j) hj
    exact wr1 h.1 (h.2.trans (by norm_num))
  | ly =>
    rw [show HV .ly n j i - Arr.off .ly = HV .ly n j i from sub_zero _]
    have hn' : n < D.nl / 2 := hn
    have hl : 2 * n + 1 < D.nl := by omega
    have he : hasExperts (L0 + (2 * n + 1)) := by
      have := hp.even
      unfold hasExperts
      omega
    have h := (R.ff (2 * n + 1) hl i hi').2.1 he j hj
    rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by ring] at h
    exact writable_two_of_fits16 h
  | l3 =>
    rw [show HV .l3 n j i - Arr.off .l3 = HV .l3 n j i from sub_zero _]
    have h := RR.1 j
    exact wr1 (le_trans (by norm_num) h.1) (h.2.trans (by norm_num))

/-- Under the same hypotheses, every valid cell of the honest trace is at most 128 in absolute
value. -/
theorem abs_hon_le (c : Cell) (hc : c.Valid D) : |H c| ≤ 128 :=
  wr_hon hp tab R c.X hc.2.1 hc.2.2.1 hc.2.2.2 c.k hc.1

end Cells

end Inst.Model.FFSeg.Hon

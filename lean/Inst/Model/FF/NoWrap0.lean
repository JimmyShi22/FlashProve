-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/NoWrap0.lean: from the field relation of a feed-forward segment to the integers:
  shared definitions and lemmas.

    `IntRel`             the field relation over `ZMod p`, restated over the integers: small cells;
                         every integer looked-up value (key in Lean names) is congruent modulo p to
                         an entry of its table; every integer identity is congruent to 0
    `intRel_of_rfraw`, `intRel_of_rf`
                         `IntRel` from `RFraw` (Inst/Model/FF/Cast.lean) and from the relation of
                         `trace`, over `ZMod p`
    `abs_val_sub_le`     the bound on a value minus its offset; `val1`, `val2`: the cases of one and
                         of two cells; `val1z`, `val2z`: without offset
    `ofInt_*`            the integer weights, mapped into the integers, are unchanged
    `clamp_site`         a lemma on numbers: under the hypotheses of its statement, the low key, the
                         high key and the key of the clamp force yw = rhu(A, k), "yw fits 16 bits",
                         y = clamp_2047(yw), and the high digit; `clamp_ssite`: the same for every
                         shift k ≤ top
    `abs_dot_le`         a bound on an accumulator Σ_j a[j] b[j]
  `IntRel` after Inst/Model/Att/NoWrap0.lean.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.

  Notation: no wrap-around (the file's name): see the head of Inst/Model/FF/NoWrap.lean; `D`: a
  `Dim`: the sizes of a feed-forward segment; `s` (in `IntRel`): a `Fam`: the families of keys
  (Inst/Model/FF/Index.lean); `tb`: `Tables`: the five table functions that the program reads;
  `w l`: a `LayerW`: the weight matrices of one layer; `rhu a k`: ⌊(a + 2^(k−1)) / 2^k⌋, k ≥ 1;
  `clamp c a`: min(max(a, −c), c) (Inst/Model/Program.lean); `L0`: a natural number: the first layer
  of the segment; `first`: a Bool: `Idn.j11` is valid only if it is true (`Idn.Valid`: "(J11) to the
  first segment only"); `emb`, `tok`: the embedding, the prompt; `t`: a map `Cell` → ℤ: a trace, a
  function on the names of cells; `key D t tb L0 w s l x i`: the key of the family s at (ℓ, x, i);
  `val t X inst j i`: the read-out formula, at an array, an instance, a channel j and a position i
  (Inst/Model/FF/Trace.lean); `site`, `high` (for every shift: `ssite`, `shigh`): the low and the
  high key of a rounding; `hd A k`: ⌊rem(A, k) / 2^16⌋, the high digit
  (Inst/Model/Common/Site.lean).
-/
import Inst.Model.FF.Cast

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset
open Inst.Model.TableKeys (InLut)

/-- The field relation over `ZMod p`, restated over the integers. -/
structure IntRel (D : Dim) (tb : Tables) (L0 : ℕ) (first : Bool) (p : ℤ) (w : ℕ → LayerW)
    (emb : Mat) (tok : ℕ → ℕ) (t : Cell → ℤ) : Prop where
  small : ∀ c : Cell, c.Valid D → |t c| < 2 ^ 18
  key : ∀ (s : Fam) (l x i : ℕ), l < D.nl → present s l = true → x < len D s → i < D.T →
    InLut p (lut tb (call s)) (key D t tb L0 (fun l => LW.ofInt ℤ (w l)) s l x i)
  idn : ∀ j : Idn, j.Valid D first → idnVal D t emb tok j ≡ 0 [ZMOD p]

theorem intRel_of_rfraw {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {w : ℕ → LayerW} {emb : Mat}
    {tok : ℕ → ℕ} {t : Cell → ℤ} (p : ℕ) (h : RFraw D tb L0 first (ZMod p) w emb tok t) :
    IntRel D tb L0 first (p : ℤ) w emb tok t :=
  ⟨h.1, fun _ _ _ _ hl hs hx hi => key_inLut D tb L0 first w emb tok t p h hl hs hx hi,
    fun _ hj => idn_modEq D tb L0 first w emb tok t p h hj⟩

theorem intRel_of_rf {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {kW : ℕ} {tok : ℕ → ℕ}
    {W : Mat} {s : {c : Cell // c.Valid D} → ℤ} (p : ℕ)
    (h : (trace D tb kW L0 first (ZMod p)).RF tok (fun y c => ((W y c : ℤ) : ZMod p)) s) :
    IntRel D tb L0 first (p : ℤ) (fun l => Layout.layerOf D.P kW W (L0 + l))
      (Layout.weightsOf D.P kW W).Emb tok (rd D s) :=
  intRel_of_rfraw p ((rf_iff D tb L0 first kW (ZMod p) tok W s).1 h)

/-! ## Bounds on values -/

section Values
variable {D : Dim} {t : Cell → ℤ} (small : ∀ c : Cell, c.Valid D → |t c| < 2 ^ 18)
include small

omit scl in
/-- If every valid cell is below 2^18 in absolute value, a value of n cells at valid indices differs
from its offset by at most (1 + 256 + .. + 256^(n − 1)) 2^18. -/
theorem abs_val_sub_le (X : Arr) {a j i : ℕ} (ha : a < X.cnt D)
    (hj : j < X.width D) (hi : i < D.T) :
    |val t X a j i - X.off| ≤ (∑ k ∈ range X.nCell, 256 ^ k) * 2 ^ 18 := by
  have e : val t X a j i - X.off = ∑ k ∈ range X.nCell, 256 ^ k * t ⟨X, k, a, j, i⟩ := by
    unfold val
    simp
  rw [e, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 256 ^ k)]
  exact mul_le_mul_of_nonneg_left
    (small ⟨X, k, a, j, i⟩ ⟨mem_range.1 hk, ha, hj, hi⟩).le (by positivity)

omit scl in
theorem val1 (X : Arr) (hn : X.nCell = 1) {a j i : ℕ} (ha : a < X.cnt D)
    (hj : j < X.width D) (hi : i < D.T) :
    |val t X a j i - X.off| ≤ 2 ^ 18 := by
  have h := abs_val_sub_le small X ha hj hi
  rw [hn] at h
  norm_num [sum_range_succ] at h
  linarith

omit scl in
theorem val2 (X : Arr) (hn : X.nCell = 2) {a j i : ℕ} (ha : a < X.cnt D)
    (hj : j < X.width D) (hi : i < D.T) :
    |val t X a j i - X.off| ≤ 257 * 2 ^ 18 := by
  have h := abs_val_sub_le small X ha hj hi
  rw [hn] at h
  norm_num [sum_range_succ] at h
  linarith

omit scl in
/-- the bound for an array of one cell without offset -/
theorem val1z (X : Arr) (hn : X.nCell = 1) (ho : X.off = 0) {a j i : ℕ} (ha : a < X.cnt D)
    (hj : j < X.width D) (hi : i < D.T) : |val t X a j i| ≤ 2 ^ 18 := by
  have h := val1 small X hn ha hj hi
  rwa [ho, sub_zero] at h

omit scl in
theorem val2z (X : Arr) (hn : X.nCell = 2) (ho : X.off = 0) {a j i : ℕ} (ha : a < X.cnt D)
    (hj : j < X.width D) (hi : i < D.T) :
    |val t X a j i| ≤ 257 * 2 ^ 18 := by
  have h := val2 small X hn ha hj hi
  rwa [ho, sub_zero] at h

end Values

/-! ## The integer weights, mapped into the integers -/

section Weights
variable (w : LayerW)
omit scl in
@[simp] theorem ofInt_Wq (j x : ℕ) : (LW.ofInt ℤ w).Wq j x = w.Wq j x := rfl
omit scl in
@[simp] theorem ofInt_Wk (j x : ℕ) : (LW.ofInt ℤ w).Wk j x = w.Wk j x := rfl
omit scl in
@[simp] theorem ofInt_Wv (j x : ℕ) : (LW.ofInt ℤ w).Wv j x = w.Wv j x := rfl
omit scl in
@[simp] theorem ofInt_Wo (j x : ℕ) : (LW.ofInt ℤ w).Wo j x = w.Wo j x := rfl
omit scl in
@[simp] theorem ofInt_Wg (j x : ℕ) : (LW.ofInt ℤ w).Wg j x = w.Wg j x := rfl
omit scl in
@[simp] theorem ofInt_Wu (j x : ℕ) : (LW.ofInt ℤ w).Wu j x = w.Wu j x := rfl
omit scl in
@[simp] theorem ofInt_Wd (j x : ℕ) : (LW.ofInt ℤ w).Wd j x = w.Wd j x := rfl
omit scl in
@[simp] theorem ofInt_Wr (j x : ℕ) : (LW.ofInt ℤ w).Wr j x = w.Wr j x := rfl
omit scl in
@[simp] theorem ofInt_Eg (e j x : ℕ) : (LW.ofInt ℤ w).Eg e j x = w.Eg e j x := rfl
omit scl in
@[simp] theorem ofInt_Eu (e j x : ℕ) : (LW.ofInt ℤ w).Eu e j x = w.Eu e j x := rfl
omit scl in
@[simp] theorem ofInt_Ed (e j x : ℕ) : (LW.ofInt ℤ w).Ed e j x = w.Ed e j x := rfl
end Weights

/-! ## Lemmas on numbers, for a single index -/

omit scl in
/-- A rounding with a high digit, followed by a clamp: the pattern of (N4) with (N5) and of (PL5).
top = 16 + w, where the table of the high key has 2^w rows; Ab, B2, Rb bound the accumulator, a
value of two cells and the high digit. -/
theorem clamp_site {p : ℤ} {k top w : ℕ} (htop : top = 16 + w) (hk16 : 16 ≤ k) (hk : k ≤ top)
    {A yw y rh Ab B2 Rb : ℤ} (hA : |A| ≤ Ab) (hyw : |yw| ≤ B2) (hy : |y| ≤ B2) (hR : |rh| ≤ Rb)
    (hpC : (B2 + 2 ^ 15) + 2 ^ 28 * (B2 + 2 ^ 11) + 2 ^ 41 ≤ p)
    (guard : B2 + 2 ^ 15 + 2 ^ 16 < 2 ^ 28) (hpH : 2 ^ (top - k) * Rb + 2 ^ w ≤ p)
    (hpL : Ab + 2 ^ (k - 1) + 2 ^ k * 2 ^ 15 + 2 ^ 16 * Rb + 2 ^ 16 ≤ p)
    (kL : InLut p R16 (Site.site A yw rh k))
    (kH : ∃ u : ℤ, 0 ≤ u ∧ u < 2 ^ w ∧ Site.high rh k top ≡ u [ZMOD p])
    (kC : InLut p FC ((yw + 2 ^ 15) + 2 ^ 28 * (y + 2 ^ 11))) :
    yw = rhu A k ∧ Fits16 yw ∧ y = clamp 2047 yw ∧ rh = Site.hd A k := by
  obtain ⟨f1, f2⟩ := TableKeys.fc_key hyw hy hpC guard kC
  have hq : |yw| ≤ 2 ^ 15 := by
    unfold Fits16 at f1
    rw [abs_le]
    omega
  obtain ⟨r0, r1⟩ := Site.high_sound htop hk16 hk hR hpH kH
  obtain ⟨s1, s2, s3⟩ := Site.site_sound hk16 hA hq hR r0 r1 hpL kL.r16
  refine ⟨s1, f1, f2, ?_⟩
  rw [s1] at s2 s3
  exact Site.hd_unique s2 s3

omit scl in
/-- The same for every shift k ≤ top (Inst/Model/Common/Site.lean, Sections 5 to 8): the pattern of
(PL5) with the keys `ssite` and `shigh`. (not all hypotheses are named here: see the statement
below) -/
theorem clamp_ssite {p : ℤ} {k top w : ℕ} (htop : top = 16 + w) (hk : k ≤ top)
    {A yw y rh Ab B2 Rb : ℤ} (hA : |A| ≤ Ab) (hyw : |yw| ≤ B2) (hy : |y| ≤ B2) (hR : |rh| ≤ Rb)
    (hpC : (B2 + 2 ^ 15) + 2 ^ 28 * (B2 + 2 ^ 11) + 2 ^ 41 ≤ p)
    (guard : B2 + 2 ^ 15 + 2 ^ 16 < 2 ^ 28) (hpH : 2 ^ (top - Site.up k) * Rb + 2 ^ w ≤ p)
    (hpL : 2 ^ Site.dn k * (Ab + 2 ^ (k - 1) + 2 ^ k * 2 ^ 15) + 2 ^ 16 * Rb + 2 ^ 16 ≤ p)
    (kL : InLut p R16 (Site.ssite A yw rh k))
    (kH : ∃ u : ℤ, 0 ≤ u ∧ u < 2 ^ w ∧ Site.shigh rh k top ≡ u [ZMOD p])
    (kC : InLut p FC ((yw + 2 ^ 15) + 2 ^ 28 * (y + 2 ^ 11))) :
    yw = rhu A k ∧ Fits16 yw ∧ y = clamp 2047 yw ∧ rh = Site.hd A k := by
  obtain ⟨f1, f2⟩ := TableKeys.fc_key hyw hy hpC guard kC
  have hq : |yw| ≤ 2 ^ 15 := by
    unfold Fits16 at f1
    rw [abs_le]
    omega
  obtain ⟨r0, r1⟩ := Site.shigh_sound htop hk hR hpH kH
  obtain ⟨s1, s2, s3⟩ := Site.ssite_sound hA hq hR r0 r1 hpL kL.r16
  refine ⟨s1, f1, f2, ?_⟩
  rw [s1] at s2 s3
  exact Site.hd_unique_s s2 s3

omit scl in
/-- a bound on an accumulator -/
theorem abs_dot_le {n : ℕ} {a b : Vec} {Ba Bb : ℤ}
    (ha : ∀ j < n, |a j| ≤ Ba) (hb : ∀ j < n, |b j| ≤ Bb) :
    |dot n a b| ≤ n * (Ba * Bb) := by
  unfold dot
  calc |∑ j ∈ range n, a j * b j| ≤ ∑ j ∈ range n, |a j * b j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range n, Ba * Bb := sum_le_sum fun j hj => by
        rw [abs_mul]
        exact mul_le_mul (ha j (mem_range.1 hj)) (hb j (mem_range.1 hj)) (abs_nonneg _)
          (le_trans (abs_nonneg _) (ha j (mem_range.1 hj)))
    _ = n * (Ba * Bb) := by simp

end Inst.Model.FFSeg

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/NoWrapProj.lean: the projections of a layer: from the field relation to the steps
  (PL3) to (PL5) of the integer program (Inst/Model/Program.lean).

  The file treats two rounding sites, QK (with the rotary tables) and V, with the families of
  looked-up values (keys in Lean names) QKH, VH and CQK, CV, and it bounds the accumulators
  (rounding site, low and high key, high digit: `key`, Inst/Model/FF/Trace.lean). `qk_at` and `v_at`
  have these hypotheses: `IntRel` (the field relation over `ZMod p`, restated over the integers:
  Inst/Model/FF/NoWrap0.lean); `AdmP`; the array a holds the program's values; l < D.nl, i < D.T,
  and c below the width (D.dqk, D.dkv). Their results, but for the high digits, are fields of
  `Part1` (Inst/Model/FF/Trace.lean).
    `AdmP p D tb L0 w`   the size conditions, the ranges of the public tables and of the weights
    `abs_two_le`         a two-byte weight is at most 2^12 in absolute value
    `Aq_eq` .. `Y'_eq`   the accumulators of the trace are those of the program, once the array a
                         holds the program's values
    `abs_Y'_le`          |Y'| ≤ 2^13 · d · 2,047 · 2^12, under `AdmP`, `hl`, `hi`, `hc`
    `qk_at`, `v_at`      the arrays qkw, q, kx, rqk and vw, v, rv hold the program's values and the
                         high digits; the range conditions of (PL5) hold
  The sizes D are not fixed: the statements hold for all sizes that meet `AdmP`, and for every shift
  that meets its conditions: at most 32 (QK) or 24 (V), with no lower limit but the no-overflow
  conditions `wq`, `wk`, `wv` (the keys are those of Inst/Model/Common/Site.lean, Sections 5 to 8).
  Labels such as "Step L1" link one docstring to another.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.

  Notation: `D`: a `Dim`: the sizes of a feed-forward segment; a, qkw, q, kx, ..: arrays (`Arr`)
  (Inst/Model/FF/Index.lean); `tb`: `Tables`: the five table functions that the program reads;
  `w l`: a `LayerW`: the weight matrices of one layer; `clamp c a`: min(max(a, −c), c); `Fits16 a`:
  a fits 16 bits: −2^15 ≤ a < 2^15 (Inst/Model/Program.lean); `L0`: a natural number: the first
  layer of the segment; `first`: a Bool: `Idn.j11` is valid only if it is true (`Idn.Valid`: "(J11)
  to the first segment only"); `emb`: a `Mat`: the embedding; `tok`: ℕ → ℕ: the prompt; `t`: a map
  `Cell` → ℤ: a trace, a function on the names of cells; `val t X inst j i`: the read-out formula,
  at an array, an instance, a channel j and a position i; `stream D t s`: state s of the stream
  (Inst/Model/FF/Trace.lean); `site`, `high` (for every shift: `ssite`, `shigh`): the low and the
  high key of a rounding; `hd A k`: ⌊rem(A, k) / 2^16⌋, the high digit; `dn k`: max(0, 16 − k)
  (Inst/Model/Common/Site.lean); `l`, `i`, `c`: a layer, a position, a channel.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.FF.NoWrapNorm

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset
open Inst.Model.TableKeys (InLut)

/-- The size conditions for the projections, the ranges of the tables and of the weights. -/
structure AdmP (p : ℤ) (D : Dim) (tb : Tables) (L0 : ℕ) (w : ℕ → LayerW) : Prop where
  big : 2 ^ 60 ≤ p
  kq : ∀ l, (D.Pl l).kq ≤ 32
  kk : ∀ l, (D.Pl l).kk ≤ 32
  kv : ∀ l, (D.Pl l).kv ≤ 24
  /-- The no-overflow condition of a rounding site, in the form of the implementation's
  (`Scales.SiteW`, Inst/Model/FF/ScalesDef.lean) with ≤ p − 2^16 where that has < 2^60: the low keys
  of QK, at the shifts of the queries and of the keys, and of V. The accumulator's bound is
  multiplied by the weight 2^dn(k), dn(k) = max(0, 16 − k) -/
  wq : ∀ l, 2 ^ Site.dn (D.Pl l).kq *
        (2 ^ 13 * ((D.d : ℤ) * (2047 * 2 ^ 12)) +
          2 ^ ((D.Pl l).kq - 1) + 2 ^ (D.Pl l).kq * 2 ^ 15) +
      2 ^ 16 * (257 * 2 ^ 18 + 32896) + 2 ^ 16 ≤ p
  wk : ∀ l, 2 ^ Site.dn (D.Pl l).kk *
        (2 ^ 13 * ((D.d : ℤ) * (2047 * 2 ^ 12)) +
          2 ^ ((D.Pl l).kk - 1) + 2 ^ (D.Pl l).kk * 2 ^ 15) +
      2 ^ 16 * (257 * 2 ^ 18 + 32896) + 2 ^ 16 ≤ p
  wv : ∀ l, 2 ^ Site.dn (D.Pl l).kv *
        ((D.d : ℤ) * (2047 * 2 ^ 12) + 2 ^ ((D.Pl l).kv - 1) + 2 ^ (D.Pl l).kv * 2 ^ 15) +
      2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ p
  even : D.P.ch % 2 = 0
  T : D.T = D.P.T
  layers : L0 + D.nl ≤ D.P.layers
  /-- the tables' ranges. The sizes that this reads are those of D.P; the number of rows of Exp,
  which no feed-forward segment reads, is that of the segment's first layer -/
  tab : tb.OK (D.Pl 0)
  wf : ∀ l < D.nl, (w l).WF D.P (L0 + l)

omit scl in
theorem abs_two_le {r c : ℕ} {W : Mat} (h : Two r c W) (j x : ℕ) : |W j x| ≤ 2 ^ 12 := by
  have := h j x
  rw [abs_le]
  split_ifs at this with hc
  · constructor <;> linarith [this.1, this.2]
  · rw [this]
    norm_num

section Rel
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {p : ℤ} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}

/-! ## The accumulators -/

section Acc
variable {l i : ℕ} (ha : ∀ j < D.d, val t .a l j i = Att.a (D.Pl l) (stream D t (2 * l)) i j)
include ha

theorem Aq_eq (x : ℕ) :
    Aq D t (fun l => LW.ofInt ℤ (w l)) l x i = Att.Aq (D.Pl l) (w l) (stream D t (2 * l)) i x :=
  sum_congr rfl fun j hj => by rw [ha j (mem_range.1 hj)]; rfl

theorem Ak_eq (x : ℕ) :
    Ak D t (fun l => LW.ofInt ℤ (w l)) l x i = Att.Ak (D.Pl l) (w l) (stream D t (2 * l)) i x :=
  sum_congr rfl fun j hj => by rw [ha j (mem_range.1 hj)]; rfl

theorem Av_eq (x : ℕ) :
    Av D t (fun l => LW.ofInt ℤ (w l)) l x i = Att.Av (D.Pl l) (w l) (stream D t (2 * l)) i x :=
  sum_congr rfl fun j hj => by rw [ha j (mem_range.1 hj)]; rfl

theorem AY_eq (x : ℕ) :
    AY D t (fun l => LW.ofInt ℤ (w l)) l x i = Att.AY (D.Pl l) (w l) (stream D t (2 * l)) i x := by
  unfold AY Att.AY
  rw [Aq_eq ha, Ak_eq ha]
  rfl

theorem Y'_eq (x : ℕ) :
    Y' D t tb L0 (fun l => LW.ofInt ℤ (w l)) l x i =
      Att.Y' (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i x := by
  unfold Y' Att.Y'
  simp only [AY_eq ha, Int.cast_id]
  rfl

end Acc

omit scl in
theorem abs_a_le (P : Params) (x : ℕ → Vec) (i j : ℕ) : |Att.a P x i j| ≤ 2047 := by
  have := TableKeys.clamp_bounds (c := 2047) (by norm_num) (NORM.yw P.n1 P.d (x i) j)
  rw [abs_le]
  exact this

theorem abs_AY_le (adm : AdmP p D tb L0 w) {l : ℕ} (hl : l < D.nl) (x : ℕ → Vec) (i c : ℕ) :
    |Att.AY (D.Pl l) (w l) x i c| ≤ (D.d : ℤ) * (2047 * 2 ^ 12) := by
  obtain ⟨hq, hk, -, -, -⟩ := adm.wf l hl
  unfold Att.AY
  split_ifs
  · exact abs_dot_le (fun j _ => abs_a_le _ x i j) fun j _ => abs_two_le hq j c
  · exact abs_dot_le (fun j _ => abs_a_le _ x i j) fun j _ => abs_two_le hk j _

theorem abs_Av_le (adm : AdmP p D tb L0 w) {l : ℕ} (hl : l < D.nl) (x : ℕ → Vec) (i c : ℕ) :
    |Att.Av (D.Pl l) (w l) x i c| ≤ (D.d : ℤ) * (2047 * 2 ^ 12) := by
  obtain ⟨-, -, hv, -, -⟩ := adm.wf l hl
  exact abs_dot_le (fun j _ => abs_a_le _ x i j) fun j _ => abs_two_le hv j c

/-- The bound on the accumulator of QK, under `AdmP`. (not all hypotheses are named here: see the
statement below) -/
theorem abs_Y'_le (adm : AdmP p D tb L0 w) {l i c : ℕ} (hl : l < D.nl) (hi : i < D.T)
    (hc : c < D.dqk) (x : ℕ → Vec) :
    |Att.Y' (D.Pl l) tb (w l) (L0 + l) x i c| ≤ 2 ^ 13 * ((D.d : ℤ) * (2047 * 2 ^ 12)) := by
  have hch : 0 < D.P.ch := by
    rcases Nat.eq_zero_or_pos D.P.ch with h0 | h0
    · exfalso
      have : D.dqk = 0 := by unfold Dim.dqk Dim.dq Dim.dkv; rw [h0]; simp
      omega
    · exact h0
  have hjj : (c % D.P.ch) / 2 < D.P.ch / 2 := by
    have h1 := Nat.mod_lt c hch
    have h2 := adm.even
    omega
  obtain ⟨⟨c1, c2⟩, s1, s2⟩ :=
    adm.tab.2.2.1 (L0 + l) (by have := adm.layers; rw [Dim.Pl_layers]; omega) i
      (by rw [Dim.Pl_T, ← adm.T]; exact hi) _ hjj
  have hC : |tb.C (L0 + l) i ((c % D.P.ch) / 2)| ≤ 2 ^ 12 := abs_le.2 ⟨c1, c2⟩
  have hS : |tb.S (L0 + l) i ((c % D.P.ch) / 2)| ≤ 2 ^ 12 := abs_le.2 ⟨s1, s2⟩
  have hB : (0 : ℤ) ≤ (D.d : ℤ) * (2047 * 2 ^ 12) := by positivity
  have hm : ∀ (u v : ℤ), |u| ≤ 2 ^ 12 → |v| ≤ (D.d : ℤ) * (2047 * 2 ^ 12) →
      |u * v| ≤ 2 ^ 12 * ((D.d : ℤ) * (2047 * 2 ^ 12)) := fun u v hu hv => by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) (by norm_num)
  unfold Att.Y'
  dsimp only
  simp only [Dim.Pl_ch]
  split_ifs
  · refine (abs_sub _ _).trans ?_
    have h1 := hm _ _ hC (abs_AY_le adm hl x i c)
    have h2 := hm _ _ hS (abs_AY_le adm hl x i (c + 1))
    linarith
  · refine (abs_add_le _ _).trans ?_
    have h1 := hm _ _ hS (abs_AY_le adm hl x i (c - 1))
    have h2 := hm _ _ hC (abs_AY_le adm hl x i c)
    linarith

/-! ## The rounding sites -/

/-- The rounding site QK (Step L8, with L1 and L2): (PL4), (PL5) for queries and keys, under
`IntRel` and `AdmP`, if the array a holds the program's values. (not all hypotheses are named here:
see the statement below) -/
theorem qk_at (h : IntRel D tb L0 first p w emb tok t) (adm : AdmP p D tb L0 w)
    {l i : ℕ} (hl : l < D.nl) (hi : i < D.T)
    (ha : ∀ j < D.d, val t .a l j i = Att.a (D.Pl l) (stream D t (2 * l)) i j)
    {c : ℕ} (hc : c < D.dqk) :
    val t .qkw l c i = Att.qkw (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c ∧
    Fits16 (val t .qkw l c i) ∧
    (if c < D.dq then val t .q l c i else val t .kx l (c - D.dq) i) =
      clamp 2047 (val t .qkw l c i) ∧
    val t .rqk l c i =
      Site.hd (Att.Y' (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c) (kQK D l c) := by
  have hk : kQK D l c ≤ 32 ∧
      2 ^ Site.dn (kQK D l c) *
            (2 ^ 13 * ((D.d : ℤ) * (2047 * 2 ^ 12)) +
              2 ^ (kQK D l c - 1) + 2 ^ kQK D l c * 2 ^ 15) +
          2 ^ 16 * (257 * 2 ^ 18 + 32896) + 2 ^ 16 ≤ p := by
    unfold kQK
    split_ifs
    · exact ⟨adm.kq l, adm.wq l⟩
    · exact ⟨adm.kk l, adm.wk l⟩
  have k3 : (2 : ℤ) ^ (32 - Site.up (kQK D l c)) ≤ 2 ^ 16 := Site.two_pow_top_sub_le _ rfl
  have hR : |val t .rqk l c i| ≤ 257 * 2 ^ 18 + 32896 := by
    have := abs_le.mp (val2 h.small .rqk rfl (a := l) (j := c) hl hc hi)
    have e : Arr.rqk.off = 32896 := rfl
    rw [e] at this
    rw [abs_le]
    constructor <;> linarith
  have hy : |if c < D.dq then val t .q l c i else val t .kx l (c - D.dq) i| ≤ 257 * 2 ^ 18 := by
    split_ifs with hq
    · exact val2z h.small .q rfl rfl (a := l) (j := c) hl hq hi
    · exact val2z h.small .kx rfl rfl (a := l) (j := c - D.dq) hl
        (by show _ < D.dkv; unfold Dim.dqk at hc; omega) hi
  have kL := h.key .QK l c i hl rfl hc hi
  have eL : key D t tb L0 (fun l => LW.ofInt ℤ (w l)) .QK l c i =
      Site.ssite (Att.Y' (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c) (val t .qkw l c i)
        (val t .rqk l c i) (kQK D l c) := by
    simp only [key]
    rw [Y'_eq ha]
  rw [eL] at kL
  have big := adm.big
  obtain ⟨r1, r2, r3, r4⟩ := clamp_ssite (top := 32) (w := 16) (B2 := 257 * 2 ^ 18)
    (Rb := 257 * 2 ^ 18 + 32896) rfl hk.1 (abs_Y'_le adm hl hi hc _)
    (val2z h.small .qkw rfl rfl (a := l) (j := c) hl hc hi) hy hR (by linarith)
    (by norm_num) (by nlinarith) hk.2 kL
    (TableKeys.InLut.r16 (h.key .QKH l c i hl rfl hc hi)) (h.key .CQK l c i hl rfl hc hi)
  exact ⟨r1, r2, r3, r4⟩

/-- The rounding site V (Step L9, with L1 and L2): (PL5) for values, under the same hypotheses. (not
all hypotheses are named here: see the statement below) -/
theorem v_at (h : IntRel D tb L0 first p w emb tok t) (adm : AdmP p D tb L0 w)
    {l i : ℕ} (hl : l < D.nl) (hi : i < D.T)
    (ha : ∀ j < D.d, val t .a l j i = Att.a (D.Pl l) (stream D t (2 * l)) i j)
    {c : ℕ} (hc : c < D.dkv) :
    val t .vw l c i = Att.vw (D.Pl l) (w l) (stream D t (2 * l)) i c ∧
    Fits16 (val t .vw l c i) ∧
    val t .v l c i = clamp 2047 (val t .vw l c i) ∧
    val t .rv l c i = Site.hd (Att.Av (D.Pl l) (w l) (stream D t (2 * l)) i c) (D.Pl l).kv := by
  have k3 : (2 : ℤ) ^ (24 - Site.up (D.Pl l).kv) ≤ 2 ^ 8 := Site.two_pow_top_sub_le _ rfl
  have hR : |val t .rv l c i| ≤ 2 ^ 18 + 128 := by
    have := abs_le.mp (val1 h.small .rv rfl (a := l) (j := c) hl hc hi)
    have e : Arr.rv.off = 128 := rfl
    rw [e] at this
    rw [abs_le]
    constructor <;> linarith
  have kL := h.key .V l c i hl rfl hc hi
  have eL : key D t tb L0 (fun l => LW.ofInt ℤ (w l)) .V l c i =
      Site.ssite (Att.Av (D.Pl l) (w l) (stream D t (2 * l)) i c) (val t .vw l c i)
        (val t .rv l c i) (D.Pl l).kv := by
    simp only [key]
    rw [Av_eq ha]
  rw [eL] at kL
  have big := adm.big
  exact clamp_ssite (top := 24) (w := 8) (B2 := 257 * 2 ^ 18) (Rb := 2 ^ 18 + 128) rfl (adm.kv l)
    (abs_Av_le adm hl _ i c) (val2z h.small .vw rfl rfl (a := l) (j := c) hl hc hi)
    (val2z h.small .v rfl rfl (a := l) (j := c) hl hc hi) hR (by linarith) (by norm_num)
    (by nlinarith) (adm.wv l) kL (TableKeys.InLut.r8 (h.key .VH l c i hl rfl hc hi))
    (h.key .CV l c i hl rfl hc hi)

end Rel

end Inst.Model.FFSeg

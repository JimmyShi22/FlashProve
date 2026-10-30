-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/SanityAtt.lean: the integer model at the reference parameters and tables depends on a
layer, on attention and on earlier tokens. To audit the relation `RinfPP` (Inst/Model/Scales.lean),
nothing of this file need be read.

The indices of Inst/Model/SanityRef.lean with a non-empty language have all layers zero: their
answers are functions of the last token, and they reach the embedding and the output matrix only.
Here, at `ppref` and `tbRef`:
    0  `norm_ok`, `norm_ok_of_le`    step (N4) never fails at the reference normalisation (M = 44, K
                                   = 30, ϵ = 53,687, width 5,120): if V + ϵ < 2^78 then every
                                   quotient yw fits 16 bits. So of the two conditions of NORM only
                                   (N1) can fail. `norm_ok_of_le`: both conditions hold if every
                                   entry x j, j < 5,120, lies in [0, 2^20].
    1  `embA`, `headA`, `layA`, `wA`, `wZ`
                                   token 0 is embedded as 2^20 in the channel 0, every other token
                                   as the zero row; layer 0 has no queries and keys, so attention is
                                   the mean over the positions so far; the value of a position is 64
                                   in all channels if its token is 0; the output projection adds all
                                   5,120 channels into the channel 2, which votes for the token 7.
                                   `wZ`: the same with layer 0 zero.
    2  `xs`, `x1`, `att_eq`, `att_ok` ..
                                   the attention block of `layA` on a stream of such rows, step by
                                   step
    3  `runs_wA`, `lg_wA`, `model_wA_pA` ..
                                   the whole program on `wA` and `wZ`, for the prompts `pA` (token 0
                                   at the positions 0 to 1,022, token 1 at the last) and `pB` (token
                                   1 everywhere)
       `sees_earlier_token`, `sees_layer`   the title's claims
The indices are made up for these proofs. They say nothing on the weights of a trained model.
Numbers are evaluated by Lean's kernel on closed integer terms; of `tbRef` only Exp[0] = 2^12 is
read.

Notation: NORM, (N1), (N4), V, yw: the subroutine `NORM` of Inst/Model/Program.lean and its steps;
M, K, ϵ: "exponent of the reciprocal; shift; constant" of a normalisation (`NormPar`, same file);
`z : ℕ → Bool`: a bit for each position; `zz prompt pos`: whether the token at pos (`tk prompt pos`)
is 0; `xs z`: the stream of rows "2^20 in the channel 0, or zero", by the bit z pos; `bz z pos`: 64
or 0, by the bit z pos; `Bs z i`: the sum of bz z j over j ≤ i; `x1 z`: `xs z` with `dl z pos` added
in the channel 2; `sv m`: a row with one entry m in the channel 2.
-/
import Inst.Model.SanityRef

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Inst.Model
namespace SanityAtt
open Finset SanityRef

/-! ## 0. Where (N1) holds, (N4) does not fail at the reference normalisation -/

theorem norm_ok (x : Vec) (hV : NORM.V 5120 x + 53687 < 2 ^ 78) : NORM.OK npR 5120 x := by
  refine ⟨hV, fun j hj => ?_⟩
  show Fits16 (rhu (x j * NORM.R npR 5120 x) 30)
  have hV0 : 0 ≤ NORM.V 5120 x := Finset.sum_nonneg fun j _ => sq_nonneg _
  obtain ⟨h0, h1, h2⟩ := isqrt_spec (v := NORM.V 5120 x + 53687) (by linarith)
  have hs1 : 1 ≤ NORM.sig npR 5120 x := sig_pos npR (by norm_num) 5120 x
  have hsdef : NORM.sig npR 5120 x = isqrt (NORM.V 5120 x + 53687) := rfl
  have hRdef : NORM.R npR 5120 x = (2 ^ 44 + NORM.sig npR 5120 x / 2) / NORM.sig npR 5120 x := rfl
  rw [← hsdef] at h0 h1 h2
  generalize NORM.sig npR 5120 x = s at *
  have hxj : x j ^ 2 ≤ NORM.V 5120 x :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_range.2 hj)
  have hle : |x j| ≤ s := by
    by_contra hc
    push Not at hc
    have h3 : (s + 1) ^ 2 ≤ |x j| ^ 2 := pow_le_pow_left₀ (by linarith) (by omega) 2
    rw [sq_abs] at h3
    linarith
  have hs39 : s < 2 ^ 39 := by
    by_contra hc
    push Not at hc
    have h3 : ((2 : ℤ) ^ 39) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by norm_num) hc 2
    norm_num at h3 hV
    linarith
  have hR0 : 0 ≤ NORM.R npR 5120 x := by
    rw [hRdef]
    have h5 : 0 ≤ s / 2 := by omega
    have h6 : (0 : ℤ) < 2 ^ 44 := by norm_num
    exact Int.ediv_nonneg (by linarith) (by linarith)
  have hsR : NORM.R npR 5120 x * s ≤ 2 ^ 44 + s / 2 := by
    rw [hRdef]
    exact Int.ediv_mul_le _ (by omega)
  generalize NORM.R npR 5120 x = R at *
  obtain ⟨hl, hu⟩ := abs_le.1 hle
  have ha1 : x j * R ≤ s * R := mul_le_mul_of_nonneg_right hu hR0
  have ha2 : -s * R ≤ x j * R := mul_le_mul_of_nonneg_right hl hR0
  have hs2 : s / 2 ≤ 2 ^ 38 := by omega
  obtain ⟨r1, r2⟩ := rhu_spec (x j * R) 30
  generalize rhu (x j * R) 30 = r at *
  norm_num at r1 r2 hs2 hsR
  unfold Fits16
  constructor
  · norm_num
    nlinarith
  · norm_num
    nlinarith

theorem norm_ok_of_le (x : Vec) (h : ∀ j < 5120, 0 ≤ x j ∧ x j ≤ 2 ^ 20) : NORM.OK npR 5120 x := by
  apply norm_ok
  have h1 : NORM.V 5120 x ≤ ∑ _j ∈ range 5120, (2 ^ 40 : ℤ) := by
    unfold NORM.V
    refine sum_le_sum fun j hj => ?_
    obtain ⟨a, b⟩ := h j (mem_range.1 hj)
    have := pow_le_pow_left₀ a b 2
    norm_num at this ⊢
    exact this
  rw [sum_const, card_range, nsmul_eq_mul] at h1
  norm_num at h1 ⊢
  linarith

/-! ## 1. The index -/

/-- token 0 is embedded as 2^20 in the channel 0; every other token as the zero row -/
def embA : Mat := fun t j => if t = 0 ∧ j = 0 then 2 ^ 20 else 0
/-- channel 2 votes for the token 7 -/
def headA : Mat := fun j ι => if j = 2 ∧ ι = 7 then 1 else 0
/-- layer 0: no queries and keys (all scores 0: attention is the mean over the positions so far);
the value of a position is 64 in all channels if its token is 0; the output projection adds all
5,120 channels into the channel 2 -/
def layA : LayerW := { zeroLayer with
  Wv := fun j c => if j = 0 ∧ c < 1024 then 4095 else 0
  Wo := fun j c => if j < 5120 ∧ c = 2 then 4095 else 0 }
def wA : Weights := ⟨fun L => if L = 0 then layA else zeroLayer, embA, headA⟩
/-- the same index with layer 0 zero -/
def wZ : Weights := ⟨fun _ => zeroLayer, embA, headA⟩

theorem layA_wf : layA.WF ppref 0 := by
  unfold LayerW.WF
  refine ⟨SanityRef.two_zero _ _, SanityRef.two_zero _ _, fun j c => ?_, fun j c => ?_, ?_⟩
  · show if j < 5120 ∧ c < 1024 then
      _ ≤ (if j = 0 ∧ c < 1024 then (4095 : ℤ) else 0) ∧
        (if j = 0 ∧ c < 1024 then (4095 : ℤ) else 0) ≤ _
    else (if j = 0 ∧ c < 1024 then (4095 : ℤ) else 0) = 0
    split_ifs <;> omega
  · show if j < 5120 ∧ c < 5120 then
      _ ≤ (if j < 5120 ∧ c = 2 then (4095 : ℤ) else 0) ∧
        (if j < 5120 ∧ c = 2 then (4095 : ℤ) else 0) ≤ _
    else (if j < 5120 ∧ c = 2 then (4095 : ℤ) else 0) = 0
    split_ifs <;> omega
  · rw [if_neg (by decide)]
    exact ⟨SanityRef.two_zero _ _,
      SanityRef.two_zero _ _,
      SanityRef.two_zero _ _,
      SanityRef.two_zero _ _,
      fun e => ⟨SanityRef.two_zero _ _, SanityRef.two_zero _ _, SanityRef.two_zero _ _⟩⟩

theorem embA_box : Box ppref.V ppref.d (-2155905152) 2139062143 embA := fun t j => by
  show if t < 202048 ∧ j < 5120 then
    _ ≤ (if t = 0 ∧ j = 0 then (2 ^ 20 : ℤ) else 0) ∧
      (if t = 0 ∧ j = 0 then (2 ^ 20 : ℤ) else 0) ≤ _
  else (if t = 0 ∧ j = 0 then (2 ^ 20 : ℤ) else 0) = 0
  split_ifs <;> omega

theorem headA_two : Two ppref.d ppref.V headA := fun j ι => by
  show if j < 5120 ∧ ι < 202048 then
    _ ≤ (if j = 2 ∧ ι = 7 then (1 : ℤ) else 0) ∧ (if j = 2 ∧ ι = 7 then (1 : ℤ) else 0) ≤ _
  else (if j = 2 ∧ ι = 7 then (1 : ℤ) else 0) = 0
  split_ifs <;> omega

theorem wA_wf : wA.WF ppref := by
  refine ⟨fun L => ?_, embA_box, headA_two⟩
  show if L < ppref.layers then (if L = 0 then layA else zeroLayer).WF ppref L
  else (if L = 0 then layA else zeroLayer).IsZero
  by_cases h0 : L = 0
  · subst h0
    rw [if_pos (by decide), if_pos rfl]
    exact layA_wf
  · rw [if_neg h0]
    split_ifs
    · exact zeroLayer_wf L
    · exact zeroLayer_isZero

theorem wZ_wf : wZ.WF ppref := by
  refine ⟨fun L => ?_, embA_box, headA_two⟩
  split_ifs
  · exact zeroLayer_wf L
  · exact zeroLayer_isZero

/-! ## 2. The attention block of layA on a stream of rows "2^20 in the channel 0, or zero" -/

section Block
variable (z : ℕ → Bool)

def xs : ℕ → Vec := fun pos j => if z pos = true ∧ j = 0 then 2 ^ 20 else 0
def bz (pos : ℕ) : ℤ := if z pos = true then 64 else 0
def Bs (i : ℕ) : ℤ := ∑ j ∈ range (i + 1), bz z j
def Oq (i : ℕ) : ℤ := (2 * (4096 * Bs z i) + 4096 * ((i : ℤ) + 1)) / (2 * (4096 * ((i : ℤ) + 1)))
def dl (i : ℕ) : ℤ := rhu (5120 * (Oq z i * 4095)) 17
def x1 : ℕ → Vec := fun pos c => xs z pos c + if c = 2 then dl z pos else 0

theorem out_zero (j : ℕ) : NORM.out npR 5120 (fun _ => 0) j = 0 := by
  show clamp 2047 (rhu ((0 : ℤ) * _) 30) = 0
  rw [zero_mul, rhu_zero (by norm_num)]
  decide +kernel

theorem ok_xs (pos : ℕ) : NORM.OK npR 5120 (xs z pos) :=
  norm_ok_of_le _ fun j _ => by
    unfold xs
    split_ifs <;> norm_num

theorem a_eq (pos : ℕ) :
    Att.a ppref (xs z) pos = fun j => if z pos = true ∧ j = 0 then 2047 else 0 := by
  funext j
  show NORM.out npR 5120 (xs z pos) j = _
  cases hz : z pos
  · have e : xs z pos = fun _ => 0 := by funext j; simp [xs, hz]
    rw [e, out_zero]
    simp
  · have e : xs z pos = row 0 := by funext j; simp [xs, hz, row]
    rw [e, out_row (by norm_num)]
    simp

theorem Av_eq (pos c : ℕ) :
    Att.Av ppref layA (xs z) pos c = if z pos = true ∧ c < 1024 then 2047 * 4095 else 0 := by
  unfold Att.Av dot
  rw [a_eq]
  show ∑ j ∈ range 5120,
      (if z pos = true ∧ j = 0 then (2047 : ℤ) else 0) * (if j = 0 ∧ c < 1024 then 4095 else 0) = _
  rw [sum_eq_single 0 (fun j _ hj => by simp [hj]) (fun h => absurd (mem_range.2 (by norm_num)) h)]
  cases z pos <;> by_cases hc : c < 1024 <;> simp [hc]

theorem vw_eq (pos c : ℕ) :
    Att.vw ppref layA (xs z) pos c = if z pos = true ∧ c < 1024 then 64 else 0 := by
  unfold Att.vw
  rw [Av_eq]
  show rhu _ 17 = _
  split_ifs
  · decide +kernel
  · exact rhu_zero (by norm_num)

theorem v_eq (pos c : ℕ) :
    Att.v ppref layA (xs z) pos c = if z pos = true ∧ c < 1024 then 64 else 0 := by
  unfold Att.v
  rw [vw_eq]
  split_ifs <;> decide +kernel

theorem qkw0 (x : ℕ → Vec) (i c : ℕ) : Att.qkw ppref tbRef layA 0 x i c = 0 := by
  have hA : ∀ c', Att.AY ppref layA x i c' = 0 := by
    intro c'
    simp [Att.AY, Att.Aq, Att.Ak, layA, zeroLayer, dot_zero]
  simp only [Att.qkw, Att.Y', hA, mul_zero, sub_zero, add_zero, ite_self]
  split_ifs
  · exact rhu_zero (by decide)
  · exact rhu_zero (by decide)

theorem clamp0 : clamp 2047 0 = 0 := by decide +kernel

theorem sc0 (x : ℕ → Vec) (h i j : ℕ) : Att.sc ppref tbRef layA 0 x h i j = 0 := by
  simp only [Att.sc, Att.q, Att.kx, qkw0, clamp0, mul_zero, sum_const_zero]

theorem maxTo_zero : ∀ n, maxTo (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp [maxTo, maxTo_zero n]

theorem wt_eq (x : ℕ → Vec) (h i j : ℕ) : Att.wt ppref tbRef layA 0 x h i j = 4096 := by
  have hs : Att.sc ppref tbRef layA 0 x h i = fun _ => 0 := funext (sc0 x h i)
  have hu : Att.u ppref tbRef layA 0 x h i j = 0 := by
    unfold Att.u Att.mx
    rw [hs, maxTo_zero]
    norm_num
  unfold Att.wt
  rw [hu, if_pos (by decide)]
  exact refExp_zero.trans (by norm_num)

theorem den_eq (x : ℕ → Vec) (h i : ℕ) :
    Att.den ppref tbRef layA 0 x h i = 4096 * ((i : ℤ) + 1) := by
  unfold Att.den
  simp only [wt_eq]
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem ac_eq (i c : ℕ) (hc : c < 5120) :
    Att.ac ppref tbRef layA 0 (xs z) (c / ppref.ch) i (c % ppref.ch) = 4096 * Bs z i := by
  unfold Att.ac Bs
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hlt : ppref.ch * Att.kvOf ppref (c / ppref.ch) + c % ppref.ch < 1024 := by
    rw [ppref_readback.2.2.1]
    show 128 * (c / 128 / 5) + c % 128 < 1024
    omega
  rw [wt_eq, v_eq]
  unfold bz
  cases z j <;> simp [hlt]

theorem o_eq (i c : ℕ) (hc : c < 5120) : Att.o ppref tbRef layA 0 (xs z) i c = Oq z i := by
  unfold Att.o Oq
  rw [ac_eq z i c hc, den_eq]

/-- The stream after the attention block. -/
theorem att_eq : Att.x' ppref tbRef layA 0 (xs z) = x1 z := by
  funext i c
  suffices key : rhu
        (dot (Att.dq ppref) (Att.o ppref tbRef layA 0 (xs z) i) fun j => layA.Wo j c) ppref.ko =
      if c = 2 then dl z i else 0 by
    unfold Att.x' x1
    rw [key]
  unfold dot
  rw [ppref_readback.1]
  show rhu (∑ j ∈ range 5120,
        Att.o ppref tbRef layA 0 (xs z) i j * (if j < 5120 ∧ c = 2 then 4095 else 0)) 17 = _
  by_cases hc : c = 2
  · rw [sum_congr rfl
          (fun j hj => by rw [o_eq z i j (mem_range.1 hj), if_pos ⟨mem_range.1 hj, hc⟩]),
      sum_const, card_range, nsmul_eq_mul, if_pos hc]
    rfl
  · rw [sum_eq_zero (fun j _ => by rw [if_neg (fun h => hc h.2), mul_zero]), if_neg hc]
    exact rhu_zero (by norm_num)

theorem Bs_nonneg (i : ℕ) : 0 ≤ Bs z i := sum_nonneg fun j _ => by unfold bz; split_ifs <;> norm_num

theorem Bs_le (i : ℕ) : Bs z i ≤ 64 * ((i : ℤ) + 1) := by
  have h : Bs z i ≤ ∑ _j ∈ range (i + 1), (64 : ℤ) :=
    sum_le_sum fun j _ => by unfold bz; split_ifs <;> norm_num
  rw [sum_const, card_range, nsmul_eq_mul] at h
  push_cast at h
  linarith

theorem Oq_bounds (i : ℕ) : 0 ≤ Oq z i ∧ Oq z i < 65 := by
  have h0 := Bs_nonneg z i
  have h1 := Bs_le z i
  have hi : (0 : ℤ) ≤ i := Int.natCast_nonneg i
  unfold Oq
  exact ⟨Int.ediv_nonneg (by linarith) (by linarith),
    Int.ediv_lt_of_lt_mul (by linarith) (by linarith)⟩

theorem dl_bounds (i : ℕ) : 0 ≤ dl z i ∧ dl z i ≤ 10238 := by
  obtain ⟨h0, h1⟩ := Oq_bounds z i
  obtain ⟨r1, r2⟩ := rhu_spec (5120 * (Oq z i * 4095)) 17
  unfold dl
  generalize rhu (5120 * (Oq z i * 4095)) 17 = r at *
  norm_num at r1 r2
  constructor <;> omega

theorem ok_x1 (pos : ℕ) : NORM.OK npR 5120 (x1 z pos) :=
  norm_ok_of_le _ fun j _ => by
    obtain ⟨h0, h1⟩ := dl_bounds z pos
    unfold x1 xs
    split_ifs <;> omega

/-- the range conditions of the attention block -/
theorem att_ok : Att.OK ppref tbRef layA 0 (xs z) := fun i _ =>
  ⟨ok_xs z i, fun c _ => by rw [qkw0]; exact fits16_zero, fun c _ => by
    rw [vw_eq]
    unfold Fits16
    split_ifs <;> norm_num⟩

/-! the feed-forward block of layA is that of the zero layer -/
theorem ff_layA (x : ℕ → Vec) : FF.x'' ppref tbRef layA 0 x = x := by
  funext i c
  simp [FF.x'', FF.Ad, layA, zeroLayer, rhu_zero (show 1 ≤ ppref.kd by decide)]

theorem ff_ok_layA (x : ℕ → Vec) (hx : ∀ i < ppref.T, NORM.OK ppref.n2 ppref.d (x i)) :
    FF.OK ppref tbRef layA 0 x := by
  have hkG : ∀ j, 1 ≤ FF.kG ppref 0 j := by intro j; unfold FF.kG; split_ifs <;> decide
  have hkU : ∀ j, 1 ≤ FF.kU ppref 0 j := by intro j; unfold FF.kU; split_ifs <;> decide
  have hwg : ∀ i j, FF.wg ppref layA 0 x i j = fun _ => 0 := by
    intro i j; funext t; simp [FF.wg, layA, zeroLayer]
  have hwu : ∀ i j, FF.wu ppref layA 0 x i j = fun _ => 0 := by
    intro i j; funext t; simp [FF.wu, layA, zeroLayer]
  have h2 : ∀ i j,
      UNIT.OK ppref.d (FF.z ppref tbRef layA 0 x i j) (FF.wg ppref layA 0 x i j)
        (FF.wu ppref layA 0 x i j) (FF.kG ppref 0 j) (FF.kU ppref 0 j) := by
    intro i j
    simp only [UNIT.OK, UNIT.gh, UNIT.g0, UNIT.gw, UNIT.up, hwg, hwu, dot_zero, rhu_zero (hkG j),
      rhu_zero (hkU j), lowByte]
    refine ⟨by norm_num, fits16_zero⟩
  exact fun i hi => ⟨hx i hi, fun h => absurd h (by decide), fun j _ => h2 i j⟩

end Block

/-! ## 3. The whole program on `wA` and `wZ`; sanity lemmas -/

section
variable (prompt : Fin ppref.T → Fin ppref.V)

def tk (pos : ℕ) : ℕ := if h : pos < ppref.T then (prompt ⟨pos, h⟩).val else 1
def zz : ℕ → Bool := fun pos => decide (tk prompt pos = 0)

theorem X0_eq (w : ℕ → LayerW) : X ppref tbRef ⟨w, embA, headA⟩ prompt 0 = xs (zz prompt) := by
  funext pos j
  show (if h : pos < ppref.T then embA (prompt ⟨pos, h⟩) j else 0) = _
  unfold xs zz tk embA
  by_cases h : pos < ppref.T
  · simp [h]
  · simp [h]

theorem X_ge (l : ℕ) : X ppref tbRef wA prompt (l + 1) = x1 (zz prompt) := by
  induction l with
  | zero =>
    rw [X_succ, if_pos (by decide)]
    show Att.x' ppref tbRef layA 0 (X ppref tbRef wA prompt 0) = _
    rw [show X ppref tbRef wA prompt 0 = xs (zz prompt) from X0_eq prompt _, att_eq]
  | succ l ih =>
    rw [X_succ, ih]
    by_cases h0 : l = 0
    · subst h0
      rw [if_neg (by decide)]
      exact ff_layA _
    · have hL : wA.layer ((l + 1) / 2) = zeroLayer := if_neg (by omega)
      rw [hL]
      split_ifs
      · exact att_zero ppref tbRef _ _ (by decide)
      · exact ff_zero ppref tbRef _ _ (by decide)

theorem runs_wA : Runs ppref tbRef wA prompt := by
  refine ⟨fun L _ => ⟨?_, ?_⟩, fun pos _ => ?_⟩
  · by_cases h0 : L = 0
    · subst h0
      show Att.OK ppref tbRef layA 0 (X ppref tbRef wA prompt 0)
      rw [show X ppref tbRef wA prompt 0 = xs (zz prompt) from X0_eq prompt _]
      exact att_ok _
    · have hLy : wA.layer L = zeroLayer := if_neg h0
      have e : 2 * L = (2 * L - 1) + 1 := by omega
      rw [hLy, e, X_ge]
      exact (att_ok_zero ppref tbRef L _ (by decide) (by decide) (by decide)).2 fun i _ => ok_x1 _ i
  · rw [X_ge]
    by_cases h0 : L = 0
    · subst h0
      exact ff_ok_layA _ fun i _ => ok_x1 _ i
    · have hLy : wA.layer L = zeroLayer := if_neg h0
      rw [hLy]
      exact (ff_ok_zero ppref tbRef L _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).2
        fun i _ => ok_x1 _ i
  · have e : X ppref tbRef wA prompt (2 * ppref.layers) = x1 (zz prompt) := X_ge prompt 95
    rw [e]
    exact ok_x1 _ pos

theorem lg_wA (ι : ℕ) :
    lg ppref tbRef wA prompt (ppref.T - 1) ι =
      NORM.out npR 5120 (x1 (zz prompt) 1023) 2 * (if ι = 7 then 1 else 0) := by
  have e : X ppref tbRef wA prompt (2 * ppref.layers) = x1 (zz prompt) := X_ge prompt 95
  unfold lg nrm dot
  rw [e]
  show ∑ j ∈ range 5120,
      NORM.out npR 5120 (x1 (zz prompt) 1023) j * (if j = 2 ∧ ι = 7 then 1 else 0) = _
  rw [sum_eq_single 2 (fun j _ hj => by simp [hj]) (fun h => absurd (mem_range.2 (by norm_num)) h)]
  simp

theorem runs_wZ : Runs ppref tbRef wZ prompt :=
  runs_zero ppref tbRef embA headA prompt shifts_ref fun pos _ => by
    rw [X0_eq]
    exact ⟨ok_xs _ pos, ok_xs _ pos, ok_xs _ pos⟩

theorem lg_wZ (ι : ℕ) :
    lg ppref tbRef wZ prompt (ppref.T - 1) ι =
      NORM.out npR 5120 (xs (zz prompt) 1023) 2 * (if ι = 7 then 1 else 0) := by
  have e : X ppref tbRef wZ prompt (2 * ppref.layers) = xs (zz prompt) :=
    (X_zero ppref tbRef embA headA prompt shifts_ref _).trans (X0_eq prompt _)
  unfold lg nrm dot
  rw [e]
  show ∑ j ∈ range 5120,
      NORM.out npR 5120 (xs (zz prompt) 1023) j * (if j = 2 ∧ ι = 7 then 1 else 0) = _
  rw [sum_eq_single 2 (fun j _ hj => by simp [hj]) (fun h => absurd (mem_range.2 (by norm_num)) h)]
  simp
end

/-! ## The normalisation of a row with one entry m in the channel 2 -/
def sv (m : ℤ) : Vec := fun c => if c = 2 then m else 0

theorem V_sv (m : ℤ) : NORM.V 5120 (sv m) = m ^ 2 := by
  unfold NORM.V
  rw [sum_eq_single 2 (fun j _ hj => by simp [sv, hj])
      (fun h => absurd (mem_range.2 (by norm_num)) h)]
  simp [sv]

theorem out_sv (m : ℤ) :
    NORM.out npR 5120 (sv m) 2 =
      clamp 2047 (rhu (m * ((2 ^ 44 + isqrt (m ^ 2 + 53687) / 2) / isqrt (m ^ 2 + 53687))) 30) := by
  unfold NORM.out NORM.yw NORM.R NORM.sig
  rw [V_sv]
  rfl

theorem out_sv_big : NORM.out npR 5120 (sv 10238) 2 = 2047 := by rw [out_sv]; decide +kernel
theorem out_sv_zero : NORM.out npR 5120 (sv 0) 2 = 0 := by rw [out_sv]; decide +kernel

/-! ## Two prompts that agree at the last position -/
def t0 : Fin ppref.V := ⟨0, show 0 < 202048 by norm_num⟩
def t1 : Fin ppref.V := ⟨1, show 1 < 202048 by norm_num⟩
/-- the token 0 at the positions 0, .., 1,022 and the token 1 at the last -/
def pA : Fin ppref.T → Fin ppref.V := fun pos => if pos.val < 1023 then t0 else t1
/-- the token 1 everywhere -/
def pB : Fin ppref.T → Fin ppref.V := fun _ => t1

theorem zz_pA : zz pA = fun pos => decide (pos < 1023) := by
  funext pos
  unfold zz tk pA
  by_cases h : pos < ppref.T
  · rw [dif_pos h]
    by_cases h2 : pos < 1023
    · simp [h2, t0]
    · simp [h2, t1]
  · rw [dif_neg h]
    have h2 : ¬ pos < 1023 := fun h3 => h (lt_trans h3 (by decide))
    simp [h2]

theorem zz_pB : zz pB = fun _ => false := by
  funext pos
  unfold zz tk pB
  by_cases h : pos < ppref.T
  · rw [dif_pos h]; simp [t1]
  · rw [dif_neg h]; simp

theorem x1_pA : x1 (zz pA) 1023 = sv 10238 := by
  rw [zz_pA]
  have hB : Bs (fun pos => decide (pos < 1023)) 1023 = 64 * 1023 := by
    unfold Bs
    rw [sum_range_succ,
      sum_congr rfl
        (fun j hj => show bz (fun pos => decide (pos < 1023)) j = 64 by simp [bz, mem_range.1 hj]),
      sum_const, card_range, nsmul_eq_mul]
    simp [bz]
  have hO : Oq (fun pos => decide (pos < 1023)) 1023 = 64 := by
    unfold Oq
    rw [hB]
    norm_num
  have hd : dl (fun pos => decide (pos < 1023)) 1023 = 10238 := by
    unfold dl
    rw [hO]
    decide +kernel
  funext c
  unfold x1 xs sv
  rw [hd]
  simp

theorem x1_pB : x1 (zz pB) 1023 = sv 0 := by
  rw [zz_pB]
  have hB : Bs (fun _ => false) 1023 = 0 := by simp [Bs, bz]
  have hO : Oq (fun _ => false) 1023 = 0 := by
    unfold Oq
    rw [hB]
    norm_num
  have hd : dl (fun _ => false) 1023 = 0 := by
    unfold dl
    rw [hO]
    decide +kernel
  funext c
  unfold x1 xs sv
  rw [hd]
  simp

theorem xs_pA : xs (zz pA) 1023 = sv 0 := by
  rw [zz_pA]
  funext c
  simp [xs, sv]

theorem model_wA_pA : ModelIs ppref tbRef wA pA 7 := by
  refine ⟨runs_wA pA, show 7 < 202048 by norm_num, fun ι _ => ?_, fun ι hι => ?_⟩
  · rw [lg_wA, lg_wA, x1_pA, out_sv_big, if_pos rfl]
    split_ifs <;> norm_num
  · rw [lg_wA, lg_wA, x1_pA, out_sv_big, if_neg (Nat.ne_of_lt hι)]
    norm_num

theorem model_wA_pB : ModelIs ppref tbRef wA pB 0 := by
  refine ⟨runs_wA pB, show 0 < 202048 by norm_num, fun ι _ => ?_,
    fun ι hι => absurd hι (Nat.not_lt_zero _)⟩
  rw [lg_wA, lg_wA, x1_pB, out_sv_zero]
  norm_num

theorem model_wZ_pA : ModelIs ppref tbRef wZ pA 0 := by
  refine ⟨runs_wZ pA, show 0 < 202048 by norm_num, fun ι _ => ?_,
    fun ι hι => absurd hι (Nat.not_lt_zero _)⟩
  rw [lg_wZ, lg_wZ, xs_pA, out_sv_zero]
  norm_num

theorem xs_pB : xs (zz pB) 1023 = sv 0 := by
  rw [zz_pB]
  funext c
  simp [xs, sv]

theorem model_wZ_pB : ModelIs ppref tbRef wZ pB 0 := by
  refine ⟨runs_wZ pB, show 0 < 202048 by norm_num, fun ι _ => ?_,
    fun ι hι => absurd hι (Nat.not_lt_zero _)⟩
  rw [lg_wZ, lg_wZ, xs_pB, out_sv_zero]
  norm_num

/-- R_inf (`Rinf ppref tbRef`, Inst/Model/Program.lean) depends on earlier tokens (so attention is
at work): one well-formed index, two prompts with the same last token, two different next tokens. -/
theorem sees_earlier_token :
    ∃ (i : Index ppref) (p p' : Fin ppref.T → Fin ppref.V) (y y' : ℕ), p lastPos = p' lastPos ∧
      y ≠ y' ∧ ModelIs ppref tbRef i.val p y ∧ ModelIs ppref tbRef i.val p' y' :=
  ⟨⟨wA, wA_wf⟩, pA, pB, 7, 0, rfl, by decide, model_wA_pA, model_wA_pB⟩

/-- R_inf (`Rinf ppref tbRef`, Inst/Model/Program.lean) depends on the weights of a layer: two
well-formed indices with the same embedding, the same output matrix and the same layers 1, .., 47
answer one prompt differently. (In the proof they differ in W_v and W_o only.) -/
theorem sees_layer : ∃ (i i' : Index ppref) (p : Fin ppref.T → Fin ppref.V) (y y' : ℕ),
    i.val.Emb = i'.val.Emb ∧ i.val.H = i'.val.H ∧ (∀ L, L ≠ 0 → i.val.layer L = i'.val.layer L) ∧
    y ≠ y' ∧ ModelIs ppref tbRef i.val p y ∧ ModelIs ppref tbRef i'.val p y' :=
  ⟨⟨wA, wA_wf⟩, ⟨wZ, wZ_wf⟩, pA, 7, 0, rfl, rfl, fun _ hL => if_neg hL,
    by decide, model_wA_pA, model_wZ_pA⟩

end SanityAtt
end Inst.Model

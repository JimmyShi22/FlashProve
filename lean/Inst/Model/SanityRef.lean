-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/SanityRef.lean: the integer model at the reference parameters and tables, on one family
and two single well-formed indices. To audit the relation `RinfPP` (Inst/Model/Scales.lean), nothing
of this file need be read.

Inst/Model/Sanity.lean shows on a toy configuration that the program of Inst/Model/Program.lean runs
and that two indices differ. Here the same is shown of `ModelIs` at `ppref` and `tbRef`, the
reference parameters and tables: it is neither empty, nor the same for all indices, nor total.
    1  `row`, `V_row` .. `ok_row`    the normalisation (M = 44, K = 30, ϵ = 53,687, width 5,120) of
                                   a row with one entry 2^20, in a channel s < 5,120: ς = 2^20, R =
                                   2^24, yw = 16,384, out = 2,047 in that channel and 0 elsewhere;
                                   nothing halts
    2  `wts σ τ`, `wts_wf`, `model_wts`
                                   all layers zero; token t is embedded as 2^20 in the channel σ t;
                                   channel j votes for the token τ j. The model of this index, if
                                   every σ t is below 5,120 and every τ j below 202,048: the next
                                   token is τ (σ (the last token of the prompt))
    3  `zeroW`, `model_zeroW`        the all-zero index answers every prompt with the token 0
    4  `haltW`, `halts_haltW`        every token is embedded as (1,000, .., 1,000), and all entries
                                   of W_q of layer 0 are 4,095: at the position 0 the quotient qkw
                                   of the first query channel is 36,631, which does not fit 16 bits,
                                   so step (PL5) halts, whatever the prompt: a well-formed index
                                   with no output at all
The indices are made up for these proofs. They say nothing on the weights of a trained model.
Numbers are evaluated by Lean's kernel (`decide +kernel`) on closed integer terms; of
`tbRef` only C[0][0][0] = 4,096 and S[0][0][0] = 0 are read.

Notation: (in the words of the doc comments of Inst/Model/Program.lean)
  M, K, ϵ: the fields `M`, `K` (natural numbers) and `eps` (an integer) of `NormPar`: "exponent of
      the reciprocal; shift; constant" of a normalisation
  V: `NORM.V`, an integer: (N1) V = Σ_j x[j]²
  ς: `NORM.sig`, an integer: (N2) ς = isqrt(V + ϵ)
  R: `NORM.R`, an integer: (N3) R = ⌊(2^M + ⌊ς/2⌋) / ς⌋
  yw: `NORM.yw`, integers: (N4) yw[j] = rhu(x[j] R, K)
  out: `NORM.out`, integers: (N5) out[j] = clamp_2047(yw[j])
  index: `Weights`: the weight tensors, as integers, independent of any layout
  well-formed: `Weights.WF`
-/
import Inst.Model.Sanity
import Inst.Model.TablesRef

set_option autoImplicit false

namespace Inst.Model
namespace SanityRef

open Finset

/-! ## 1. The normalisation of a row with one entry 2^20 -/

/-- the parameters of all three normalisations of `ppref` -/
abbrev npR : NormPar := ⟨44, 30, 53687⟩

/-- the row with the entry 2^20 in the channel s, and 0 elsewhere -/
def row (s : ℕ) : Vec := fun j => if j = s then 2 ^ 20 else 0

theorem V_row {s : ℕ} (hs : s < 5120) : NORM.V 5120 (row s) = 2 ^ 40 := by
  unfold NORM.V
  rw [sum_eq_single s (fun j _ hj => by simp [row, hj]) (fun h => absurd (mem_range.2 hs) h)]
  simp [row]

theorem sig_row {s : ℕ} (hs : s < 5120) : NORM.sig npR 5120 (row s) = 2 ^ 20 := by
  unfold NORM.sig
  rw [V_row hs]
  decide +kernel

theorem R_row {s : ℕ} (hs : s < 5120) : NORM.R npR 5120 (row s) = 2 ^ 24 := by
  unfold NORM.R
  rw [sig_row hs]
  decide +kernel

theorem yw_row {s : ℕ} (hs : s < 5120) (j : ℕ) :
    NORM.yw npR 5120 (row s) j = if j = s then 16384 else 0 := by
  unfold NORM.yw
  rw [R_row hs]
  by_cases h : j = s
  · rw [if_pos h, show row s j = 2 ^ 20 from if_pos h]
    decide +kernel
  · rw [if_neg h, show row s j = 0 from if_neg h]
    decide +kernel

theorem out_row {s : ℕ} (hs : s < 5120) (j : ℕ) :
    NORM.out npR 5120 (row s) j = if j = s then 2047 else 0 := by
  unfold NORM.out
  rw [yw_row hs]
  by_cases h : j = s
  · rw [if_pos h, if_pos h]
    decide +kernel
  · rw [if_neg h, if_neg h]
    decide +kernel

theorem ok_row {s : ℕ} (hs : s < 5120) : NORM.OK npR 5120 (row s) := by
  refine ⟨?_, fun j _ => ?_⟩
  · rw [V_row hs]
    decide +kernel
  · rw [yw_row hs]
    by_cases h : j = s
    · rw [if_pos h]
      unfold Fits16
      norm_num
    · rw [if_neg h]
      exact fits16_zero

/-! ## 2. A family of well-formed indices whose layers are zero -/

/-- token t has the embedding row with 2^20 in the channel σ t -/
def embOf (σ : ℕ → ℕ) : Mat := fun t j => if t < 202048 ∧ j < 5120 then row (σ t) j else 0
/-- channel j votes for the token τ j -/
def headOf (τ : ℕ → ℕ) : Mat := fun j ι =>
  if j < 5120 ∧ ι < 202048 then (if ι = τ j then 1 else 0) else 0
/-- The index: all layers zero, these two matrices. -/
def wts (σ τ : ℕ → ℕ) : Weights := ⟨fun _ => zeroLayer, embOf σ, headOf τ⟩

theorem two_zero (r c : ℕ) : Two r c (fun _ _ => 0) := by
  intro j x
  split_ifs <;> norm_num

theorem zeroLayer_wf (L : ℕ) : zeroLayer.WF ppref L := by
  unfold LayerW.WF
  refine ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, ?_⟩
  split_ifs
  · refine ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, fun e => ?_⟩
    split_ifs <;> exact ⟨two_zero _ _, two_zero _ _, two_zero _ _⟩
  · exact ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _,
      fun e => ⟨two_zero _ _, two_zero _ _, two_zero _ _⟩⟩

theorem zeroLayer_isZero : zeroLayer.IsZero :=
  ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _,
    two_zero _ _, fun _ => ⟨two_zero _ _, two_zero _ _, two_zero _ _⟩⟩

theorem wts_wf (σ τ : ℕ → ℕ) : (wts σ τ).WF ppref := by
  refine ⟨fun L => ?_, fun t j => ?_, fun j ι => ?_⟩
  · split_ifs
    · exact zeroLayer_wf L
    · exact zeroLayer_isZero
  · show if t < 202048 ∧ j < 5120 then _ ≤ embOf σ t j ∧ embOf σ t j ≤ _ else embOf σ t j = 0
    unfold embOf row
    split_ifs <;> norm_num
  · show if j < 5120 ∧ ι < 202048 then _ ≤ headOf τ j ι ∧ headOf τ j ι ≤ _ else headOf τ j ι = 0
    unfold headOf
    split_ifs <;> norm_num

theorem shifts_ref : ppref.Shifts1 := by
  unfold Params.Shifts1
  decide

variable (σ τ : ℕ → ℕ) (prompt : Fin ppref.T → Fin ppref.V)

/-- under `hσ`, the stream at the start: the embedding rows of the prompt -/
theorem X0_wts (hσ : ∀ t, σ t < 5120) (pos : ℕ) (h : pos < ppref.T) :
    X ppref tbRef (wts σ τ) prompt 0 pos = row (σ (prompt ⟨pos, h⟩)) := by
  funext j
  show (if h : pos < ppref.T then embOf σ (prompt ⟨pos, h⟩) j else 0) = _
  rw [dif_pos h]
  unfold embOf
  by_cases hj : j < 5120
  · rw [if_pos ⟨(prompt ⟨pos, h⟩).2, hj⟩]
  · rw [if_neg fun hh => hj hh.2]
    have : j ≠ σ (prompt ⟨pos, h⟩) := fun e => hj (e ▸ hσ _)
    exact (if_neg this).symm

/-- Under `hσ` no range condition fails. -/
theorem runs_wts (hσ : ∀ t, σ t < 5120) : Runs ppref tbRef (wts σ τ) prompt :=
  runs_zero ppref tbRef (embOf σ) (headOf τ) prompt shifts_ref fun pos hpos => by
    have e : X ppref tbRef ⟨fun _ => zeroLayer, embOf σ, headOf τ⟩ prompt 0 pos =
        row (σ (prompt ⟨pos, hpos⟩)) :=
      X0_wts σ τ prompt hσ pos hpos
    rw [e]
    exact ⟨ok_row (hσ _), ok_row (hσ _), ok_row (hσ _)⟩

/-- the last position -/
def lastPos : Fin ppref.T := ⟨1023, by decide⟩

/-- Under `hσ`, `hι`, the logits at the last position: 2,047 for the token for which the channel of
the last token votes, 0 for all others. -/
theorem lg_wts (hσ : ∀ t, σ t < 5120) {ι : ℕ} (hι : ι < 202048) :
    lg ppref tbRef (wts σ τ) prompt (ppref.T - 1) ι =
      if ι = τ (σ (prompt lastPos)) then 2047 else 0 := by
  have e : X ppref tbRef (wts σ τ) prompt (2 * ppref.layers) (ppref.T - 1) =
      row (σ (prompt lastPos)) := by
    rw [show X ppref tbRef (wts σ τ) prompt (2 * ppref.layers) = X ppref tbRef (wts σ τ) prompt 0
        from X_zero ppref tbRef (embOf σ) (headOf τ) prompt shifts_ref _]
    exact X0_wts σ τ prompt hσ 1023 (by decide)
  unfold lg nrm dot
  rw [e]
  show ∑ j ∈ range 5120, NORM.out npR 5120 (row (σ (prompt lastPos))) j * headOf τ j ι = _
  rw [sum_eq_single (σ (prompt lastPos)) (fun j _ hj => by rw [out_row (hσ _), if_neg hj, zero_mul])
        (fun h => absurd (mem_range.2 (hσ _)) h),
    out_row (hσ _), if_pos rfl]
  unfold headOf
  rw [if_pos ⟨hσ _, hι⟩]
  split_ifs <;> norm_num

/-- Under `hσ`, `hτ`, the model of this index: the next token is τ (σ (the last token of the
prompt)). -/
theorem model_wts (hσ : ∀ t, σ t < 5120) (hτ : ∀ j, τ j < 202048) :
    ModelIs ppref tbRef (wts σ τ) prompt (τ (σ (prompt lastPos))) := by
  refine ⟨runs_wts σ τ prompt hσ, hτ _, fun ι hι => ?_, fun ι hι => ?_⟩
  · rw [lg_wts σ τ prompt hσ hι, lg_wts σ τ prompt hσ (hτ _), if_pos rfl]
    split_ifs <;> norm_num
  · rw [lg_wts σ τ prompt hσ (lt_trans hι (hτ _)), lg_wts σ τ prompt hσ (hτ _),
      if_pos rfl, if_neg (Nat.ne_of_lt hι)]
    norm_num

/-! ## 3. The all-zero index -/

/-- all weights are 0 -/
def zeroW : Weights := ⟨fun _ => zeroLayer, fun _ _ => 0, fun _ _ => 0⟩

theorem zeroW_wf : zeroW.WF ppref := by
  refine ⟨fun L => ?_, fun t j => ?_, two_zero _ _⟩
  · split_ifs
    · exact zeroLayer_wf L
    · exact zeroLayer_isZero
  · show if t < 202048 ∧ j < 5120 then _ ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ _ else (0 : ℤ) = 0
    split_ifs <;> norm_num

theorem ok_zero : NORM.OK npR 5120 (fun _ => 0) := by
  refine ⟨?_, fun j _ => ?_⟩
  · simp [NORM.V]
  · unfold NORM.yw
    rw [zero_mul, rhu_zero (by norm_num)]
    exact fits16_zero

/-- The all-zero index answers every prompt with the token 0. -/
theorem model_zeroW : ModelIs ppref tbRef zeroW prompt 0 := by
  have hX : ∀ pos, X ppref tbRef zeroW prompt 0 pos = fun _ => 0 := fun pos => by
    funext j
    show (if h : pos < ppref.T then (0 : ℤ) else 0) = 0
    split_ifs <;> rfl
  have hlg : ∀ ι, lg ppref tbRef zeroW prompt (ppref.T - 1) ι = 0 := fun ι => dot_zero _ _
  refine ⟨runs_zero ppref tbRef _ _ prompt shifts_ref fun pos _ => ?_,
    by decide, fun ι _ => ?_,
    fun ι hι => absurd hι (Nat.not_lt_zero _)⟩
  · have e : X ppref tbRef ⟨fun _ => zeroLayer, fun _ _ => 0, fun _ _ => 0⟩ prompt 0 pos =
        fun _ => 0 := hX pos
    rw [e]
    exact ⟨ok_zero, ok_zero, ok_zero⟩
  · rw [hlg, hlg]

/-! ## 4. A well-formed index on which the program halts, whatever the prompt -/

/-- the row with 1,000 in all 5,120 channels -/
def cst : Vec := fun j => if j < 5120 then 1000 else 0

theorem V_cst : NORM.V 5120 cst = 5120000000 := by
  unfold NORM.V
  rw [sum_congr rfl fun j hj =>
      show cst j ^ 2 = 1000000 by rw [show cst j = 1000 from if_pos (mem_range.1 hj)]; norm_num]
  simp

theorem out_cst {j : ℕ} (hj : j < 5120) : NORM.out npR 5120 cst j = 229 := by
  unfold NORM.out NORM.yw NORM.R NORM.sig
  rw [V_cst, show cst j = 1000 from if_pos hj]
  decide +kernel

/-- layer 0: all entries of W_q are 4,095, the largest value of a two-byte weight (`Two`,
Inst/Model/Program.lean: "b0 + 256 b1 ∈ [−2^12, 2^12)"); everything else is 0 -/
def bigQ : LayerW := { zeroLayer with Wq := fun j c => if j < 5120 ∧ c < 5120 then 4095 else 0 }

/-- The index: every token has the embedding row (1,000, .., 1,000); layer 0 is bigQ; all else is
0. -/
def haltW : Weights :=
  ⟨fun L => if L = 0 then bigQ else zeroLayer,
    fun t j => if t < 202048 ∧ j < 5120 then 1000 else 0,
    fun _ _ => 0⟩

theorem bigQ_wf : bigQ.WF ppref 0 := by
  unfold LayerW.WF
  refine ⟨fun j c => ?_, two_zero _ _, two_zero _ _, two_zero _ _, ?_⟩
  · show if j < 5120 ∧ c < 5120 then
      _ ≤ (if j < 5120 ∧ c < 5120 then (4095 : ℤ) else 0) ∧
        (if j < 5120 ∧ c < 5120 then (4095 : ℤ) else 0) ≤ _
    else (if j < 5120 ∧ c < 5120 then (4095 : ℤ) else 0) = 0
    split_ifs <;> norm_num
  · rw [if_neg (by decide)]
    exact ⟨two_zero _ _, two_zero _ _, two_zero _ _, two_zero _ _,
      fun e => ⟨two_zero _ _, two_zero _ _, two_zero _ _⟩⟩

theorem haltW_wf : haltW.WF ppref := by
  refine ⟨fun L => ?_, fun t j => ?_, two_zero _ _⟩
  · show if L < ppref.layers then (if L = 0 then bigQ else zeroLayer).WF ppref L
    else (if L = 0 then bigQ else zeroLayer).IsZero
    by_cases h0 : L = 0
    · subst h0
      rw [if_pos (by decide), if_pos rfl]
      exact bigQ_wf
    · rw [if_neg h0]
      split_ifs
      · exact zeroLayer_wf L
      · exact zeroLayer_isZero
  · show if t < 202048 ∧ j < 5120 then
      _ ≤ (if t < 202048 ∧ j < 5120 then (1000 : ℤ) else 0) ∧
        (if t < 202048 ∧ j < 5120 then (1000 : ℤ) else 0) ≤ _
    else (if t < 202048 ∧ j < 5120 then (1000 : ℤ) else 0) = 0
    split_ifs <;> norm_num

/-- In layer 0, at the position 0, the quotient qkw of the first query channel is 36,631, which does
not fit 16 bits: step (PL5) halts. -/
theorem qkw_haltW : Att.qkw ppref tbRef bigQ 0 (X ppref tbRef haltW prompt 0) 0 0 = 36631 := by
  have hX : X ppref tbRef haltW prompt 0 0 = cst := by
    funext j
    show (if h : 0 < ppref.T then
          (if (prompt ⟨0, h⟩).val < 202048 ∧ j < 5120 then (1000 : ℤ) else 0)
        else 0) = _
    rw [dif_pos (by decide)]
    unfold cst
    by_cases hj : j < 5120
    · rw [if_pos ⟨(prompt _).2, hj⟩, if_pos hj]
    · rw [if_neg fun h => hj h.2, if_neg hj]
  have hA : Att.Aq ppref bigQ (X ppref tbRef haltW prompt 0) 0 0 = 4801305600 := by
    unfold Att.Aq Att.a dot
    rw [hX]
    show ∑ j ∈ range 5120,
        NORM.out npR 5120 cst j * (if j < 5120 ∧ 0 < 5120 then (4095 : ℤ) else 0) = _
    rw [sum_congr rfl fun j hj => show NORM.out npR 5120 cst j * (if j < 5120 ∧ 0 < 5120 then (4095 : ℤ) else 0) = 937755 by
      rw [out_cst (mem_range.1 hj), if_pos ⟨mem_range.1 hj, by norm_num⟩]; norm_num]
    simp
  have hC : tbRef.C 0 0 0 = 4096 := by decide +kernel
  have hS : tbRef.S 0 0 0 = 0 := by decide +kernel
  have hY : Att.Y' ppref tbRef bigQ 0 (X ppref tbRef haltW prompt 0) 0 0 = 4096 * 4801305600 := by
    have hAY : Att.AY ppref bigQ (X ppref tbRef haltW prompt 0) 0 0 = 4801305600 := by
      unfold Att.AY
      rw [if_pos (by decide), hA]
    unfold Att.Y'
    have h1 : 0 % ppref.ch = 0 := Nat.zero_mod _
    simp only [h1, Nat.zero_div, Nat.zero_mod, if_true, hC, hS, zero_mul, sub_zero, hAY]
  unfold Att.qkw
  rw [hY, if_pos (by decide)]
  decide +kernel

/-- The program halts on every prompt: no y is the output. So R_inf is not total: an index may have
an empty language. -/
theorem halts_haltW (y : ℕ) : ¬ ModelIs ppref tbRef haltW prompt y := by
  rintro ⟨⟨hL, -⟩, -⟩
  have h := ((hL 0 (by decide)).1 0 (by decide)).2.1 0 (by decide)
  have e : Att.qkw ppref tbRef (haltW.layer 0) 0 (X ppref tbRef haltW prompt (2 * 0)) 0 0 = 36631 :=
    qkw_haltW prompt
  rw [e] at h
  exact absurd h.2 (by norm_num)

end SanityRef
end Inst.Model

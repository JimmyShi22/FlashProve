-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/SanityExp.lean: the integer model at the reference parameters and tables depends on the
router and a routed expert. To audit the relation `RinfPP` (Inst/Model/Scales.lean), nothing of this
file need be read.

At `ppref` and `tbRef`. The index `wE r s` (well-formed for r, s < 128: `wE_wf`): embedding and
output matrix of Inst/Model/SanityAtt.lean; layer 1 (a layer with experts) is `layE r s`: the router
favours the expert r, only the expert s has weights, attention and the shared expert are zero; all
other layers are zero. For r < 128: on the prompt of 1,024 tokens 0 the routed expert adds 2,559 to
the channel 2 of the stream if r = s and nothing otherwise; the next token is 7 or 0.
    `lw_eq` .. `es_eq`, `xr_eq`, `hh_eq`, `ff_eq`, `ff_ok`
        the feed-forward block of `layE`, step by step: (R1) to (R6), UNIT, (PL12), (PL13)
        (labels: steps of Inst/Model/Program.lean);
        SIGM[2^15 + 64] = 36,848 and SILU[2^15 + 72] = 10 are read from `tbRef`
    `model_on`, `model_off`
        the whole program
    `sees_router`, `sees_expert`
        the title's two claims
Notation:
    `z`: `ℕ → Bool`; `z pos = true`: the position holds the token 0 (doc comment of `live`)
    `xs z`: `ℕ → Vec` (Inst/Model/SanityAtt.lean): `if z pos = true ∧ j = 0 then 2 ^ 20 else 0`
    `zz prompt`: `ℕ → Bool` (Inst/Model/SanityAtt.lean): `decide (tk prompt pos = 0)`
    `x2 r s z`: `ℕ → Vec`: `xs z pos c + if z pos = true ∧ r = s ∧ c = 2 then 2559 else 0`
    `tv m`: `Vec`: the row (2^20, 0, m, 0, ..)
    `FF.lw`, `FF.ly`, `FF.lr`, `FF.es`, `FF.xr`, `FF.hh` (Inst/Model/Program.lean): lw_e of (R1),
        ly_e of (R2), lr_e of (R3), e* of (R4), xr[j] of (R6), hh_j of (PL9), (PL11)
    `FF.kG`, `FF.kU` (Inst/Model/Program.lean): the first and the second shift of the hidden unit j
The indices are made up for these proofs. They say nothing on the weights of a trained model.
-/
import Inst.Model.SanityAtt

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Inst.Model
namespace SanityExp
open Finset SanityRef SanityAtt

section
variable (r s : ℕ)

/-- a layer with experts: the router favours the expert r; only the expert s has weights; attention
and the shared expert are zero -/
def layE : LayerW := { zeroLayer with
  Wr := fun j e => if j = 0 ∧ e = r then 4095 else 0
  Eg := fun e t j => if e = s ∧ t = 0 ∧ j < 8192 then 4095 else 0
  Eu := fun e t j => if e = s ∧ t = 0 ∧ j < 8192 then 4095 else 0
  Ed := fun e j c => if e = s ∧ j < 8192 ∧ c = 2 then 4095 else 0 }

variable (z : ℕ → Bool)

theorem m_eq (pos : ℕ) :
    FF.m ppref (xs z) pos = fun j => if z pos = true ∧ j = 0 then 2047 else 0 := a_eq z pos

theorem lw_eq (pos e : ℕ) :
    FF.lw ppref (layE r s) (xs z) pos e = if z pos = true ∧ e = r then 64 else 0 := by
  unfold FF.lw dot
  rw [m_eq]
  show rhu (∑ j ∈ range 5120,
        (if z pos = true ∧ j = 0 then (2047 : ℤ) else 0) * (if j = 0 ∧ e = r then 4095 else 0)) 17 =
    _
  rw [sum_eq_single 0 (fun j _ hj => by simp [hj]) (fun h => absurd (mem_range.2 (by norm_num)) h)]
  cases z pos <;> by_cases he : e = r <;> simp [he] <;> decide +kernel

theorem ly_eq (pos e : ℕ) :
    FF.ly ppref (layE r s) (xs z) pos e = if z pos = true ∧ e = r then 8 else 0 := by
  simp only [FF.ly, FF.l3, lw_eq]
  split_ifs <;> decide +kernel

theorem lr_eq (pos e : ℕ) :
    FF.lr ppref (layE r s) (xs z) pos e = if z pos = true ∧ e = r then 64 else 0 := by
  simp only [FF.lr, ly_eq, FF.l3, lw_eq]
  split_ifs <;> decide +kernel

theorem es_eq (hr : r < 128) (pos : ℕ) :
    FF.es ppref (layE r s) (xs z) pos = if z pos = true then r else 0 := by
  unfold FF.es
  obtain ⟨-, h1, h2⟩ := argTo_spec (FF.lr ppref (layE r s) (xs z) pos) (ppref.nexp - 1)
  generalize argTo (FF.lr ppref (layE r s) (xs z) pos) (ppref.nexp - 1) = a at *
  simp only [lr_eq] at h1 h2
  cases hz : z pos
  · simp only [hz] at h2
    by_contra hc
    have := h2 0 (Nat.pos_of_ne_zero (by simpa using hc))
    simp at this
  · have h3 := h1 r (show r ≤ 127 by omega)
    simp only [hz] at h3
    by_contra hc
    have hc' : ¬ a = r := by simpa using hc
    simp [hc'] at h3

theorem xr_eq (hr : r < 128) (pos : ℕ) :
    FF.xr ppref tbRef (layE r s) (xs z) pos =
      fun j => if z pos = true ∧ j = 0 then 1151 else 0 := by
  funext j
  unfold FF.xr FF.sc FF.mr
  rw [lr_eq, es_eq r s z hr, m_eq]
  cases z pos
  · simp
    exact rhu_zero (by norm_num)
  · by_cases hj : j = 0
    · simp [hj]
      decide +kernel
    · simp [hj]
      exact rhu_zero (by norm_num)

theorem routed_iff (j : ℕ) : FF.routed ppref 1 j ↔ 8192 ≤ j := by
  show (1 % 2 = 1 ∧ 8192 ≤ j) ↔ _
  simp

theorem kG_eq (j : ℕ) : FF.kG ppref 1 j = 16 := by unfold FF.kG; split_ifs <;> rfl
theorem kU_eq (j : ℕ) : FF.kU ppref 1 j = 20 := by unfold FF.kU; split_ifs <;> rfl

/-- the unit is live: the position holds the token 0, the unit is one of the routed expert, and the
router's expert is the one with weights -/
def live (pos j : ℕ) : Prop := z pos = true ∧ 8192 ≤ j ∧ r = s
instance (pos j : ℕ) : Decidable (live r s z pos j) := by unfold live; infer_instance

theorem dotg (hr : r < 128) (pos j : ℕ) (hj : j < 16384) :
    dot ppref.d (FF.z ppref tbRef (layE r s) 1 (xs z) pos j)
        (FF.wg ppref (layE r s) 1 (xs z) pos j) =
      if live r s z pos j then 1151 * 4095 else 0 := by
  unfold FF.z FF.wg live dot
  by_cases h : 8192 ≤ j
  · simp only [if_pos ((routed_iff j).2 h), xr_eq r s z hr, es_eq r s z hr]
    show ∑ t ∈ range 5120, (if z pos = true ∧ t = 0 then (1151 : ℤ) else 0) *
        (if (if z pos = true then r else 0) = s ∧ t = 0 ∧ j - 8192 < 8192 then 4095 else 0) = _
    rw [sum_eq_single 0 (fun t _ ht => by simp [ht])
        (fun h => absurd (mem_range.2 (by norm_num)) h)]
    have h3 : j - 8192 < 8192 := by omega
    by_cases hz : z pos = true <;> by_cases hrs : r = s <;> simp [hz, hrs, h, h3]
  · simp only [if_neg (fun hh => h ((routed_iff j).1 hh))]
    rw [if_neg (fun hh => h hh.2.1)]
    exact sum_eq_zero fun t _ => by simp [layE, zeroLayer]

theorem dotu (hr : r < 128) (pos j : ℕ) (hj : j < 16384) :
    dot ppref.d (FF.z ppref tbRef (layE r s) 1 (xs z) pos j)
        (FF.wu ppref (layE r s) 1 (xs z) pos j) =
      if live r s z pos j then 1151 * 4095 else 0 := by
  unfold FF.z FF.wu live dot
  by_cases h : 8192 ≤ j
  · simp only [if_pos ((routed_iff j).2 h), xr_eq r s z hr, es_eq r s z hr]
    show ∑ t ∈ range 5120, (if z pos = true ∧ t = 0 then (1151 : ℤ) else 0) *
        (if (if z pos = true then r else 0) = s ∧ t = 0 ∧ j - 8192 < 8192 then 4095 else 0) = _
    rw [sum_eq_single 0 (fun t _ ht => by simp [ht])
        (fun h => absurd (mem_range.2 (by norm_num)) h)]
    have h3 : j - 8192 < 8192 := by omega
    by_cases hz : z pos = true <;> by_cases hrs : r = s <;> simp [hz, hrs, h, h3]
  · simp only [if_neg (fun hh => h ((routed_iff j).1 hh))]
    rw [if_neg (fun hh => h hh.2.1)]
    exact sum_eq_zero fun t _ => by simp [layE, zeroLayer]

theorem hh_eq (hr : r < 128) (pos j : ℕ) (hj : j < 16384) :
    FF.hh ppref tbRef (layE r s) 1 (xs z) pos j = if live r s z pos j then 40 else 0 := by
  unfold FF.hh UNIT.hh UNIT.sl UNIT.gc UNIT.gh UNIT.g0 UNIT.gw UNIT.up
  rw [dotg r s z hr pos j hj, dotu r s z hr pos j hj, kG_eq, kU_eq]
  split_ifs <;> decide +kernel

theorem unit_ok (hr : r < 128) (pos j : ℕ) (hj : j < 16384) :
    UNIT.OK ppref.d (FF.z ppref tbRef (layE r s) 1 (xs z) pos j)
      (FF.wg ppref (layE r s) 1 (xs z) pos j) (FF.wu ppref (layE r s) 1 (xs z) pos j)
      (FF.kG ppref 1 j) (FF.kU ppref 1 j) := by
  unfold UNIT.OK UNIT.gh UNIT.g0 UNIT.gw UNIT.up Fits16
  rw [dotg r s z hr pos j hj, dotu r s z hr pos j hj, kG_eq, kU_eq]
  split_ifs <;> decide +kernel

def x2 : ℕ → Vec := fun pos c => xs z pos c + if z pos = true ∧ r = s ∧ c = 2 then 2559 else 0

theorem ff_eq (hr : r < 128) : FF.x'' ppref tbRef (layE r s) 1 (xs z) = x2 r s z := by
  funext pos c
  suffices key : rhu (FF.Ad ppref tbRef (layE r s) 1 (xs z) pos c) ppref.kd =
      if z pos = true ∧ r = s ∧ c = 2 then 2559 else 0 by
    unfold FF.x'' x2
    rw [key]
  unfold FF.Ad
  rw [ppref_readback.2.2.2.1]
  have hterm : ∀ j ∈ range 16384, FF.hh ppref tbRef (layE r s) 1 (xs z) pos j *
        (if FF.routed ppref 1 j then
            (layE r s).Ed (FF.es ppref (layE r s) (xs z) pos) (j - ppref.fe) c
          else (layE r s).Wd j c) =
      if 8192 ≤ j then (if z pos = true ∧ r = s ∧ c = 2 then 40 * 4095 else 0) else 0 := by
    intro j hj
    have hj' := mem_range.1 hj
    rw [hh_eq r s z hr pos j hj', es_eq r s z hr]
    unfold live
    by_cases h : 8192 ≤ j
    · rw [if_pos ((routed_iff j).2 h), if_pos h]
      show (if z pos = true ∧ 8192 ≤ j ∧ r = s then (40 : ℤ) else 0) *
          (if (if z pos = true then r else 0) = s ∧ j - 8192 < 8192 ∧ c = 2 then 4095 else 0) = _
      have h3 : j - 8192 < 8192 := by omega
      cases z pos <;> by_cases hrs : r = s <;> by_cases hc : c = 2 <;> simp [hrs, h, h3, hc]
    · rw [if_neg (fun hh => h hh.2.1), if_neg h, zero_mul]
  rw [sum_congr rfl hterm, show (16384 : ℕ) = 8192 + 8192 from rfl, sum_range_add,
    sum_eq_zero (fun j hj => if_neg (by have := mem_range.1 hj; omega)),
    sum_congr rfl (fun j _ => if_pos (Nat.le_add_right 8192 j)), sum_const,
      card_range, nsmul_eq_mul, zero_add]
  show rhu _ 19 = _
  split_ifs <;> decide +kernel

theorem ok_x2 (pos : ℕ) : NORM.OK npR 5120 (x2 r s z pos) :=
  norm_ok_of_le _ fun j _ => by
    unfold x2 xs
    split_ifs <;> omega

theorem ff_ok (hr : r < 128) : FF.OK ppref tbRef (layE r s) 1 (xs z) := fun i _ =>
  ⟨ok_xs z i, fun _ e _ => by
    rw [ly_eq]
    unfold Fits16
    split_ifs <;> norm_num,
      fun j hj => unit_ok r s z hr i j (by rwa [ppref_readback.2.2.2.1] at hj)⟩

theorem att_layE (x : ℕ → Vec) : Att.x' ppref tbRef (layE r s) 1 x = x := by
  funext i c
  simp [Att.x', layE, zeroLayer, dot_zero, rhu_zero (show 1 ≤ ppref.ko by decide)]

theorem att_ok_layE (x : ℕ → Vec) (hx : ∀ i < ppref.T, NORM.OK ppref.n1 ppref.d (x i)) :
    Att.OK ppref tbRef (layE r s) 1 x := by
  have h1 : ∀ i c, Att.qkw ppref tbRef (layE r s) 1 x i c = 0 := by
    intro i c
    have hA : ∀ c', Att.AY ppref (layE r s) x i c' = 0 := by
      intro c'
      simp [Att.AY, Att.Aq, Att.Ak, layE, zeroLayer, dot_zero]
    simp only [Att.qkw, Att.Y', hA, mul_zero, sub_zero, add_zero, ite_self]
    split_ifs
    · exact rhu_zero (by decide)
    · exact rhu_zero (by decide)
  have h2 : ∀ i c, Att.vw ppref (layE r s) x i c = 0 := by
    intro i c
    simp [Att.vw, Att.Av, layE, zeroLayer, dot_zero, rhu_zero (show 1 ≤ ppref.kv by decide)]
  exact fun i hi =>
    ⟨hx i hi, fun c _ => by rw [h1]; exact fits16_zero, fun c _ => by rw [h2]; exact fits16_zero⟩

/-- The index: layer 1 is `layE r s`, all other layers are zero; embedding and output matrix as in
Inst/Model/SanityAtt.lean (`embA`, `headA`) -/
def wE : Weights := ⟨fun L => if L = 1 then layE r s else zeroLayer, embA, headA⟩

theorem layE_wf (hr : r < 128) (hs : s < 128) : (layE r s).WF ppref 1 := by
  unfold LayerW.WF
  refine ⟨SanityRef.two_zero _ _, SanityRef.two_zero _ _, SanityRef.two_zero _ _,
    SanityRef.two_zero _ _, ?_⟩
  rw [if_pos (by decide)]
  refine ⟨SanityRef.two_zero _ _, SanityRef.two_zero _ _, SanityRef.two_zero _ _,
    fun j e => ?_, fun e => ?_⟩
  · show if j < 5120 ∧ e < 128 then
      _ ≤ (if j = 0 ∧ e = r then (4095 : ℤ) else 0) ∧ (if j = 0 ∧ e = r then (4095 : ℤ) else 0) ≤ _
    else (if j = 0 ∧ e = r then (4095 : ℤ) else 0) = 0
    split_ifs <;> omega
  · show if e < 128 then _ else _
    split_ifs with he
    · refine ⟨fun t j => ?_, fun t j => ?_, fun j c => ?_⟩
      · show if t < 5120 ∧ j < 8192 then
          _ ≤ (if e = s ∧ t = 0 ∧ j < 8192 then (4095 : ℤ) else 0) ∧
            (if e = s ∧ t = 0 ∧ j < 8192 then (4095 : ℤ) else 0) ≤ _
        else (if e = s ∧ t = 0 ∧ j < 8192 then (4095 : ℤ) else 0) = 0
        split_ifs <;> omega
      · show if t < 5120 ∧ j < 8192 then
          _ ≤ (if e = s ∧ t = 0 ∧ j < 8192 then (4095 : ℤ) else 0) ∧
            (if e = s ∧ t = 0 ∧ j < 8192 then (4095 : ℤ) else 0) ≤ _
        else (if e = s ∧ t = 0 ∧ j < 8192 then (4095 : ℤ) else 0) = 0
        split_ifs <;> omega
      · show if j < 8192 ∧ c < 5120 then
          _ ≤ (if e = s ∧ j < 8192 ∧ c = 2 then (4095 : ℤ) else 0) ∧
            (if e = s ∧ j < 8192 ∧ c = 2 then (4095 : ℤ) else 0) ≤ _
        else (if e = s ∧ j < 8192 ∧ c = 2 then (4095 : ℤ) else 0) = 0
        split_ifs <;> omega
    · refine ⟨fun t j => ?_, fun t j => ?_, fun j c => ?_⟩
      · show if t < 0 ∧ j < 0 then _ else (if e = s ∧ t = 0 ∧ j < 8192 then (4095 : ℤ) else 0) = 0
        split_ifs <;> omega
      · show if t < 0 ∧ j < 0 then _ else (if e = s ∧ t = 0 ∧ j < 8192 then (4095 : ℤ) else 0) = 0
        split_ifs <;> omega
      · show if j < 0 ∧ c < 0 then _ else (if e = s ∧ j < 8192 ∧ c = 2 then (4095 : ℤ) else 0) = 0
        split_ifs <;> omega

theorem wE_wf (hr : r < 128) (hs : s < 128) : (wE r s).WF ppref := by
  refine ⟨fun L => ?_, embA_box, headA_two⟩
  show if L < ppref.layers then (if L = 1 then layE r s else zeroLayer).WF ppref L
  else (if L = 1 then layE r s else zeroLayer).IsZero
  by_cases h0 : L = 1
  · subst h0
    rw [if_pos (by decide), if_pos rfl]
    exact layE_wf r s hr hs
  · rw [if_neg h0]
    split_ifs
    · exact zeroLayer_wf L
    · exact zeroLayer_isZero

variable (prompt : Fin ppref.T → Fin ppref.V)

theorem X_lo (l : ℕ) (hl : l ≤ 3) : X ppref tbRef (wE r s) prompt l = xs (zz prompt) := by
  induction l with
  | zero => exact X0_eq prompt _
  | succ l ih =>
    rw [X_succ, ih (by omega)]
    by_cases h2 : l = 2
    · subst h2
      rw [if_pos (by decide)]
      exact att_layE r s _
    · have hL : (wE r s).layer (l / 2) = zeroLayer := if_neg (by omega)
      rw [hL]
      split_ifs
      · exact att_zero ppref tbRef _ _ (by decide)
      · exact ff_zero ppref tbRef _ _ (by decide)

theorem X_hi (hr : r < 128) (l : ℕ) :
    X ppref tbRef (wE r s) prompt (l + 4) = x2 r s (zz prompt) := by
  induction l with
  | zero =>
    rw [show 0 + 4 = 3 + 1 from rfl, X_succ, X_lo r s prompt 3 le_rfl, if_neg (by decide)]
    exact ff_eq r s _ hr
  | succ l ih =>
    rw [show l + 1 + 4 = (l + 4) + 1 from rfl, X_succ, ih]
    have hL : (wE r s).layer ((l + 4) / 2) = zeroLayer := if_neg (by omega)
    rw [hL]
    split_ifs
    · exact att_zero ppref tbRef _ _ (by decide)
    · exact ff_zero ppref tbRef _ _ (by decide)

theorem runs_wE (hr : r < 128) : Runs ppref tbRef (wE r s) prompt := by
  refine ⟨fun L _ => ⟨?_, ?_⟩, fun pos _ => ?_⟩
  · rcases Nat.lt_or_ge L 2 with h | h
    · rw [X_lo r s prompt (2 * L) (by omega)]
      by_cases h1 : L = 1
      · subst h1
        exact att_ok_layE r s _ fun i _ => ok_xs _ i
      · rw [show (wE r s).layer L = zeroLayer from if_neg h1]
        exact (att_ok_zero ppref tbRef L _ (by decide) (by decide) (by decide)).2
          fun i _ => ok_xs _ i
    · rw [show 2 * L = (2 * L - 4) + 4 by omega, X_hi r s prompt hr,
        show (wE r s).layer L = zeroLayer from if_neg (by omega)]
      exact (att_ok_zero ppref tbRef L _ (by decide) (by decide) (by decide)).2
        fun i _ => ok_x2 r s _ i
  · rcases Nat.lt_or_ge L 2 with h | h
    · rw [X_lo r s prompt (2 * L + 1) (by omega)]
      by_cases h1 : L = 1
      · subst h1
        exact ff_ok r s _ hr
      · rw [show (wE r s).layer L = zeroLayer from if_neg h1]
        exact (ff_ok_zero ppref tbRef L _ (by decide) (by decide) (by decide)
            (by decide) (by decide)).2
          fun i _ => ok_xs _ i
    · rw [show 2 * L + 1 = (2 * L - 3) + 4 by omega, X_hi r s prompt hr,
        show (wE r s).layer L = zeroLayer from if_neg (by omega)]
      exact (ff_ok_zero ppref tbRef L _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).2
        fun i _ => ok_x2 r s _ i
  · have e : X ppref tbRef (wE r s) prompt (2 * ppref.layers) = x2 r s (zz prompt) :=
      X_hi r s prompt hr 92
    rw [e]
    exact ok_x2 r s _ pos

theorem lg_wE (hr : r < 128) (ι : ℕ) :
    lg ppref tbRef (wE r s) prompt (ppref.T - 1) ι =
      NORM.out npR 5120 (x2 r s (zz prompt) 1023) 2 * (if ι = 7 then 1 else 0) := by
  have e : X ppref tbRef (wE r s) prompt (2 * ppref.layers) = x2 r s (zz prompt) :=
    X_hi r s prompt hr 92
  unfold lg nrm dot
  rw [e]
  show ∑ j ∈ range 5120,
      NORM.out npR 5120 (x2 r s (zz prompt) 1023) j * (if j = 2 ∧ ι = 7 then 1 else 0) = _
  rw [sum_eq_single 2 (fun j _ hj => by simp [hj]) (fun h => absurd (mem_range.2 (by norm_num)) h)]
  simp
end

/-! ## The normalisation of the row (2^20, 0, m, 0, ..) -/
def tv (m : ℤ) : Vec := fun c => (if c = 0 then 2 ^ 20 else 0) + (if c = 2 then m else 0)

theorem V_tv (m : ℤ) : NORM.V 5120 (tv m) = 2 ^ 40 + m ^ 2 := by
  unfold NORM.V
  have h : ∀ j ∈ range 5120,
      tv m j ^ 2 = (if j = 0 then 2 ^ 40 else 0) + (if j = 2 then m ^ 2 else 0) := by
    intro j _
    unfold tv
    by_cases h0 : j = 0
    · subst h0; norm_num
    · by_cases h2 : j = 2
      · subst h2; norm_num
      · simp [h0, h2]
  rw [sum_congr rfl h, sum_add_distrib, sum_ite_eq', sum_ite_eq',
    if_pos (mem_range.2 (by norm_num)), if_pos (mem_range.2 (by norm_num))]

theorem out_tv (m : ℤ) :
    NORM.out npR 5120 (tv m) 2 =
      clamp 2047
        (rhu (m * ((2 ^ 44 + isqrt (2 ^ 40 + m ^ 2 + 53687) / 2) / isqrt (2 ^ 40 + m ^ 2 + 53687)))
          30) := by
  unfold NORM.out NORM.yw NORM.R NORM.sig
  rw [V_tv]
  simp [tv]

theorem out_tv_big : NORM.out npR 5120 (tv 2559) 2 = 40 := by rw [out_tv]; decide +kernel
theorem out_tv_zero : NORM.out npR 5120 (tv 0) 2 = 0 := by rw [out_tv]; decide +kernel

/-- the token 0 everywhere -/
def pC : Fin ppref.T → Fin ppref.V := fun _ => t0

theorem zz_pC : zz pC 1023 = true := by
  unfold zz tk pC
  rw [dif_pos (by decide)]
  simp [t0]

theorem x2_pC (r s : ℕ) : x2 r s (zz pC) 1023 = tv (if r = s then 2559 else 0) := by
  funext c
  unfold x2 xs tv
  rw [zz_pC]
  by_cases h : r = s <;> simp [h]

theorem model_on (r : ℕ) (hr : r < 128) : ModelIs ppref tbRef (wE r r) pC 7 := by
  refine ⟨runs_wE r r pC hr, show 7 < 202048 by norm_num, fun ι _ => ?_, fun ι hι => ?_⟩
  · rw [lg_wE r r pC hr, lg_wE r r pC hr, x2_pC, if_pos rfl, out_tv_big, if_pos rfl]
    split_ifs <;> norm_num
  · rw [lg_wE r r pC hr, lg_wE r r pC hr, x2_pC, if_pos rfl, out_tv_big, if_neg (Nat.ne_of_lt hι)]
    norm_num

theorem model_off (r s : ℕ) (hr : r < 128) (h : r ≠ s) : ModelIs ppref tbRef (wE r s) pC 0 := by
  refine ⟨runs_wE r s pC hr, show 0 < 202048 by norm_num, fun ι _ => ?_,
    fun ι hι => absurd hι (Nat.not_lt_zero _)⟩
  rw [lg_wE r s pC hr, lg_wE r s pC hr, x2_pC, if_neg h, out_tv_zero]
  norm_num

/-- R_inf (`Rinf ppref tbRef`, Inst/Model/Program.lean) depends on the router: two well-formed
indices that differ in W_r of layer 1 only answer one prompt differently. -/
theorem sees_router : ∃ (i i' : Index ppref) (p : Fin ppref.T → Fin ppref.V) (y y' : ℕ),
    i.val.Emb = i'.val.Emb ∧ i.val.H = i'.val.H ∧ (∀ L, L ≠ 1 → i.val.layer L = i'.val.layer L) ∧
    { i.val.layer 1 with Wr := (i'.val.layer 1).Wr } = i'.val.layer 1 ∧
    y ≠ y' ∧ ModelIs ppref tbRef i.val p y ∧ ModelIs ppref tbRef i'.val p y' :=
  ⟨⟨wE 5 5, wE_wf 5 5 (by norm_num) (by norm_num)⟩,
    ⟨wE 6 5, wE_wf 6 5 (by norm_num) (by norm_num)⟩, pC, 7, 0, rfl, rfl,
    fun L hL => by
      show (if L = 1 then _ else _) = (if L = 1 then _ else _); rw [if_neg hL, if_neg hL],
    rfl, by decide, model_on 5 (by norm_num), model_off 6 5 (by norm_num) (by norm_num)⟩

/-- R_inf (`Rinf ppref tbRef`, Inst/Model/Program.lean) depends on the routed experts: two
well-formed indices that differ in the matrices of the routed experts of layer 1 only answer one
prompt differently. -/
theorem sees_expert :
    ∃ (i i' : Index ppref) (p : Fin ppref.T → Fin ppref.V) (y y' : ℕ),
      i.val.Emb = i'.val.Emb ∧
      i.val.H = i'.val.H ∧
      (∀ L, L ≠ 1 → i.val.layer L = i'.val.layer L) ∧
      { i.val.layer 1 with
        Eg := (i'.val.layer 1).Eg, Eu := (i'.val.layer 1).Eu, Ed := (i'.val.layer 1).Ed } =
        i'.val.layer 1 ∧
      y ≠ y' ∧
      ModelIs ppref tbRef i.val p y ∧
      ModelIs ppref tbRef i'.val p y' :=
  ⟨⟨wE 5 5, wE_wf 5 5 (by norm_num) (by norm_num)⟩,
    ⟨wE 5 6, wE_wf 5 6 (by norm_num) (by norm_num)⟩, pC, 7, 0, rfl, rfl,
    fun L hL => by
      show (if L = 1 then _ else _) = (if L = 1 then _ else _); rw [if_neg hL, if_neg hL],
    rfl, by decide, model_on 5 (by norm_num), model_off 5 6 (by norm_num) (by norm_num)⟩

end SanityExp
end Inst.Model

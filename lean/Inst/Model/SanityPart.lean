-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/SanityPart.lean: the integer model at the reference parameters and tables: one index, a
prompt on which the program runs and a prompt on which it halts. To audit the relation `RinfPP`
(Inst/Model/Scales.lean), nothing of this file need be read.

At `ppref` and `tbRef`. The index `wP`: the token 1 is embedded as (1,000, .., 1,000), every other
token as the zero row; layer 0 is `SanityRef.bigQ` (all entries of W_q are 4,095); all else is 0. On
the prompt of 1,024 tokens 0 nothing halts and the next token is 0; on the prompt of 1,024 tokens
1 step (PL5) of Inst/Model/Program.lean halts at the position 0.
    `partial_index`   the title's statement
Notation:
  index: `Index ppref` (Inst/Model/Program.lean): the type of indices: the well-formed weights.
  well-formed: `Weights.WF`; `Weights`: the weight tensors, as integers, independent of any layout
    (both Inst/Model/Program.lean).
  `ppref`: `Params`; the reference parameters (Inst/Model/Program.lean).
  `pC`: a prompt: the token 0 everywhere; `pB` (Inst/Model/SanityAtt.lean): the token 1 everywhere.
The index is made up for these proofs. It says nothing on the weights of a trained model.
-/
import Inst.Model.SanityAtt

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Inst.Model
namespace SanityPart
open Finset SanityRef SanityAtt

/-- the token 1 is embedded as (1,000, .., 1,000), every other token as the zero row -/
def embP : Mat := fun t j => if t = 1 ∧ j < 5120 then 1000 else 0
/-- the embedding is `embP`; layer 0 is `bigQ` of Inst/Model/SanityRef.lean (all entries of W_q are
4,095); everything else is 0 -/
def wP : Weights := ⟨fun L => if L = 0 then bigQ else zeroLayer, embP, fun _ _ => 0⟩

theorem wP_wf : wP.WF ppref := by
  refine ⟨fun L => ?_, fun t j => ?_, SanityRef.two_zero _ _⟩
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
      _ ≤ (if t = 1 ∧ j < 5120 then (1000 : ℤ) else 0) ∧
        (if t = 1 ∧ j < 5120 then (1000 : ℤ) else 0) ≤ _
    else (if t = 1 ∧ j < 5120 then (1000 : ℤ) else 0) = 0
    split_ifs <;> omega

def zs : ℕ → Vec := fun _ _ => 0

theorem att_bigQ (x : ℕ → Vec) : Att.x' ppref tbRef bigQ 0 x = x := by
  funext i c
  simp [Att.x', bigQ, zeroLayer, dot_zero, rhu_zero (show 1 ≤ ppref.ko by decide)]

theorem att_ok_bigQ : Att.OK ppref tbRef bigQ 0 zs := by
  have ha : ∀ i, Att.a ppref zs i = fun _ => 0 := fun i => funext out_zero
  have h1 : ∀ i c, Att.qkw ppref tbRef bigQ 0 zs i c = 0 := by
    intro i c
    have hA : ∀ c', Att.AY ppref bigQ zs i c' = 0 := by
      intro c'
      simp [Att.AY, Att.Aq, Att.Ak, ha, dot]
    simp only [Att.qkw, Att.Y', hA, mul_zero, sub_zero, add_zero, ite_self]
    split_ifs
    · exact rhu_zero (by decide)
    · exact rhu_zero (by decide)
  have h2 : ∀ i c, Att.vw ppref bigQ zs i c = 0 := by
    intro i c
    simp [Att.vw, Att.Av, ha, dot, rhu_zero (show 1 ≤ ppref.kv by decide)]
  exact fun i _ =>
    ⟨ok_zero, fun c _ => by rw [h1]; exact fits16_zero, fun c _ => by rw [h2]; exact fits16_zero⟩

theorem ff_bigQ (x : ℕ → Vec) : FF.x'' ppref tbRef bigQ 0 x = x := by
  funext i c
  simp [FF.x'', FF.Ad, bigQ, zeroLayer, rhu_zero (show 1 ≤ ppref.kd by decide)]

theorem ff_ok_bigQ (x : ℕ → Vec) (hx : ∀ i < ppref.T, NORM.OK ppref.n2 ppref.d (x i)) :
    FF.OK ppref tbRef bigQ 0 x := by
  have hkG : ∀ j, 1 ≤ FF.kG ppref 0 j := by intro j; unfold FF.kG; split_ifs <;> decide
  have hkU : ∀ j, 1 ≤ FF.kU ppref 0 j := by intro j; unfold FF.kU; split_ifs <;> decide
  have hwg : ∀ i j, FF.wg ppref bigQ 0 x i j = fun _ => 0 := by
    intro i j; funext t; simp [FF.wg, bigQ, zeroLayer]
  have hwu : ∀ i j, FF.wu ppref bigQ 0 x i j = fun _ => 0 := by
    intro i j; funext t; simp [FF.wu, bigQ, zeroLayer]
  have h2 : ∀ i j,
      UNIT.OK ppref.d (FF.z ppref tbRef bigQ 0 x i j) (FF.wg ppref bigQ 0 x i j)
        (FF.wu ppref bigQ 0 x i j) (FF.kG ppref 0 j) (FF.kU ppref 0 j) := by
    intro i j
    simp only [UNIT.OK, UNIT.gh, UNIT.g0, UNIT.gw, UNIT.up, hwg, hwu, dot_zero, rhu_zero (hkG j),
      rhu_zero (hkU j), lowByte]
    refine ⟨by norm_num, fits16_zero⟩
  exact fun i hi => ⟨hx i hi, fun h => absurd h (by decide), fun j _ => h2 i j⟩

/-- the token 0 everywhere -/
def pC : Fin ppref.T → Fin ppref.V := fun _ => t0

theorem X_pC (l : ℕ) : X ppref tbRef wP pC l = zs := by
  induction l with
  | zero =>
    funext pos j
    show (if h : pos < ppref.T then embP (pC ⟨pos, h⟩) j else 0) = 0
    split_ifs
    · simp [embP, pC, t0]
    · rfl
  | succ l ih =>
    rw [X_succ, ih]
    by_cases h0 : l / 2 = 0
    · rw [h0, show wP.layer 0 = bigQ from rfl]
      split_ifs
      · exact att_bigQ _
      · exact ff_bigQ _
    · rw [show wP.layer (l / 2) = zeroLayer from if_neg h0]
      split_ifs
      · exact att_zero ppref tbRef _ _ (by decide)
      · exact ff_zero ppref tbRef _ _ (by decide)

theorem model_pC : ModelIs ppref tbRef wP pC 0 := by
  refine ⟨⟨fun L _ => ⟨?_, ?_⟩, fun pos _ => ?_⟩,
    show 0 < 202048 by norm_num,
    fun ι _ => ?_,
    fun ι hι => absurd hι (Nat.not_lt_zero _)⟩
  · rw [X_pC]
    by_cases h0 : L = 0
    · subst h0
      exact att_ok_bigQ
    · rw [show wP.layer L = zeroLayer from if_neg h0]
      exact (att_ok_zero ppref tbRef L _ (by decide) (by decide) (by decide)).2 fun i _ => ok_zero
  · rw [X_pC]
    by_cases h0 : L = 0
    · subst h0
      exact ff_ok_bigQ _ fun i _ => ok_zero
    · rw [show wP.layer L = zeroLayer from if_neg h0]
      exact (ff_ok_zero ppref tbRef L _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).2
        fun i _ => ok_zero
  · rw [X_pC]
    exact ok_zero
  · have hlg : ∀ ι, lg ppref tbRef wP pC (ppref.T - 1) ι = 0 := fun ι => dot_zero _ _
    rw [hlg, hlg]

/-- `SanityRef.qkw_haltW` for a variable stream: for any stream whose row at the position 0 is
(1,000, .., 1,000) (`cst`): in layer 0, with the weights `bigQ`, at the position 0, the quotient qkw
of the first query channel is 36,631 -/
theorem qkw_cst (x : ℕ → Vec) (hX : x 0 = cst) : Att.qkw ppref tbRef bigQ 0 x 0 0 = 36631 := by
  have hA : Att.Aq ppref bigQ x 0 0 = 4801305600 := by
    unfold Att.Aq Att.a dot
    rw [hX]
    show ∑ j ∈ range 5120,
        NORM.out npR 5120 cst j * (if j < 5120 ∧ 0 < 5120 then (4095 : ℤ) else 0) = _
    rw [sum_congr rfl fun j hj => show NORM.out npR 5120 cst j * (if j < 5120 ∧ 0 < 5120 then (4095 : ℤ) else 0) = 937755 by
      rw [out_cst (mem_range.1 hj), if_pos ⟨mem_range.1 hj, by norm_num⟩]; norm_num]
    simp
  have hC : tbRef.C 0 0 0 = 4096 := by decide +kernel
  have hS : tbRef.S 0 0 0 = 0 := by decide +kernel
  have hY : Att.Y' ppref tbRef bigQ 0 x 0 0 = 4096 * 4801305600 := by
    have hAY : Att.AY ppref bigQ x 0 0 = 4801305600 := by
      unfold Att.AY
      rw [if_pos (by decide), hA]
    unfold Att.Y'
    have h1 : 0 % ppref.ch = 0 := Nat.zero_mod _
    simp only [h1, Nat.zero_div, Nat.zero_mod, if_true, hC, hS, zero_mul, sub_zero, hAY]
  unfold Att.qkw
  rw [hY, if_pos (by decide)]
  decide +kernel

theorem halts_pB (y : ℕ) : ¬ ModelIs ppref tbRef wP pB y := by
  rintro ⟨⟨hL, -⟩, -⟩
  have h := ((hL 0 (by decide)).1 0 (by decide)).2.1 0 (by decide)
  have hX : X ppref tbRef wP pB (2 * 0) 0 = cst := by
    funext j
    show (if h : 0 < ppref.T then embP (pB ⟨0, h⟩) j else 0) = _
    rw [dif_pos (by decide)]
    simp [embP, pB, t1, cst]
  have e : Att.qkw ppref tbRef (wP.layer 0) 0 (X ppref tbRef wP pB (2 * 0)) 0 0 = 36631 :=
    qkw_cst _ hX
  rw [e] at h
  exact absurd h.2 (by norm_num)

/-- Model_i is a properly partial function: one well-formed index with an output on one prompt and
none on another. -/
theorem partial_index :
    ∃ (i : Index ppref) (p p' : Fin ppref.T → Fin ppref.V),
      (∃ y, ModelIs ppref tbRef i.val p y) ∧ ∀ y, ¬ ModelIs ppref tbRef i.val p' y :=
  ⟨⟨wP, wP_wf⟩, pC, pB, ⟨0, model_pC⟩, halts_pB⟩

end SanityPart
end Inst.Model

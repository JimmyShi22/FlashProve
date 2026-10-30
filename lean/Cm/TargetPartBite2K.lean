-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPartBite2K.lean: a guard: the index matters at every lawful table of scales, and "the
proofs hide the index" has two different models to hide between. Two indices i, i' and two requests
x, x', the same four for all tables, such that at every lawful s: x is true at both indices; x' is
true at i and false at i'.

Definitions, statements (`Cm.Spec.target_bite2_norm`, `target_bite2_pos`, `target_bite2_all`) and
proofs. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs. No cells, no code, no protocol, no chance.
"True" is `PaperTrue` (Cm/RelTruePaper.lean); the head of Cm/TargetPartBite2.lean tells it in
words.

Why: in another file "the index matters" stands at the reference scales alone
(Cm/TargetPartBite2.lean: `target_bite2_ref`), and the indices
that share a true request at every lawful table (`target_bite2_many`) have one language.


Main names:
  `biteW σ τ`: made-up weights after `wts` (Inst/Model/SanityRef.lean), with 2^24 for its 2^20.
  `Spec.target_bite2_norm`: the one fact on the program's arithmetic: for every normalisation's
    parameters within the lawful ranges (1 ≤ ϵ < 2^48, 24 ≤ M ≤ 47, 17 ≤ K ≤ 32, M ≤ K + 14) with
    K ≤ M, and every channel c < 5,120: the normalisation of `biteRow c` passes its two range
    tests; its output is at least 1 in the channel c and 0 elsewhere.
  `Spec.target_bite2_pos`: the analogue at every lawful table of `true_pos`, Cm/RelTrue.lean, which
    is at the reference scales, `ppRef`.
  `Spec.target_bite2_all`: the title's second sentence.






Why 2^24: the constant ϵ under the root may be anything below 2^48, and the reciprocal's exponent M
may be as small as 24: a smaller entry may be normalised to 0 where ϵ is large, a larger one where
M is small. At 2^24 the root lies in [2^24, 2^25) (in truth below 2^24.5: the bound used is
coarse), so the reciprocal is at least 2^(M - 25) (at least 1 at M = 24), the product at least
2^(M - 1), and, since K ≤ M is a clause of "lawful" (`Scales.Lawful`, Cm/Rel2.lean), the shift by K
leaves at least 1.

Limits: all indices are made up: all layers are zero: nothing here passes through attention or a
feed-forward block. This file says nothing on real weights. It does not say that a lawful table is
sensible. It does not say anything on a protocol.
Terms: lean/GLOSSARY.md.
-/
import Cm.TargetPartBite2

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Inst.Model.ScalesSanity Inst.Model.ProgramRGuards
  Inst.Model.SanityRef Finset

/-- the row with 2^24 in the channel c -/
def biteRow (c : ℕ) : Vec := fun j => if j = c then 2 ^ 24 else 0

/-- token t is embedded as biteRow (σ t) -/
def biteEmb (σ : ℕ → ℕ) : Mat := fun t j => if t < 202048 ∧ j < 5120 then biteRow (σ t) j else 0

/-- made-up weights: all layers zero; token t in the channel σ t; channel j votes for the token
τ j -/
def biteW (σ τ : ℕ → ℕ) : Weights := ⟨fun _ => layW 0, biteEmb σ, headOf τ⟩

theorem biteEmb_box (σ : ℕ → ℕ) :
    Box ppref.V ppref.d (-2155905152) 2139062143 (biteEmb σ) := fun t j => by
  show if t < 202048 ∧ j < 5120 then _ ≤ biteEmb σ t j ∧ biteEmb σ t j ≤ _ else biteEmb σ t j = 0
  unfold biteEmb biteRow
  split_ifs <;> norm_num

theorem biteW_wf (σ τ : ℕ → ℕ) : (biteW σ τ).WF ppref :=
  ⟨(iW_wf (vs := fun _ => 0) (fun _ => by norm_num) (fun _ _ => rfl) (biteEmb_box σ)).1,
    biteEmb_box σ, (wts_wf σ τ).2.2⟩

/-- the index that holds these weights -/
def biteI (σ τ : ℕ → ℕ) : Idx := Idx.ofIndex ⟨biteW σ τ, biteW_wf σ τ⟩

namespace Spec

/-- the normalisation of `biteRow c` at all lawful parameters (`np.OK`, K ≤ M) and c < 5120: it
passes its tests; at least 1 in the channel c, 0 elsewhere -/
def target_bite2_norm : Prop :=
  ∀ (np : NormPar) (c : ℕ), np.OK → np.K ≤ np.M → c < 5120 →
    NORM.OK np 5120 (biteRow c) ∧
    1 ≤ NORM.out np 5120 (biteRow c) c ∧
    ∀ j, j ≠ c → NORM.out np 5120 (biteRow c) j = 0

/-- what is true at these weights, at every lawful table. (not all hypotheses are named here: see
the statement below) -/
def target_bite2_pos : Prop :=
  ∀ s : Scales, s.Lawful →
    ∀ σ τ : ℕ → ℕ, (∀ t, σ t < 5120) → (∀ j, τ j < 202048) →
      ∀ x : Instance ppref,
        PaperTrue s.kap s.nf (biteI σ τ) x ↔
        Head3 x ∧ ∀ t (ht : t < ppref.T), x.r ≤ t → t < x.e → x.w t = τ (σ (x.prompt ⟨t, ht⟩))

/-- The index matters at every lawful table; two different models answer one request alike: the
same four for all tables. -/
def target_bite2_all : Prop :=
  ∃ (i i' : Idx) (x x' : Instance ppref), ∀ s : Scales, s.Lawful →
    PaperTrue s.kap s.nf i x ∧ PaperTrue s.kap s.nf i' x ∧
    PaperTrue s.kap s.nf i x' ∧ ¬ PaperTrue s.kap s.nf i' x'

end Spec

/-! ## The normalisation -/

theorem biteRow_V {c : ℕ} (hc : c < 5120) : NORM.V 5120 (biteRow c) = 2 ^ 48 := by
  unfold NORM.V
  rw [sum_eq_single c (fun j _ hj => by simp [biteRow, hj]) (fun h => absurd (mem_range.2 hc) h)]
  simp [biteRow]

theorem biteRow_sig (np : NormPar) {c : ℕ} (h : np.OK) (hc : c < 5120) :
    2 ^ 24 ≤ NORM.sig np 5120 (biteRow c) ∧ NORM.sig np 5120 (biteRow c) < 2 ^ 25 := by
  unfold NORM.sig isqrt
  rw [biteRow_V hc]
  obtain ⟨h1, h2, -⟩ := h
  have hn1 : 2 ^ 24 * 2 ^ 24 ≤ ((2 : ℤ) ^ 48 + np.eps).toNat := by omega
  have hn2 : ((2 : ℤ) ^ 48 + np.eps).toNat < 2 ^ 25 * 2 ^ 25 := by omega
  have a := Nat.le_sqrt.2 hn1
  have b := Nat.sqrt_lt.2 hn2
  constructor
  · exact_mod_cast a
  · exact_mod_cast b

/-- pure arithmetic: the reciprocal, the product, the shift -/
theorem bite_arith (M K : ℕ) (g : ℤ) (hM : 24 ≤ M) (hK : 17 ≤ K) (hKM : K ≤ M) (hMK : M ≤ K + 14)
    (g1 : 2 ^ 24 ≤ g) (g2 : g < 2 ^ 25) :
    1 ≤ rhu (2 ^ 24 * ((2 ^ M + g / 2) / g)) K ∧
    rhu (2 ^ 24 * ((2 ^ M + g / 2) / g)) K < 2 ^ 15 := by
  have gpos : 0 < g := by omega
  set R : ℤ := (2 ^ M + g / 2) / g with hR
  -- lower bound on R
  have hlow : (2 : ℤ) ^ (M - 1) ≤ 2 ^ 24 * R := by
    rcases Nat.eq_or_lt_of_le hM with e | hlt
    · have hR1 : 1 ≤ R := by
        rw [hR, Int.le_ediv_iff_mul_le gpos, ← e]
        omega
      rw [← e]
      have : (2 : ℤ) ^ (24 - 1) ≤ 2 ^ 24 * 1 := by norm_num
      nlinarith
    · have hR1 : (2 : ℤ) ^ (M - 25) ≤ R := by
        rw [hR, Int.le_ediv_iff_mul_le gpos]
        have e1 : (2 : ℤ) ^ M = 2 ^ (M - 25) * 2 ^ 25 := by rw [← pow_add]; congr 1; omega
        have p : (0 : ℤ) < 2 ^ (M - 25) := by positivity
        have : 0 ≤ g / 2 := by omega
        nlinarith
      have e2 : (2 : ℤ) ^ (M - 1) = 2 ^ 24 * 2 ^ (M - 25) := by rw [← pow_add]; congr 1; omega
      rw [e2]
      nlinarith
  -- upper bound
  have hRnn : 0 ≤ R := by
    have : (0 : ℤ) < 2 ^ (M - 1) := by positivity
    nlinarith
  have hup : 2 ^ 24 * R ≤ 2 ^ M + 2 ^ 24 := by
    have h1 : R * g ≤ 2 ^ M + g / 2 := Int.ediv_mul_le _ (ne_of_gt gpos)
    have h2 : g / 2 ≤ 2 ^ 24 := by omega
    nlinarith
  have eK : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
  have hKM' : (2 : ℤ) ^ (K - 1) ≤ 2 ^ (M - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hM14 : (2 : ℤ) ^ M ≤ 2 ^ 14 * 2 ^ K := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h17 : (2 : ℤ) ^ 17 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
  have pK : (0 : ℤ) < 2 ^ K := by positivity
  have pK1 : (0 : ℤ) < 2 ^ (K - 1) := by positivity
  unfold rhu
  constructor
  · rw [Int.le_ediv_iff_mul_le pK]
    linarith
  · rw [Int.ediv_lt_iff_lt_mul pK]
    nlinarith

theorem target_bite2_norm : Spec.target_bite2_norm := by
  intro np c h hKM hc
  obtain ⟨g1, g2⟩ := biteRow_sig np h hc
  have hMK : np.M ≤ np.K + 14 := by have := h.2.2.2.2.2.2; omega
  have hA := bite_arith np.M np.K (NORM.sig np 5120 (biteRow c)) h.2.2.1 h.2.2.2.2.1 hKM hMK g1 g2
  have yc : NORM.yw np 5120 (biteRow c) c =
      rhu (2 ^ 24 * ((2 ^ np.M + NORM.sig np 5120 (biteRow c) / 2) / NORM.sig np 5120 (biteRow c)))
        np.K := by
    unfold NORM.yw NORM.R
    rw [show biteRow c c = 2 ^ 24 from if_pos rfl]
  have y0 : ∀ j, j ≠ c → NORM.yw np 5120 (biteRow c) j = 0 := fun j hj => by
    unfold NORM.yw
    rw [show biteRow c j = 0 from if_neg hj, zero_mul, rhu_zero (by have := h.2.2.2.2.1; omega)]
  refine ⟨⟨?_, fun j _ => ?_⟩, ?_, fun j hj => ?_⟩
  · rw [biteRow_V hc]
    have := h.2.1
    norm_num at this ⊢
    linarith
  · by_cases hj : j = c
    · subst hj
      rw [yc]
      exact ⟨le_trans (by norm_num) hA.1, hA.2⟩
    · rw [y0 j hj]
      exact fits16_zero
  · unfold NORM.out clamp
    rw [yc]
    exact le_min (le_max_of_le_left hA.1) (by norm_num)
  · unfold NORM.out
    rw [y0 j hj]
    decide

/-! ## The stream, the range tests, the logits -/

section
variable (κ : ℕ → LayerScale)
  (nf : NormPar) (tbs : ℕ → Tables) (σ τ : ℕ → ℕ) (prompt : Fin ppref.T → Fin ppref.V)

/-- the stream at these weights does not read the output matrix -/
theorem biteXK :
    ∀ l, XK ppref κ tbs (biteW σ τ) prompt l = XK ppref κ tbs (iW (fun _ => 0) (biteEmb σ)) prompt l
  | 0 => rfl
  | l + 1 => by
    show (if l % 2 = 0 then
          Att.x' (ppref.at (κ (l / 2))) (tbs (l / 2)) (layW 0)
            (l / 2) (XK ppref κ tbs (biteW σ τ) prompt l)
        else
          FF.x'' (ppref.at (κ (l / 2))) (tbs (l / 2)) (layW 0) (l / 2)
            (XK ppref κ tbs (biteW σ τ) prompt l)) =
      (if l % 2 = 0 then
          Att.x' (ppref.at (κ (l / 2))) (tbs (l / 2)) (layW 0) (l / 2)
            (XK ppref κ tbs (iW (fun _ => 0) (biteEmb σ)) prompt l)
        else
          FF.x'' (ppref.at (κ (l / 2))) (tbs (l / 2)) (layW 0) (l / 2)
            (XK ppref κ tbs (iW (fun _ => 0) (biteEmb σ)) prompt l))
    rw [biteXK l]

theorem biteX0 (hσ : ∀ t, σ t < 5120) (pos : ℕ) (h : pos < ppref.T) :
    x0 κ tbs (fun _ => 0) (biteEmb σ) prompt pos = biteRow (σ (prompt ⟨pos, h⟩)) := by
  funext j
  show (if hh : pos < ppref.T then biteEmb σ (prompt ⟨pos, hh⟩) j else 0) = _
  rw [dif_pos h]
  unfold biteEmb
  by_cases hj : j < 5120
  · rw [if_pos ⟨(prompt ⟨pos, h⟩).2, hj⟩]
  · rw [if_neg (fun hh => hj hh.2)]
    have := hσ (prompt ⟨pos, h⟩)
    exact (if_neg (by omega)).symm

end

theorem biteRuns {pp : ScalesAndPolicy} (h : Lawful pp) (σ τ : ℕ → ℕ)
    (hσ : ∀ t, σ t < 5120) (prompt : Fin ppref.T → Fin ppref.V) :
    RunsK ppref pp.kap pp.nf (fun _ => tbRef) (biteW σ τ) prompt := by
  have hkm : ∀ L, L < 48 →
      (pp.kap L).n1.K ≤ (pp.kap L).n1.M ∧ (pp.kap L).n2.K ≤ (pp.kap L).n2.M := fun L hL => by
    rw [pp.kap_lt hL]
    exact h.km.1 ⟨L, hL⟩
  have h0 : RunsK ppref pp.kap pp.nf (fun _ => tbRef) (iW (fun _ => 0) (biteEmb σ)) prompt := by
    refine (runsW pp.nf _ _ _ prompt (fun L hL => shifts1 h hL)).2
      ⟨fun L hL pos hpos => ?_, fun pos hpos => ?_⟩
    · rw [biteX0 pp.kap (fun _ => tbRef) σ prompt hσ pos hpos]
      refine ⟨(target_bite2_norm _ _ (normsOK h hL).1 (hkm L hL).1 (hσ _)).1,
        ?_,
        (target_bite2_norm _ _ (normsOK h hL).2 (hkm L hL).2 (hσ _)).1⟩
      have hv : 1 ≤ (pp.kap L).kv := (shifts1 h hL).2.2.1
      rw [mul_zero, rhu_zero hv]
      exact fits16_zero
    · rw [biteX0 pp.kap (fun _ => tbRef) σ prompt hσ pos hpos]
      exact (target_bite2_norm _ _ h.nf h.km.2 (hσ _)).1
  have e : XK ppref pp.kap (fun _ => tbRef) (biteW σ τ) prompt =
      XK ppref pp.kap (fun _ => tbRef) (iW (fun _ => 0) (biteEmb σ)) prompt :=
    funext (biteXK _ _ σ τ prompt)
  unfold RunsK at h0 ⊢
  rw [e]
  exact h0

theorem biteLg {pp : ScalesAndPolicy} (h : Lawful pp) (σ τ : ℕ → ℕ) (hσ : ∀ t, σ t < 5120)
    (prompt : Fin ppref.T → Fin ppref.V) (pos : ℕ) (hpos : pos < ppref.T)
    {ι : ℕ} (hι : ι < 202048) :
    lgK ppref pp.kap pp.nf (fun _ => tbRef) (biteW σ τ) prompt pos ι =
      if ι = τ (σ (prompt ⟨pos, hpos⟩)) then
        NORM.out pp.nf 5120 (biteRow (σ (prompt ⟨pos, hpos⟩))) (σ (prompt ⟨pos, hpos⟩))
      else 0 := by
  have hN := target_bite2_norm pp.nf (σ (prompt ⟨pos, hpos⟩)) h.nf h.km.2 (hσ _)
  unfold lgK nrmK dot
  rw [biteXK,
    ScalesSanity.XK_const (fun _ => tbRef) (fun _ => 0) (biteEmb σ) prompt
      (fun L hL => shifts1 h hL) (2 * ppref.layers) (by decide),
    biteX0 pp.kap (fun _ => tbRef) σ prompt hσ pos hpos]
  show ∑ j ∈ range 5120, NORM.out pp.nf 5120 (biteRow (σ (prompt ⟨pos, hpos⟩))) j * headOf τ j ι = _
  rw [sum_eq_single (σ (prompt ⟨pos, hpos⟩)) (fun j _ hj => by rw [hN.2.2 j hj, zero_mul])
      (fun hh => absurd (mem_range.2 (hσ _)) hh)]
  unfold headOf
  rw [if_pos ⟨hσ _, hι⟩]
  split_ifs <;> simp

theorem bitePos {pp : ScalesAndPolicy} (h : Lawful pp) (σ τ : ℕ → ℕ) (hσ : ∀ t, σ t < 5120)
    (hτ : ∀ j, τ j < 202048) (x : Instance ppref) :
    TrueAt pp.kap pp.nf (biteI σ τ) x ↔
    Head3 x ∧ ∀ t (ht : t < ppref.T), x.r ≤ t → t < x.e → x.w t = τ (σ (x.prompt ⟨t, ht⟩)) := by
  unfold biteI
  rw [trueAt_iff, weights_ofIndex]
  refine and_congr_right fun _ => ?_
  show (RunsK ppref pp.kap pp.nf (fun _ => tbRef) (biteW σ τ) x.prompt ∧
      ∀ t, x.r ≤ t → t < x.e →
        gapOf ppref.V (lgK ppref pp.kap pp.nf (fun _ => tbRef) (biteW σ τ) x.prompt t) (x.w t) =
          0) ↔
    _
  have hw : ∀ t, x.w t < 202048 := fun t => x.w_lt t
  have ho : ∀ t (ht : t < ppref.T),
      1 ≤ NORM.out pp.nf 5120 (biteRow (σ (x.prompt ⟨t, ht⟩))) (σ (x.prompt ⟨t, ht⟩)) :=
    fun t ht => (target_bite2_norm pp.nf _ h.nf h.km.2 (hσ _)).2.1
  constructor
  · rintro ⟨-, hg⟩ t ht hr he
    have h1 :=
      ((gapOf_eq_zero_iff _ _ (x.w_lt t)).1 (hg t hr he)).1 (τ (σ (x.prompt ⟨t, ht⟩))) (hτ _)
    rw [biteLg h σ τ hσ x.prompt t ht (hτ _), if_pos rfl,
      biteLg h σ τ hσ x.prompt t ht (hw t)] at h1
    by_contra hne
    rw [if_neg hne] at h1
    have := ho t ht
    omega
  · intro hx
    refine ⟨biteRuns h σ τ hσ x.prompt, fun t hr he => ?_⟩
    have ht : t < ppref.T := lt_of_lt_of_le he x.e_le
    have := ho t ht
    rw [gapOf_eq_zero_iff _ _ (x.w_lt t)]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [biteLg h σ τ hσ x.prompt t ht hv,
        biteLg h σ τ hσ x.prompt t ht (hw t), if_pos (hx t ht hr he)]
      split_ifs <;> omega
    · rw [biteLg h σ τ hσ x.prompt t ht (lt_trans hv (hw t)), biteLg h σ τ hσ x.prompt t ht (hw t),
        if_pos (hx t ht hr he), if_neg (by rw [← hx t ht hr he]; exact Nat.ne_of_lt hv)]
      omega

theorem target_bite2_pos : Spec.target_bite2_pos := fun s hs σ τ hσ hτ x =>
  (paper_iff s.kap s.nf _ x).symm.trans (bitePos hs.toPP σ τ hσ hτ x)

theorem target_bite2_all : Spec.target_bite2_all := by
  have hS : ∀ t, biteS t < 5120 := fun t => by unfold biteS; split <;> norm_num
  have hT : ∀ j, biteT j < 202048 := fun j => by unfold biteT; split <;> norm_num
  have h3 : ∀ x : Instance ppref, x.rF = 0 → x.eF = Fin.last _ → Head3 x := fun x h1 h2 => by
    have e1 : x.r = 0 := by show x.rF.val = 0; rw [h1]; rfl
    have e2 : x.e = ppref.T := by show x.eF.val = ppref.T; rw [h2]; rfl
    exact ⟨by rw [e1, e2]; decide, le_of_eq e2, fun h => absurd h (by rw [e2]; exact lt_irrefl _)⟩
  refine ⟨biteI biteS fun _ => 0, biteI biteS biteT, RequestGuards2.xz 0 (Fin.last _),
    biteX, fun s hs => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (target_bite2_pos s hs biteS (fun _ => 0) hS (fun _ => by norm_num) _).2
      ⟨h3 _ rfl rfl, fun t _ _ _ => RequestGuards2.xz_w _ _ t⟩
  · exact (target_bite2_pos s hs biteS biteT hS hT _).2
      ⟨h3 _ rfl rfl,
        fun t _ _ _ =>
          (RequestGuards2.xz_w _ _ t).trans (by simp [RequestGuards2.xz, biteS, biteT])⟩
  · exact (target_bite2_pos s hs biteS (fun _ => 0) hS (fun _ => by norm_num) _).2
      ⟨h3 _ rfl rfl, fun t _ _ _ => biteX_w t⟩
  · intro h
    have := ((target_bite2_pos s hs biteS biteT hS hT _).1 h).2
      0 (by decide) (Nat.zero_le _) (by show 0 < (Fin.last ppref.T).val; decide)
    rw [biteX_w] at this
    simp [biteX, biteS, biteT] at this

end Cm

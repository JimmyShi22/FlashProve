-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/ScalesSanity.lean: the relation at valid settings is neither empty nor blind to the
settings (`Lawful`, Inst/Model/Scales.lean). To audit the relations `RinfPP0` and `RinfPP`
(Inst/Model/Scales.lean), nothing of this file need be read.

A theorem "for every table pp" (for all settings pp) about the relation `RinfPP0 pp`
(Inst/Model/Scales.lean) would say little if that relation were empty, or did not read pp. Here:
  1  `sigK_pos`, `denK_pos`, `modelIsK_unique`: at valid settings no division by 0 is reached in a
     normalisation or in attention's quotient, and the program is a partial function.
  2  `layW`, `iW`, `runsW`: a family of synthetic indices: in every layer all matrices are zero but
     for one entry v of W_v. Under `hs` (all shifts at least 1) the stream never changes, and the
     program runs if and only if the normalisations accept the embedding rows and the one value
     rhu(a · v, kv) of each layer at each position fits 16 bits.
  3  `zero_true`: for all valid settings the all-zero index and every prompt give a true instance,
     the request "the next token after these tokens" (`Instance.nextOf`) with y = 0: the relation is
     never empty.
  4  `differs`: the relation reads a scale (kv) of every layer L (the last, 47, among them): one
     index and prompt are in the relation at the reference settings, and at the valid settings with
     kv = 1 in the place of 17 in layer L the program does not run, so there no instance with that
     prompt is in the relation, whatever y, r, e.
The indices are made up for these proofs; `ppAt` is the reference settings with one kv set to 1.
Notation: (the definitions in the words of the doc comments of Inst/Model/Program.lean)
  rhu: `rhu`: "rhu(a, k) = ⌊(a + 2^(k−1)) / 2^k⌋, the quotient by 2^k rounded to the nearest
      integer, halves up"; k ≥ 1
  fits 16 bits: `Fits16`: "a fits 16 bits if −2^15 ≤ a < 2^15"
  a (in 2): an integer: `NORM.out` of the row at a position, in the channel 0 (`att_ok_layW`)
  ς: `NORM.sig`, an integer: (N2) ς = isqrt(V + ϵ)
  den: `Att.den`, an integer: (PA5) den_i = Σ_{j ≤ i} wt_ij
  (N3), (PA7): labels of steps of the program, in the doc comments of `NORM.R` and `Att.o`
Limits: `differs` changes one number of each layer, kv; no theorem in this file shows the like for a
layer's other numbers or for the final normalisation, and none has the program run at two settings
with different answers y.
-/
import Inst.Model.ScalesGuard
import Inst.Model.SanityAtt

set_option autoImplicit false

namespace Inst.Model.ScalesSanity

open Finset

/-! ## 1. No division by 0; a partial function -/

theorem shifts1_but {pp : ScalesAndPolicy} (h : LawfulBut pp) {L : ℕ} (hL : L < 48) :
    (ppref.at (pp.kap L)).Shifts1 := by
  rw [pp.kap_lt hL]
  have r := h.ff ⟨L, hL⟩
  exact ⟨le_trans (by norm_num) r.kq.1, le_trans (by norm_num) r.kk.1, r.kv.1, r.ko.1, r.kg.1,
    r.ku.1, le_trans (by norm_num) r.kd.1, le_trans (by norm_num) r.kr.1, r.kg'.1, r.ku'.1⟩
theorem shifts1 {pp : ScalesAndPolicy} (h : Lawful pp) {L : ℕ} (hL : L < 48) : (ppref.at (pp.kap L)).Shifts1 :=
  shifts1_but h.toLawfulBut hL

theorem normsOK_but {pp : ScalesAndPolicy} (h : LawfulBut pp) {L : ℕ} (hL : L < 48) :
    (pp.kap L).n1.OK ∧ (pp.kap L).n2.OK := by
  rw [pp.kap_lt hL]
  exact ⟨(h.ff ⟨L, hL⟩).n1, (h.ff ⟨L, hL⟩).n2⟩
theorem normsOK {pp : ScalesAndPolicy} (h : Lawful pp) {L : ℕ} (hL : L < 48) :
    (pp.kap L).n1.OK ∧ (pp.kap L).n2.OK :=
  normsOK_but h.toLawfulBut hL

/-- At valid settings, in a layer L < 48, (N3) divides by ς ≥ 1, in all three kinds of
normalisation -/
theorem sigK_pos {pp : ScalesAndPolicy} (h : Lawful pp) {L : ℕ} (hL : L < 48) (d : ℕ) (x : Vec) :
    1 ≤ NORM.sig (pp.kap L).n1 d x ∧ 1 ≤ NORM.sig (pp.kap L).n2 d x ∧ 1 ≤ NORM.sig pp.nf d x :=
  ⟨sig_pos _ (normsOK h hL).1.1 d x, sig_pos _ (normsOK h hL).2.1 d x, sig_pos _ h.nf.1 d x⟩

/-- At any settings pp, in a layer L < 48, with the tables `tbRef`: (PA7) divides by 2 den, and
den ≥ 2^12 -/
theorem denK_pos (pp : ScalesAndPolicy) {L : ℕ} (hL : L < 48) (w : LayerW) (x : ℕ → Vec) (hd i : ℕ) :
    2 ^ 12 ≤ Att.den (ppref.at (pp.kap L)) tbRef w L x hd i := by
  have e : (pp.kap L).expRows = ppref.expRows := by rw [pp.kap_lt hL]; rfl
  exact den_pos _ tbRef ((Tables.OK_at e).2 tbRef_ok)
    (by show 0 < (pp.kap L).expRows; rw [e]; decide) w L x hd i

/-- The program at given scales is a partial function. -/
theorem modelIsK_unique {P : Params} {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables}
    {i : Weights} {prompt : Fin P.T → Fin P.V} {y y' : ℕ} (h : ModelIsK P κ nf tbs i prompt y)
    (h' : ModelIsK P κ nf tbs i prompt y') : y = y' := by
  obtain ⟨-, hy, hmax, hleast⟩ := h
  obtain ⟨-, hy', hmax', hleast'⟩ := h'
  rcases Nat.lt_trichotomy y y' with hlt | heq | hgt
  · exact absurd (hmax y' hy') (not_le.2 (hleast' y hlt))
  · exact heq
  · exact absurd (hmax' y hy) (not_le.2 (hleast y' hgt))

/-! ## 2. Layers with one entry of W_v -/

/-- all matrices zero, but W_v[0][0] = v -/
def layW (v : ℤ) : LayerW := { zeroLayer with Wv := fun j c => if j = 0 ∧ c = 0 then v else 0 }

section Lay
variable (P : Params) (tb : Tables) (L : ℕ) (x : ℕ → Vec) (v : ℤ)

theorem att_layW (hko : 1 ≤ P.ko) : Att.x' P tb (layW v) L x = x := by
  funext i c
  simp [Att.x', layW, zeroLayer, dot_zero, rhu_zero hko]

theorem vw_layW (hd : 0 < P.d) (hv : 1 ≤ P.kv) (i c : ℕ) :
    Att.vw P (layW v) x i c = if c = 0 then rhu (NORM.out P.n1 P.d (x i) 0 * v) P.kv else 0 := by
  unfold Att.vw Att.Av
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    congr 1
    unfold dot
    rw [sum_eq_single 0 (fun j _ hj => by simp [layW, hj]) (fun h => absurd (mem_range.2 hd) h)]
    simp [layW, Att.a]
  · rw [if_neg hc]
    have : (fun j => (layW v).Wv j c) = fun _ => 0 := by
      funext j
      simp [layW, hc]
    rw [this, dot_zero, rhu_zero hv]

theorem att_ok_layW (hd : 0 < P.d) (hw : 0 < P.nkv * P.ch) (hq : 1 ≤ P.kq)
    (hk : 1 ≤ P.kk) (hv : 1 ≤ P.kv) :
    Att.OK P tb (layW v) L x ↔
    ∀ i < P.T, NORM.OK P.n1 P.d (x i) ∧ Fits16 (rhu (NORM.out P.n1 P.d (x i) 0 * v) P.kv) := by
  have h1 : ∀ i c, Att.qkw P tb (layW v) L x i c = 0 := by
    intro i c
    have hA : ∀ c', Att.AY P (layW v) x i c' = 0 := by
      intro c'
      simp [Att.AY, Att.Aq, Att.Ak, layW, zeroLayer, dot_zero]
    simp only [Att.qkw, Att.Y', hA, mul_zero, sub_zero, add_zero, ite_self]
    split_ifs
    · exact rhu_zero hq
    · exact rhu_zero hk
  simp only [Att.OK, h1, vw_layW P x v hd hv]
  refine ⟨fun h i hi => ⟨(h i hi).1, by simpa using (h i hi).2.2 0 hw⟩,
    fun h i hi => ⟨(h i hi).1, fun _ _ => fits16_zero, fun c _ => ?_⟩⟩
  split_ifs
  · exact (h i hi).2
  · exact fits16_zero

theorem ff_layW (hkd : 1 ≤ P.kd) : FF.x'' P tb (layW v) L x = x := by
  funext i c
  simp [FF.x'', FF.Ad, layW, zeroLayer, rhu_zero hkd]

theorem ff_ok_layW (hr : 1 ≤ P.kr) (hg : 1 ≤ P.kg) (hu : 1 ≤ P.ku)
    (hg' : 1 ≤ P.kg') (hu' : 1 ≤ P.ku') :
    FF.OK P tb (layW v) L x ↔ ∀ i < P.T, NORM.OK P.n2 P.d (x i) := by
  have h1 : ∀ i e, FF.ly P (layW v) x i e = 0 := by
    intro i e
    simp [FF.ly, FF.l3, FF.lw, layW, zeroLayer, dot_zero, rhu_zero hr]
  have hkG : ∀ j, 1 ≤ FF.kG P L j := by intro j; unfold FF.kG; split_ifs <;> assumption
  have hkU : ∀ j, 1 ≤ FF.kU P L j := by intro j; unfold FF.kU; split_ifs <;> assumption
  have hwg : ∀ i j, FF.wg P (layW v) L x i j = fun _ => 0 := by
    intro i j; funext t; simp [FF.wg, layW, zeroLayer]
  have hwu : ∀ i j, FF.wu P (layW v) L x i j = fun _ => 0 := by
    intro i j; funext t; simp [FF.wu, layW, zeroLayer]
  have h2 : ∀ i j,
      UNIT.OK P.d (FF.z P tb (layW v) L x i j) (FF.wg P (layW v) L x i j) (FF.wu P (layW v) L x i j)
        (FF.kG P L j) (FF.kU P L j) := by
    intro i j
    simp only [UNIT.OK, UNIT.gh, UNIT.g0, UNIT.gw, UNIT.up, hwg, hwu, dot_zero, rhu_zero (hkG j),
      rhu_zero (hkU j), lowByte]
    refine ⟨by norm_num, fits16_zero⟩
  simp only [FF.OK, h1]
  exact ⟨fun h i hi => (h i hi).1,
    fun h i hi => ⟨h i hi, fun _ _ _ => fits16_zero, fun j _ => h2 i j⟩⟩

end Lay

/-- The synthetic indices: layer L has the entry vs L; the output matrix is zero. -/
def iW (vs : ℕ → ℤ) (Emb : Mat) : Weights := ⟨fun L => layW (vs L), Emb, fun _ _ => 0⟩

section Index
variable (κ : ℕ → LayerScale)
  (nf : NormPar) (tbs : ℕ → Tables) (vs : ℕ → ℤ) (Emb : Mat) (prompt : Fin ppref.T → Fin ppref.V)

/-- the embedding rows of the prompt -/
abbrev x0 : ℕ → Vec := XK ppref κ tbs (iW vs Emb) prompt 0

variable {κ} (hs : ∀ L < 48, (ppref.at (κ L)).Shifts1)
include hs

/-- If all shifts of the 48 layers are at least 1 (`hs`), the stream of a synthetic index (`iW`)
never changes. -/
theorem XK_const : ∀ l ≤ 96, XK ppref κ tbs (iW vs Emb) prompt l = x0 κ tbs vs Emb prompt
  | 0, _ => rfl
  | l + 1, hl => by
    have ih := XK_const l (Nat.le_of_succ_le hl)
    obtain ⟨-, -, -, hko, -, -, hkd, -, -, -⟩ := hs (l / 2) (by omega)
    show (if l % 2 = 0 then
          Att.x' (ppref.at (κ (l / 2))) (tbs (l / 2)) (layW (vs (l / 2)))
            (l / 2) (XK ppref κ tbs (iW vs Emb) prompt l)
        else
          FF.x'' (ppref.at (κ (l / 2))) (tbs (l / 2)) (layW (vs (l / 2))) (l / 2)
            (XK ppref κ tbs (iW vs Emb) prompt l)) = _
    split_ifs
    · rw [att_layW _ _ _ _ _ hko, ih]
    · rw [ff_layW _ _ _ _ _ hkd, ih]

/-- Under `hs`, the program runs on such an index if and only if the normalisations accept the
embedding rows and the one value of each layer at each position fits 16 bits. -/
theorem runsW :
    RunsK ppref κ nf tbs (iW vs Emb) prompt ↔
    (∀ L < 48, ∀ pos < 1024,
      NORM.OK (κ L).n1 5120 (x0 κ tbs vs Emb prompt pos) ∧
      Fits16 (rhu (NORM.out (κ L).n1 5120 (x0 κ tbs vs Emb prompt pos) 0 * vs L) (κ L).kv) ∧
      NORM.OK (κ L).n2 5120 (x0 κ tbs vs Emb prompt pos)) ∧
    ∀ pos < 1024, NORM.OK nf 5120 (x0 κ tbs vs Emb prompt pos) := by
  unfold RunsK
  refine and_congr (forall_congr' fun L => forall_congr' fun hL => ?_) ?_
  · have hL' : L < 48 := hL
    obtain ⟨hq, hk, hv, -, hg, hu, -, hr, hg', hu'⟩ := hs L hL'
    rw [XK_const tbs vs Emb prompt hs (2 * L) (by omega),
      XK_const tbs vs Emb prompt hs (2 * L + 1) (by omega)]
    show Att.OK (ppref.at (κ L)) (tbs L) (layW (vs L)) L _ ∧
        FF.OK (ppref.at (κ L)) (tbs L) (layW (vs L)) L _ ↔
      _
    rw [att_ok_layW (ppref.at (κ L)) _ _ _ _ (by decide : 0 < ppref.d)
          (by decide : 0 < ppref.nkv * ppref.ch) hq hk hv,
      ff_ok_layW _ _ _ _ _ hr hg hu hg' hu']
    exact ⟨fun h pos hpos => ⟨(h.1 pos hpos).1, (h.1 pos hpos).2, h.2 pos hpos⟩,
      fun h =>
        ⟨fun pos hpos => ⟨(h pos hpos).1, (h pos hpos).2.1⟩, fun pos hpos => (h pos hpos).2.2⟩⟩
  · rw [XK_const tbs vs Emb prompt hs (2 * ppref.layers) (by decide)]
    exact Iff.rfl

omit hs in
/-- the output matrix is zero: all logits are 0, and the output is the token 0 -/
theorem outW : IsOutputK ppref κ nf tbs (iW vs Emb) prompt 0 :=
  ⟨by decide, fun ι _ => by simp [lgK, iW, dot_zero], fun ι h => absurd h (Nat.not_lt_zero ι)⟩

end Index

theorem layW_wf {v : ℤ} (hv : -4096 ≤ v ∧ v ≤ 4095) (L : ℕ) : (layW v).WF ppref L := by
  have hz := SanityRef.zeroLayer_wf L
  unfold LayerW.WF at hz ⊢
  refine ⟨hz.1, hz.2.1, fun j c => ?_, hz.2.2.2.1, hz.2.2.2.2⟩
  show if j < 5120 ∧ c < 1024 then
    _ ≤ (if j = 0 ∧ c = 0 then v else 0) ∧ (if j = 0 ∧ c = 0 then v else 0) ≤ _
  else (if j = 0 ∧ c = 0 then v else 0) = 0
  split_ifs <;> omega

theorem layW_zero : layW 0 = zeroLayer := by
  unfold layW zeroLayer
  simp

theorem iW_wf {vs : ℕ → ℤ} (hv : ∀ L, -4096 ≤ vs L ∧ vs L ≤ 4095) (h0 : ∀ L, 48 ≤ L → vs L = 0)
    {Emb : Mat} (hE : Box ppref.V ppref.d (-2155905152) 2139062143 Emb) : (iW vs Emb).WF ppref := by
  refine ⟨fun L => ?_, hE, SanityRef.two_zero _ _⟩
  show if L < 48 then (layW (vs L)).WF ppref L else (layW (vs L)).IsZero
  split_ifs with hL
  · exact layW_wf (hv L) L
  · rw [h0 L (by omega), layW_zero]
    exact SanityRef.zeroLayer_isZero

/-! ## 3. At valid settings the relation is never empty -/

theorem normOK_zero {np : NormPar} (h : np.OK) (d : ℕ) : NORM.OK np d fun _ => 0 := by
  refine ⟨?_, fun j _ => ?_⟩
  · have : NORM.V d (fun _ => 0) = 0 := by simp [NORM.V]
    rw [this]
    have := h.2.1
    norm_num at this ⊢
    linarith
  · show Fits16 (rhu ((0 : ℤ) * _) np.K)
    rw [zero_mul, rhu_zero (by have := h.2.2.2.2.1; omega)]
    exact fits16_zero

/-- the all-zero index -/
def iZero : Index ppref :=
  ⟨iW (fun _ => 0) fun _ _ => 0,
    iW_wf (fun _ => by norm_num) (fun _ _ => rfl) fun t j => by split_ifs <;> norm_num⟩

/-- Under `LawfulBut`, the all-zero index and every prompt give a true instance, with y = 0. -/
theorem zero_true_but {pp : ScalesAndPolicy} (h : LawfulBut pp) (prompt : Fin ppref.T → Fin ppref.V) :
    RinfPP0 pp iZero (Instance.nextOf prompt ⟨0, by decide⟩) := by
  refine (ModelR_nextOf ppref (by decide) _ _ _ pp.pol _ prompt ⟨0, by decide⟩).2
    ⟨(runsW pp.nf _ _ _ prompt (fun L hL => shifts1_but h hL)).2 ?_, outW _ _ _ _ _⟩
  have e : x0 pp.kap (fun _ => tbRef) (fun _ => 0) (fun _ _ => 0) prompt = fun _ _ => 0 := by
    funext pos j
    show (if hh : pos < ppref.T then (0 : ℤ) else 0) = 0
    split <;> rfl
  rw [e]
  refine ⟨fun L hL pos _ =>
      ⟨normOK_zero (normsOK_but h hL).1 _, ?_, normOK_zero (normsOK_but h hL).2 _⟩,
    fun pos _ => normOK_zero h.nf _⟩
  have hv : 1 ≤ (pp.kap L).kv := (shifts1_but h hL).2.2.1
  rw [mul_zero, rhu_zero hv]
  exact fits16_zero
theorem zero_true {pp : ScalesAndPolicy} (h : Lawful pp) (prompt : Fin ppref.T → Fin ppref.V) :
    RinfPP0 pp iZero (Instance.nextOf prompt ⟨0, by decide⟩) :=
  zero_true_but h.toLawfulBut prompt

/-! ## 4. The relation reads a scale (kv) of every layer -/

open ScalesGuard (put one)

/-- `vsAt`, with `iAt` below: the index `iAt L₀ h` has W_v[0][0] = 4,095 in layer L₀, all else zero;
token 0 is embedded as 2^20 in the channel 0 (SanityAtt.embA) -/
def vsAt (L₀ : ℕ) : ℕ → ℤ := fun L => if L = L₀ then 4095 else 0

def iAt (L₀ : ℕ) (h : L₀ < 48) : Index ppref :=
  ⟨iW (vsAt L₀) SanityAtt.embA,
    iW_wf (fun L => by unfold vsAt; split_ifs <;> norm_num)
      (fun L hL => by unfold vsAt; rw [if_neg (by omega)]) SanityAtt.embA_box⟩

/-- the prompt of 1,024 tokens 0 -/
def p0 : Fin ppref.T → Fin ppref.V := fun _ => ⟨0, by decide⟩

/-- the reference settings with kv = 1 in layer L₀ -/
def ppAt (L₀ : ℕ) : ScalesAndPolicy := put (one L₀) { wRef with kv := 1 }

theorem x0_p0 (κ : ℕ → LayerScale) (tbs : ℕ → Tables) (vs : ℕ → ℤ) {pos : ℕ} (hpos : pos < 1024) :
    x0 κ tbs vs SanityAtt.embA p0 pos = SanityAtt.xs (fun _ => true) pos := by
  funext j
  show (if hh : pos < ppref.T then SanityAtt.embA (p0 ⟨pos, hh⟩) j else 0) = _
  rw [dif_pos (show pos < ppref.T from hpos)]
  simp [SanityAtt.embA, SanityAtt.xs, p0]

theorem out0 (pos : ℕ) :
    NORM.out SanityRef.npR 5120 (SanityAtt.xs (fun _ => true) pos) 0 = 2047 := by
  have := congrFun (SanityAtt.a_eq (fun _ => true) pos) 0
  simpa using this

theorem ppAt_lawful {L₀ : ℕ} : Lawful (ppAt L₀) where
  ff := fun L => by
    show FFSeg.Ranges (if one L₀ L then { wRef with kv := 1 } else wRef : Words).scale
    split <;> decide
  sh := fun L => by
    show 4 ≤ (if one L₀ L then { wRef with kv := 1 } else wRef : Words).sh ∧
      (if one L₀ L then { wRef with kv := 1 } else wRef : Words).sh ≤ 12
    split <;> decide
  one := fun g l => by
    have hsh : ∀ L, ((ppAt L₀).kap L).sh = 8 := fun L => by
      unfold ScalesAndPolicy.kap
      split
      · show (if one L₀ _ then { wRef with kv := 1 } else wRef : Words).sh = 8
        split <;> rfl
      · rfl
    rw [hsh, hsh]
  nf := lawful_ref.nf
  pol := lawful_ref.pol
  km := ⟨fun L => by
    show (if one L₀ L then { wRef with kv := 1 } else wRef : Words).n1.K ≤
        (if one L₀ L then { wRef with kv := 1 } else wRef : Words).n1.M ∧
      (if one L₀ L then { wRef with kv := 1 } else wRef : Words).n2.K ≤
        (if one L₀ L then { wRef with kv := 1 } else wRef : Words).n2.M
    split <;> decide, lawful_ref.km.2⟩

/-- the scales of `ppAt L₀`: those of the reference but for kv in layer L₀ -/
theorem kap_ppAt (L₀ : ℕ) {L : ℕ} (hL : L < 48) :
    (ppAt L₀).kap L = if L = L₀ then { ppref.scale with kv := 1 } else ppref.scale := by
  rw [ScalesAndPolicy.kap_lt _ hL]
  show (if one L₀ ⟨L, hL⟩ then { wRef with kv := 1 } else wRef : Words).scale = _
  by_cases h : L = L₀
  · rw [if_pos (by simp [ScalesGuard.one, h]), if_pos h]
    rfl
  · rw [if_neg (by simp [ScalesGuard.one, h]), if_neg h]
    rfl

/-- The relation reads a scale of every layer: for every layer L₀ there are an index and an
instance that are in the relation at the reference settings and not in the relation at the valid
settings that differ from them in the one number kv of layer L₀. -/
theorem differs {L₀ : ℕ} (h : L₀ < 48) :
    Lawful (ppAt L₀) ∧
    RinfPP0 ppRef (iAt L₀ h) (Instance.nextOf p0 ⟨0, by decide⟩) ∧
    ∀ x : Instance ppref, x.prompt = p0 → ¬ RinfPP0 (ppAt L₀) (iAt L₀ h) x := by
  refine ⟨ppAt_lawful,
    (ModelR_nextOf ppref (by decide) _ _ _ ppRef.pol _ p0 ⟨0, by decide⟩).2
      ⟨(runsW _ _ _ _ p0 (fun L hL => shifts1 lawful_ref hL)).2
          ⟨fun L hL pos hpos => ?_, fun pos hpos => ?_⟩,
        outW _ _ _ _ _⟩,
    fun x hx hy => ?_⟩
  · rw [x0_p0 _ _ _ hpos, kap_ref]
    refine ⟨SanityAtt.ok_xs _ pos, ?_, SanityAtt.ok_xs _ pos⟩
    show Fits16
      (rhu (NORM.out SanityRef.npR 5120 (SanityAtt.xs (fun _ => true) pos) 0 * vsAt L₀ L) 17)
    rw [out0]
    unfold vsAt
    unfold Fits16
    split_ifs <;> decide +kernel
  · rw [x0_p0 _ _ _ hpos]
    exact SanityAtt.ok_xs _ pos
  · have hy1 := hy.1
    rw [hx] at hy1
    have hr := ((runsW _ _ _ _ p0 (fun L hL => shifts1 (ppAt_lawful (L₀ := L₀)) hL)).1 hy1).1
      L₀ h 0 (by norm_num)
    rw [x0_p0 _ _ _ (by norm_num), kap_ppAt L₀ h, if_pos rfl] at hr
    have h2 : Fits16
        (rhu (NORM.out SanityRef.npR 5120 (SanityAtt.xs (fun _ => true) 0) 0 * vsAt L₀ L₀) 1) :=
      hr.2.1
    rw [out0] at h2
    unfold vsAt at h2
    rw [if_pos rfl] at h2
    unfold Fits16 at h2
    exact absurd h2 (by decide +kernel)

/-- in particular the last layer -/
example :
    ∃ (pp : ScalesAndPolicy) (i : Index ppref) (x : Instance ppref), Lawful pp ∧
      (∀ L : Fin 48, L.val ≠ 47 → pp.w L = ppRef.w L) ∧ RinfPP0 ppRef i x ∧ ¬ RinfPP0 pp i x :=
  ⟨ppAt 47, iAt 47 (by norm_num), Instance.nextOf p0 ⟨0, by decide⟩, (differs (by norm_num)).1, fun L hL => by
    show (if one 47 L then _ else _) = _
    rw [if_neg (by simp [ScalesGuard.one, hL])],
      (differs (by norm_num)).2.1,
      (differs (by norm_num)).2.2 _ rfl⟩

end Inst.Model.ScalesSanity

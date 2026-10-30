-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PlacesTiesHead.lean

If Head.layout returns at a shape whose eight numbers are S's ("FitsH"), the numbers by which
Johnson/HonestTrace/Places.lean places the cells of the output head's matrices hf and hd are those
of the layout; for hr also, if XL = 5.

Johnson/HonestTrace/Places.lean computes a matrix's columns and a cell's place from the numbers of a
value S : Sz. Head.layout (OnBytes/Model/HeadLayout.lean), a function of the Lean verifier under
OnBytes/Model/, computes the head's numbers from a shape hH : Head.Shape and returns them in L :
Head.HL. The library's rule for the place of a feature in such a layout is Hd.placeIn
(Johnson/Road/HeadPlace.lean). This file sets the two side by side.

Main definition and theorems. "The layout returns" means Head.layout hH tau = .ok L.
* "FitsH S hH": eight numbers of S are hH's: lt, la, d, V, NHf, and the features in a column of hf,
  hd, hr, which are 2^lmhf / 2^lt, 2^lmhd / 2^lt, 2^lmhr / 2^lt.
* "T_H": under FitsH, hH.T = 2^lt.
* "JV_H", "feat_H", "wc_H", "k_H": if the layout returns, under FitsH: L.JV = S.JV;
  L.feat = S.n (.hf 0); L.m / T, L.mD / T, L.mR / T are S.wchf, S.wchd, S.wchr; L.k = S.kF (.hf 0),
  L.kD = S.kF .hd, and, if hH.XL = 5, L.kR = S.kF .hr.
* "place_hf": under the same premises, at every feature φ and position t, the matrix's name, the row
  and the column of S.atFeat .head (.hf 0) φ t are part, row and column of
  Hd.placeIn L.k (L.m / T) T φ t.
* "place_hd", "place_hr": the like for row and column in hd and, if hH.XL = 5, in hr. "part_hd",
  "part_hr": for a feature below S.n .hd (S.n .hr), placeIn's part is 0.
* "wc_H_pos": if the layout returns, under FitsH, S.wchf, S.wchd, S.wchr and S.NHf are not 0.
* "nr_H": if hH.XL = 5, ledNRH hH.XL = S.n .hr.

Limits. S.n .hr is the constant 120. Head.numbers counts ledNRH hH.XL features in hr, which is 120
at XL = 5 and 95 at XL = 4, and Head.layout admits both: so every statement on hr has the premise
hH.XL = 5. Head.HL has a field for the number of features of hf alone (feat); for hd and hr it has
the numbers rounded up to whole columns. FitsH is shown of the numbers at a parameter file's lines
in Johnson/HonestTrace/PlacesTies.lean ("fitsH_ofHdr"), not here. No theorem of this file shows that
Head.layout returns for some shape. Nothing is said of the matrix bH (see
Johnson/HonestTrace/PlacesTies.lean) or of the stream's matrix.

Not claimed: anything on a proof, a prover or what a verifier accepts.

-/
import Johnson.Road.HeadPlace
import Johnson.Road.HeadLaid
import Johnson.HonestTrace.Places

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Model (roundUp exc ledNRH)

/-- Eight numbers of S are those of the head's shape hH: lt, la, d, V, NHf, and the numbers of
features in a column of hf, hd and hr, which are 2^lmhf / 2^lt, 2^lmhd / 2^lt and 2^lmhr / 2^lt. -/
structure FitsH (S : Sz) (hH : Model.Head.Shape) : Prop where
  lt : S.lt = hH.lt
  la : S.la = hH.la
  d : S.P.d = hH.d
  V : S.P.V = hH.V
  NHf : S.NHf = hH.NHf
  wchf : S.wchf = 2 ^ hH.lmhf / 2 ^ hH.lt
  wchd : S.wchd = 2 ^ hH.lmhd / 2 ^ hH.lt
  wchr : S.wchr = 2 ^ hH.lmhr / 2 ^ hH.lt

namespace TiesHead

/-! ## What Head.layout returns -/

/-- For w > 0: roundUp x w / w is Sz.ceilDiv x w. -/
theorem roundUp_div (x : ℕ) {w : ℕ} (hw : 0 < w) : roundUp x w / w = Sz.ceilDiv x w := by
  unfold roundUp Sz.ceilDiv
  exact Nat.mul_div_cancel _ hw

/-- If Head.layout h tau returns L, eight numbers of L are as Head.numbers makes them (JV, m, mD,
mR, feat, k, kD, kR), and NHf is not 0 and lt ≤ lmhf, lmhd, lmhr. -/
theorem layout_numbers {h : Model.Head.Shape} {tau : Array UInt64} {L : Model.Head.HL}
    (hy : Model.Head.layout h tau = .ok L) :
    (L.JV = roundUp h.V h.S2 ∧ L.m = 2 ^ h.lmhf ∧ L.mD = 2 ^ h.lmhd ∧ L.mR = 2 ^ h.lmhr ∧
      L.feat = 4 * h.d + (3 + exc) * L.JV ∧
      L.k = roundUp L.feat (h.NHf * (L.m / h.T)) / (h.NHf * (L.m / h.T)) ∧
      L.kD = roundUp (2 * h.d) (L.mD / h.T) / (L.mD / h.T) ∧
      L.kR = roundUp (ledNRH h.XL) (L.mR / h.T) / (L.mR / h.T)) ∧
    (0 < h.NHf ∧ h.lt ≤ h.lmhf ∧ h.lt ≤ h.lmhd ∧ h.lt ≤ h.lmhr) := by
  have hadm := (Road.Hd.admittedH_of_layout hy).adm
  simp only [Model.Head.admitted, Bool.and_eq_true, decide_eq_true_eq] at hadm
  unfold Model.Head.layout at hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨L0, hn, hy⟩ := Road.ok_of_bind hy
  obtain ⟨cs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨kb, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  cases hy
  unfold Model.Head.numbers at hn
  obtain ⟨-, hn⟩ := Road.Hd.ok_of_needed hn
  obtain ⟨e3, hn⟩ := Road.Hd.ok_of_needed hn
  cases hn
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt,
    beq_eq_false_iff_ne] at e3
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by omega, by omega, by omega, by omega⟩

end TiesHead

/-! ## The numbers and the places -/

section
variable {S : Sz} {hH : Model.Head.Shape} {tau : Array UInt64} {L : Model.Head.HL}

/-- Under FitsH S hH, the number of positions hH.T is 2^S.lt. -/
theorem T_H (F : FitsH S hH) : hH.T = 2 ^ S.lt := by
  rw [F.lt]
  rfl

/-- If Head.layout hH tau returns L and FitsH S hH holds, then L.JV = S.JV. -/
theorem JV_H (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) : L.JV = S.JV := by
  rw [(TiesHead.layout_numbers hy).1.1]
  unfold Sz.JV roundUp Model.Head.Shape.S2 Model.Head.Shape.ls
  rw [F.V, F.la, F.lt]

/-- If Head.layout hH tau returns L and FitsH S hH holds, then L.m / hH.T, L.mD / hH.T and L.mR /
hH.T are S.wchf, S.wchd and S.wchr. -/
theorem wc_H (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) :
    L.m / hH.T = S.wchf ∧ L.mD / hH.T = S.wchd ∧ L.mR / hH.T = S.wchr := by
  obtain ⟨⟨_, e1, e2, e3, _⟩, _⟩ := TiesHead.layout_numbers hy
  rw [e1, e2, e3, F.wchf, F.wchd, F.wchr]
  exact ⟨rfl, rfl, rfl⟩

/-- If Head.layout hH tau returns L and FitsH S hH holds, then S.wchf, S.wchd, S.wchr and S.NHf are
greater than 0. -/
theorem wc_H_pos (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) :
    0 < S.wchf ∧ 0 < S.wchd ∧ 0 < S.wchr ∧ 0 < S.NHf := by
  obtain ⟨_, p0, p1, p2, p3⟩ := TiesHead.layout_numbers hy
  have pos : ∀ a, hH.lt ≤ a → 0 < 2 ^ a / 2 ^ hH.lt := fun a ha =>
    Nat.div_pos (Nat.pow_le_pow_right (by norm_num) ha) (Nat.pow_pos (by norm_num))
  rw [F.wchf, F.wchd, F.wchr, F.NHf]
  exact ⟨pos _ p1, pos _ p2, pos _ p3, p0⟩

/-- If Head.layout hH tau returns L and FitsH S hH holds, then L.feat = S.n (.hf 0). -/
theorem feat_H (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) :
    L.feat = S.n (.hf 0) := by
  rw [(TiesHead.layout_numbers hy).1.2.2.2.2.1, JV_H hy F]
  show 4 * hH.d + 6 * S.JV = 4 * S.P.d + 6 * S.JV
  rw [F.d]

/-- If Head.layout hH tau returns L and FitsH S hH holds, then L.k = S.kF (.hf 0) and L.kD = S.kF
.hd; and if hH.XL = 5, L.kR = S.kF .hr. -/
theorem k_H (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) :
    L.k = S.kF (.hf 0) ∧ L.kD = S.kF .hd ∧ (hH.XL = 5 → L.kR = S.kF .hr) := by
  obtain ⟨⟨_, _, _, _, _, e1, e2, e3⟩, _⟩ := TiesHead.layout_numbers hy
  obtain ⟨w1, w2, w3⟩ := wc_H hy F
  obtain ⟨p1, p2, p3, p0⟩ := wc_H_pos hy F
  refine ⟨?_, ?_, fun hx => ?_⟩
  · rw [e1, w1, feat_H hy F, ← F.NHf, TiesHead.roundUp_div _ (Nat.mul_pos p0 p1)]
    rfl
  · rw [e2, w2, TiesHead.roundUp_div _ p2, ← F.d]
    show _ = Sz.ceilDiv (2 * S.P.d) (1 * S.wchd)
    rw [Nat.one_mul]
  · rw [e3, w3, TiesHead.roundUp_div _ p3, hx]
    show _ = Sz.ceilDiv Head.nB (1 * S.wchr)
    rw [Nat.one_mul]
    rfl

/-- **The place of a feature of hf.** If Head.layout hH tau returns L and FitsH S hH holds, then
for all φ and t the matrix's name, the row and the column of S.atFeat .head (.hf 0) φ t are .hf of
the part, the row and the column of Hd.placeIn L.k (L.m / hH.T) hH.T φ t. -/
theorem place_hf (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) (φ t : ℕ) :
    ((S.atFeat .head (.hf 0) φ t).2.1, (S.atFeat .head (.hf 0) φ t).2.2.1,
      (S.atFeat .head (.hf 0) φ t).2.2.2) =
      (MatName.hf (Road.Hd.placeIn L.k (L.m / hH.T) hH.T φ t).1,
        (Road.Hd.placeIn L.k (L.m / hH.T) hH.T φ t).2.1,
        (Road.Hd.placeIn L.k (L.m / hH.T) hH.T φ t).2.2) := by
  rw [(k_H hy F).1, (wc_H hy F).1, T_H F]
  rfl

/-- If Head.layout hH tau returns L and FitsH S hH holds, then for all φ and t the matrix's name of
S.atFeat .head .hd φ t is .hd, and its row and column are those of Hd.placeIn L.kD (L.mD / hH.T)
hH.T φ t. -/
theorem place_hd (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) (φ t : ℕ) :
    ((S.atFeat .head .hd φ t).2.1, (S.atFeat .head .hd φ t).2.2.1,
      (S.atFeat .head .hd φ t).2.2.2) =
      (MatName.hd, (Road.Hd.placeIn L.kD (L.mD / hH.T) hH.T φ t).2.1,
        (Road.Hd.placeIn L.kD (L.mD / hH.T) hH.T φ t).2.2) := by
  rw [(k_H hy F).2.1, (wc_H hy F).2.1, T_H F]
  rfl

/-- If Head.layout hH tau returns L and FitsH S hH holds, and hH.XL = 5, then for all φ and t the
matrix's name of S.atFeat .head .hr φ t is .hr, and its row and column are those of Hd.placeIn L.kR
(L.mR / hH.T) hH.T φ t. -/
theorem place_hr (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) (hx : hH.XL = 5)
    (φ t : ℕ) :
    ((S.atFeat .head .hr φ t).2.1, (S.atFeat .head .hr φ t).2.2.1,
      (S.atFeat .head .hr φ t).2.2.2) =
      (MatName.hr, (Road.Hd.placeIn L.kR (L.mR / hH.T) hH.T φ t).2.1,
        (Road.Hd.placeIn L.kR (L.mR / hH.T) hH.T φ t).2.2) := by
  rw [(k_H hy F).2.2 hx, (wc_H hy F).2.2, T_H F]
  rfl

/-- For w > 0 and φ < x: φ / w / Sz.ceilDiv x w = 0. -/
theorem part_eq_zero {x w φ : ℕ} (hw : 0 < w) (hφ : φ < x) : φ / w / Sz.ceilDiv x w = 0 := by
  have h1 := le_ceilDiv_mul x hw
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hφ h1)

/-- If Head.layout hH tau returns L and FitsH S hH holds, then for φ < S.n .hd the part of
Hd.placeIn L.kD (L.mD / hH.T) hH.T φ t is 0. -/
theorem part_hd (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) {φ : ℕ}
    (hφ : φ < S.n .hd) (t : ℕ) : (Road.Hd.placeIn L.kD (L.mD / hH.T) hH.T φ t).1 = 0 := by
  obtain ⟨_, p2, _, _⟩ := wc_H_pos hy F
  show φ / (L.mD / hH.T) / L.kD = 0
  rw [(k_H hy F).2.1, (wc_H hy F).2.1]
  show φ / S.wchd / Sz.ceilDiv (S.n .hd) (1 * S.wchd) = 0
  rw [Nat.one_mul]
  exact part_eq_zero p2 hφ

/-- If Head.layout hH tau returns L and FitsH S hH holds, and hH.XL = 5, then for φ < S.n .hr the
part of Hd.placeIn L.kR (L.mR / hH.T) hH.T φ t is 0. -/
theorem part_hr (hy : Model.Head.layout hH tau = .ok L) (F : FitsH S hH) (hx : hH.XL = 5)
    {φ : ℕ} (hφ : φ < S.n .hr) (t : ℕ) :
    (Road.Hd.placeIn L.kR (L.mR / hH.T) hH.T φ t).1 = 0 := by
  obtain ⟨_, _, p3, _⟩ := wc_H_pos hy F
  show φ / (L.mR / hH.T) / L.kR = 0
  rw [(k_H hy F).2.2 hx, (wc_H hy F).2.2]
  show φ / S.wchr / Sz.ceilDiv (S.n .hr) (1 * S.wchr) = 0
  rw [Nat.one_mul]
  exact part_eq_zero p3 hφ

/-- If hH.XL = 5, the number ledNRH hH.XL of features of hr is S.n .hr. -/
theorem nr_H (hx : hH.XL = 5) : ledNRH hH.XL = S.n .hr := by
  rw [hx]
  rfl

end

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.TiesHead.roundUp_div
#print axioms OnBytes.HonestTrace.TiesHead.layout_numbers
#print axioms OnBytes.HonestTrace.T_H
#print axioms OnBytes.HonestTrace.JV_H
#print axioms OnBytes.HonestTrace.wc_H
#print axioms OnBytes.HonestTrace.wc_H_pos
#print axioms OnBytes.HonestTrace.feat_H
#print axioms OnBytes.HonestTrace.k_H
#print axioms OnBytes.HonestTrace.place_hf
#print axioms OnBytes.HonestTrace.place_hd
#print axioms OnBytes.HonestTrace.place_hr
#print axioms OnBytes.HonestTrace.part_eq_zero
#print axioms OnBytes.HonestTrace.part_hd
#print axioms OnBytes.HonestTrace.part_hr
#print axioms OnBytes.HonestTrace.nr_H

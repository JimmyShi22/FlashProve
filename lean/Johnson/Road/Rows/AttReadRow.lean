-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttReadRow.lean: what the forms on the matrix ah of the attention sub-proof are
worth, in the library's words.

The matrix ah holds, for each row of scores, its maximum, its denominator and the bits of its index.
The verifier reads it through three functions of OnBytes/Model/AttentionClaimsA.lean: readMaximum,
readDenominator and readIndexBit. Each is a sum over the heads of keys and values (overG) of a
number in limbs (shV), read in a table on ah. This file shows: in a world in which every table is
true of the matrices, the form that such a function returns is worth the library's read rd2
(Inst/Model/Att/Sums.lean) of the library's array mxV, denV or ibV, on the cells of the matrices,
under the table's own weights on the positions.

Main definitions: ShapedG (three more fields of a shape that the verifier's function returns).
Main theorems.
 - shapedG_of_shape, shapedG_of_hid.
 - rowLimb_value: a weight of a limb reads as a power of 256.
 - shV_value: a number in limbs. rowOverG_value: the sum over the heads of keys and values.
 - readMaximum_rd2, readDenominator_rd2, readIndexBit_rd2.

Every theorem on a form begins "if the routine returns": none says that it does. Nothing is said
about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttReadLaws
import Johnson.Road.Lane5AttNum
import Johnson.Road.FormsKeysPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HTailF2 eqTab)
open OnBytes.Attention (Shape Heard)
open OnBytes.Road.Hd (Ok colsOf rdW)
open Inst.Model.AttSeg (rd2 mxV denV ibV)

/-! ## Three more fields of a shape -/

/-- What the verifier's function shape returns, beside L5.Shaped. -/
structure ShapedG (S : Shape) : Prop where
  /-- the heads of keys and values -/
  G : S.G = 2 ^ S.cf.lgk
  /-- the side of a tile -/
  B : S.B = 2 ^ S.cf.lB
  /-- the features of a block -/
  ls : S.ls = S.cf.la - S.cf.lt

theorem shapedG_of_shape {cf : Attention.Cfg} {S : Shape}
    (h : Attention.shape cf = Except.ok S) : ShapedG S := by
  unfold Attention.shape at h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨rfl, rfl, rfl⟩

theorem shapedG_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : Attention.shapeHid lid cf = Except.ok (S, fs)) : ShapedG S := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  have e := (Prod.mk.inj (Except.ok.inj h)).1
  have P := shapedG_of_shape hA
  subst e
  exact ⟨P.G, P.B, P.ls⟩

variable {K : Type} [Field K]

/-! ## Limbs -/

/-- The weight of limb l reads as 256^l. -/
theorem rowLimb_value {ρ : Reading K} (N : Numerals ρ) {n l : ℕ} (hl : l < n) :
    ρ.val ((Attention.limbWeights n).getD l zeroE) = 256 ^ l := by
  unfold Attention.limbWeights
  rw [getD_map_lt (Array.range n) _ (by simpa using hl) zeroE 0, N.ofNat]
  simp [hl]

section
variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- The positions of a shape are not none. -/
theorem T_pos (A : AttAt ρ W tl K3 M h lid cf fs) : 0 < h.S.T := by
  rw [(L5.shaped_of_hid A.shape).T]
  exact Nat.two_pow_pos _

/-- **A number in nl limbs, read in a table on ah under the position weights psi.** -/
theorem shV_value (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3) {t : ℕ}
    {psi : Array E} (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi) {off nl J lam j : ℕ} {C : Ctx}
    {q : Aff} {G : Fork} {D : Ctx} (hh : Ok (Attention.shV h t off nl J lam j) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W = ∑ l ∈ range nl, 256 ^ l *
      ∑ i ∈ range h.S.T, ρ.val (psi.getD i zeroE) *
        mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH (off + (l * h.S.Lam + lam) * J + j) i) := by
  have hT := T_pos A
  have hn : (tl.mats.getD h.S.cf.NAs {}).m / h.S.T = h.S.cf.wcH := by
    rw [A.mats.ahM, Nat.mul_div_cancel _ hT]
  have hm : h.S.cf.NAs < tl.NM := by rw [A.mats.nm]; omega
  obtain ⟨e1, e2, -, e4⟩ := weighted_value ρ W nl (Attention.limbWeights nl)
    (fun l => Attention.u3at h t (off + (l * h.S.Lam + lam) * J + j))
    (fun l => ∑ i ∈ range h.S.T, ρ.val (psi.getD i zeroE) *
      mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH (off + (l * h.S.Lam + lam) * J + j) i))
    (fun _ => True)
    (by
      intro l _ x G1 D1 hx
      obtain ⟨a1, a2, a3, a4⟩ := u3at_value ρ W hx
      refine ⟨a1, a2, trivial, ?_⟩
      have hc' : colsOf F h.iU3 = K3 := hc
      rw [a4, hc', tab_read A Tb hm (Nat.ne_of_gt hT) a3, hn]
      rfl)
    hh
  refine ⟨e1, e2, ?_⟩
  rw [e4]
  exact sum_congr rfl fun l hl => by rw [rowLimb_value A.num (mem_range.mp hl)]

/-- **The sum over the heads of keys and values.** -/
theorem rowOverG_value (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} {C : Ctx} {zg : Array E}
    (hz : h.S.cf.lgk ≤ zg.size) (f : ℕ → SubM Aff) (v : ℕ → K)
    (hf : ∀ g < h.S.G, ∀ x G D, Ok (f g) F C x G D → G = F ∧ D = C ∧ x.value ρ W = v g)
    {q : Aff} {G : Fork} {D : Ctx} (hh : Ok (Attention.overG h zg f) F C q G D) :
    G = F ∧ D = C ∧
      q.value ρ W =
        ∑ g ∈ range (2 ^ h.S.cf.lgk), Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * v g := by
  have hG := (shapedG_of_hid A.shape).G
  obtain ⟨e1, e2, -, e4⟩ := weighted_value ρ W h.S.G (eqTab (zg.extract 0 h.S.cf.lgk)) f v
    (fun _ => True)
    (fun g hg x G1 D1 hx => by
      obtain ⟨a1, a2, a3⟩ := hf g hg x G1 D1 hx
      exact ⟨a1, a2, trivial, a3⟩)
    hh
  refine ⟨e1, e2, ?_⟩
  have hs : (zg.extract 0 h.S.cf.lgk).size = h.S.cf.lgk := by
    rw [Array.size_extract]
    omega
  rw [e4, hG]
  refine sum_congr rfl fun g hg => ?_
  have hg' : g < 2 ^ (zg.extract 0 h.S.cf.lgk).size := by rw [hs]; exact mem_range.mp hg
  rw [eqTab_value ρ _ g hg', hs]
  congr 1
  unfold Blocks.eqN
  refine prod_congr rfl fun k hk => ?_
  have hk' : k < h.S.cf.lgk := mem_range.mp hk
  have e : pt ρ (zg.extract 0 h.S.cf.lgk) (0 + k) = pt ρ zg (0 + k) := by
    unfold pt
    rw [Nat.zero_add, getD_extract zg hz (by omega), Nat.zero_add]
  rw [e]

/-- The library's number of positions is the shape's. -/
theorem dim_T (A : AttAt ρ W tl K3 M h lid cf fs) : (L5.dimOf h.S).T = h.S.T := by
  have P := L5.shaped_of_hid A.shape
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have N := L5.norm_of_shaped P (L5.tested_of_shape hS0).1 (L5.tested_of_shape hS0).2
  rw [(L5.dimOf h.S).T_eq, P.T, ← P.cfg]
  show 2 ^ (h.S.lnT - 1 + 1 + h.S.cf.lB) = 2 ^ h.S.cf.lt
  rw [← N.lt]

/-- **A form on ah, summed over the heads of keys and values, is the library's read of the array
that its limbs spell.** jOf g: the feature within a limb of a layer, at head g. arr: the array. -/
theorem limbs_rd2 (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3) {t : ℕ}
    {psi : Array E} (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi) {zg : Array E}
    (hz : h.S.cf.lgk ≤ zg.size) {off nl J lam : ℕ} (jOf : ℕ → ℕ) (arr : ℕ → ℕ → K)
    (harr : ∀ g i, arr g i = ∑ l ∈ range nl, 256 ^ l *
      mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH (off + (l * h.S.Lam + lam) * J + jOf g) i))
    {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}
    (hh : Ok (Attention.overG h zg fun g => Attention.shV h t off nl J lam (jOf g)) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (psi.getD i zeroE)) arr := by
  obtain ⟨e1, e2, e⟩ := rowOverG_value A hz _
    (fun g => ∑ l ∈ range nl, 256 ^ l * ∑ i ∈ range h.S.T, ρ.val (psi.getD i zeroE) *
      mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH (off + (l * h.S.Lam + lam) * J + jOf g) i))
    (fun g _ x G1 D1 hx => shV_value A hc Tb hx) hh
  refine ⟨e1, e2, ?_⟩
  rw [e]
  unfold rd2
  rw [dim_T A]
  refine sum_congr rfl fun g _ => ?_
  simp only [harr, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun l _ => by
    show Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * _ = Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * _ * _
    ring

/-- Pair number lam HA + a is the layer lam and the head a. -/
theorem pair_parts {HA lam a : ℕ} (ha : a < HA) :
    (lam * HA + a) / HA = lam ∧ (lam * HA + a) % HA = a :=
  Inst.Model.AttSeg.Dim.div_step (Nat.lt_of_le_of_lt (Nat.zero_le _) ha) ha

variable {F : Fork} {t : ℕ} {psi zg : Array E} {lam a : ℕ} {C : Ctx} {q : Aff} {G : Fork}
  {D : Ctx}

/-- **The row maximum.** -/
theorem readMaximum_rd2 (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi) (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    (hh : Ok (Attention.readMaximum h t zg lam a) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (psi.getD i zeroE))
        (mxV (cellsK h.S M) (lam * h.S.HA + a)) := by
  have hb := pair_parts (lam := lam) ha
  refine limbs_rd2 A hc Tb hz (fun g => g * h.S.HA + a) _ (fun g i => ?_) hh
  show ∑ k ∈ range 4, 256 ^ k * mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH
    (h.S.oMr + (k * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.cf.H +
      (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA)) i) = _
  rw [hb.1, hb.2]

/-- **The denominator.** -/
theorem readDenominator_rd2 (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi) (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    (hh : Ok (Attention.readDenominator h t zg lam a) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (psi.getD i zeroE))
        (denV (cellsK h.S M) (lam * h.S.HA + a)) := by
  have hb := pair_parts (lam := lam) ha
  refine limbs_rd2 A hc Tb hz (fun g => g * h.S.HA + a) _ (fun g i => ?_) hh
  show ∑ k ∈ range 4, 256 ^ k * mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH
    (h.S.oZr + (k * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.cf.H +
      (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA)) i) = _
  rw [hb.1, hb.2]

/-- **A bit of the index.** -/
theorem readIndexBit_rd2 (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi) (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    {k : ℕ} (hh : Ok (Attention.readIndexBit h t zg lam a k) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (psi.getD i zeroE))
        (ibV (cellsK h.S M) k (lam * h.S.HA + a)) := by
  have hb := pair_parts (lam := lam) ha
  refine limbs_rd2 A hc Tb hz (fun g => k * h.S.cf.H + g * h.S.HA + a) _ (fun g i => ?_) hh
  show mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH
    (h.S.oIb + (0 * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + (lam * h.S.HA + a) % h.S.HA)) i) = _
  rw [hb.1, hb.2, sum_range_one, pow_zero, one_mul]

end

end OnBytes.Road.Rows

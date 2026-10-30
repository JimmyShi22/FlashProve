-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds14Proofs.lean: proofs of the statements of
Johnson/Road/Rows/AttEnds14.lean.

Each statement says that two claims of the attention sub-proof, in a world in which every table is
true of the matrices, make two end values of a sumcheck the library's maps Aext and Bext on the
cells. A proof has three parts: the verifier's form is a read of the library (AttReadRow.lean,
AttReadHead.lean); the library's map is such a read (Cb/Pv/Att/Mean/ReadsTiles.lean); the two have
the same points and weights.

Main theorems: ten_dvd, qa_aligned; readHead_qry, readHead_out, readGroup_key, readGroup_val;
eqTab_eqT; productEnd.

Nothing is said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttEnds14
import Johnson.Road.Rows.AttReadHead
import Cb.Pv.Att.Mean.ReadsTiles
import Johnson.Road.Rows.AttTiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HFun HTailF2 TenAt tenCell eqTab blockRows)
open OnBytes.Attention (Shape Heard sc3A sc3B)
open OnBytes.Road.Hd (Ok)
open Inst.Model.AttSeg (rd2 rd3 eqT sh qryV outV keyV valV denV Aext Bext)

variable {K : Type} [Field K]

/-! ## The tensors of the matrix qa -/

/-- A cell of a tensor stands at a multiple of P if the tensor's first feature, the features of a
layer and the tensor's own feature do. -/
theorem ten_dvd {P : ℕ} {X : TenAt} (h1 : P ∣ X.off) (h2 : P ∣ X.J) {j : ℕ} (h3 : P ∣ j)
    (l i : ℕ) : P ∣ tenCell X l i j := by
  unfold Model.tenCell
  exact Nat.dvd_add (Nat.dvd_add h1 (Dvd.dvd.mul_left h2 _)) h3

/-- The four tensors of qa begin at a block's first feature, and so does each of their layers and
heads. -/
theorem qa_aligned {S : Shape} (N : L5.Norm S) (Z : Sizes S) (l lam hd : ℕ) :
    2 ^ S.ls ∣ tenCell S.atQ l lam (hd * S.dh) ∧ 2 ^ S.ls ∣ tenCell S.atK l lam (hd * S.dh) ∧
      2 ^ S.ls ∣ tenCell S.atV l lam (hd * S.dh) ∧ 2 ^ S.ls ∣ tenCell S.atO l lam (hd * S.dh) := by
  have hp : 2 ^ S.ls ∣ 2 ^ S.cf.ldh := pow_dvd_pow 2 Z.ls
  have hd' : 2 ^ S.ls ∣ hd * S.dh := by
    rw [N.dh]
    exact Dvd.dvd.mul_left hp _
  refine ⟨ten_dvd ?_ ?_ hd' l lam, ten_dvd ?_ ?_ hd' l lam, ten_dvd ?_ ?_ hd' l lam,
    ten_dvd ?_ ?_ hd' l lam⟩
  · rw [N.atQ]
    exact Nat.dvd_zero _
  · rw [N.atQ]
    exact Dvd.dvd.mul_left hp _
  · rw [N.atK]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hp _) _
  · rw [N.atK]
    exact Dvd.dvd.mul_left hp _
  · rw [N.atV]
    exact Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hp _) _)
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left hp _) _)
  · rw [N.atV]
    exact Dvd.dvd.mul_left hp _
  · rw [N.atO]
    exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hp _) _)
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left hp _) _)) (Dvd.dvd.mul_left (Dvd.dvd.mul_left hp _) _)
  · rw [N.atO]
    exact Dvd.dvd.mul_left hp _

section Forms

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {F : Fork} {t : ℕ} {zg zc tok : Array E} {lam a : ℕ} {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}

/-- The matrix qa is in the list. -/
theorem qa_lt (A : AttAt ρ W tl K3 M h lid cf fs) : h.S.cf.NAs + 3 < tl.NM := by
  rw [A.mats.nm]
  omega

/-- The queries. -/
theorem readHead_qry (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (ha : a < h.S.HA) (hq : Ok (Attention.readHead h t h.S.atQ zg zc lam a) F C q G D) :
    q.value ρ W = rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
      (qryV (cellsK h.S M) (lam * h.S.HA + a)) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  have hnl : h.S.atQ.nl = 2 := by rw [N.atQ]
  refine head_rd3 A hc (fun g => g * h.S.HA + a) Tb (qa_lt A) A.mats.qaM Z.wcQ htok hzg hzc
    (fun g l => (qa_aligned N Z l lam _).1) _ (fun g i n => ?_) hq
  show ∑ k ∈ range 2, 256 ^ k * mAt M (L5.featCell h.S (h.S.cf.NAs + 3) h.S.cf.wcQ
    (tenCell h.S.atQ k ((lam * h.S.HA + a) / h.S.HA)
      ((g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) * h.S.dh) + n) i) = _
  rw [hb.1, hb.2, hnl]

/-- The outputs. -/
theorem readHead_out (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (ha : a < h.S.HA) (hq : Ok (Attention.readHead h t h.S.atO zg zc lam a) F C q G D) :
    q.value ρ W = rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
      (outV (cellsK h.S M) (lam * h.S.HA + a)) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  have hnl : h.S.atO.nl = 2 := by rw [N.atO]
  refine head_rd3 A hc (fun g => g * h.S.HA + a) Tb (qa_lt A) A.mats.qaM Z.wcQ htok hzg hzc
    (fun g l => (qa_aligned N Z l lam _).2.2.2) _ (fun g i n => ?_) hq
  show ∑ k ∈ range 2, 256 ^ k * mAt M (L5.featCell h.S (h.S.cf.NAs + 3) h.S.cf.wcQ
    (tenCell h.S.atO k ((lam * h.S.HA + a) / h.S.HA)
      ((g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) * h.S.dh) + n) i) = _
  rw [hb.1, hb.2, hnl]

/-- The keys. -/
theorem readGroup_key (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hq : Ok (Attention.readGroup h t h.S.atK zg zc lam) F C q G D) :
    q.value ρ W = rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
      (keyV (cellsK h.S M) lam) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hnl : h.S.atK.nl = 2 := by rw [N.atK]
  refine head_rd3 A hc (fun g => g) Tb (qa_lt A) A.mats.qaM Z.wcQ htok hzg hzc
    (fun g l => (qa_aligned N Z l lam _).2.1) _ (fun g i n => ?_) hq
  show ∑ k ∈ range 2, 256 ^ k * mAt M (L5.featCell h.S (h.S.cf.NAs + 3) h.S.cf.wcQ
    (tenCell h.S.atK k lam (g * h.S.dh) + n) i) = _
  rw [hnl]

/-- The values. -/
theorem readGroup_val (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hq : Ok (Attention.readGroup h t h.S.atV zg zc lam) F C q G D) :
    q.value ρ W = rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
      (valV (cellsK h.S M) lam) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hnl : h.S.atV.nl = 2 := by rw [N.atV]
  refine head_rd3 A hc (fun g => g) Tb (qa_lt A) A.mats.qaM Z.wcQ htok hzg hzc
    (fun g l => (qa_aligned N Z l lam _).2.2.1) _ (fun g i n => ?_) hq
  show ∑ k ∈ range 2, 256 ^ k * mAt M (L5.featCell h.S (h.S.cf.NAs + 3) h.S.cf.wcQ
    (tenCell h.S.atV k lam (g * h.S.dh) + n) i) = _
  rw [hnl]

/-- The number of bits of a position. -/
theorem dimLT (A : AttAt ρ W tl K3 M h lid cf fs) : (L5.dimOf h.S).lT = h.S.cf.lt :=
  (norm_of_hid A.shape).lt.symm

/-- The equality weights of a stretch of lt coordinates of a point are the library's equality vector
over the positions. -/
theorem eqTab_eqT (A : AttAt ρ W tl K3 M h lid cf fs) (r : Array E) (off : ℕ)
    (hr : off + h.S.cf.lt ≤ r.size) {i : ℕ} (hi : i < (L5.dimOf h.S).T) :
    ρ.val ((eqTab (r.extract off (off + h.S.cf.lt))).getD i zeroE) =
      eqT (L5.dimOf h.S) (sh (pt ρ r) off) i := by
  have hlT := dimLT A
  have s1 : (r.extract off (off + h.S.cf.lt)).size = h.S.cf.lt := by
    rw [Array.size_extract]
    omega
  have hi2 : i < 2 ^ (r.extract off (off + h.S.cf.lt)).size := by
    rw [s1, ← hlT, ← Inst.Model.AttSeg.Dim.T_eq]
    exact hi
  unfold eqT
  rw [eqTab_value ρ _ i hi2, s1, hlT]
  refine eqN_agree (fun k hk => ?_) i
  unfold pt sh
  rw [Nat.zero_add, getD_extract r hr (by omega)]

end Forms

/-! ## The denominator times the output -/

/-- The end values of the sumcheck for the denominator times the output. -/
theorem productEnd : ProductEnd := by
  intro K _ ρ W tl K3 M h lid cf fs C p b w z o F F' G G' c c1 c' c1' A hc hc' hr hzc ha hyn
    TbE TbO hz ho vz vo
  have hr' : h.d.scE.r.size = h.S.cf.lgk + h.S.cf.lt := hr
  have hT := dim_T A
  have es : (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))).size = h.S.T := by
    rw [eqTab_size, (sizes_of_hid A.shape).T]
    congr 1
    rw [Array.size_extract]
    omega
  obtain ⟨-, -, e1⟩ := readDenominator_rd2 A hc TbE (by omega) ha (ok_of_yields hz)
  have e2 := readHead_out A hc' TbO es (by omega) hzc ha (ok_of_yields ho)
  have s1 : (sc3A h.d.scE b).value ρ W = W.slot (h.d.scE.sEnd + 2 * b) := Aff.value_slot ρ W _
  have s2 : (sc3B h.d.scE b).value ρ W = W.slot (h.d.scE.sEnd + (2 * b + 1)) :=
    Aff.value_slot ρ W _
  rw [Aff.value_sub, s1, e1, sub_eq_zero] at vz
  rw [Aff.value_sub, s2, e2, sub_eq_zero] at vo
  refine ⟨?_, ?_⟩
  · rw [vz, aext8]
    unfold rd2
    refine sum_congr rfl fun g _ => sum_congr rfl fun i hi => ?_
    beta_reduce
    rw [eqTab_eqT A h.d.scE.r h.S.cf.lgk (by omega) (mem_range.mp hi)]
    rfl
  · rw [vo, bext8]
    exact rd3_congr _ (fun _ _ => rfl)
      (fun i hi => eqTab_eqT A h.d.scE.r h.S.cf.lgk (by omega) hi) hyn _

end OnBytes.Road.Rows

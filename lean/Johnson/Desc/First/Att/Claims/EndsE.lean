-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsE.lean: kind K5: the four tensors' readers on "qa", and the end
values of "denominator × output": twins, for the written forms, of readHead_qry, readHead_out,
readGroup_key, readGroup_val and ProductEnd (Johnson/Road/Rows/AttEnds14Proofs.lean,
AttEnds14.lean), which speak of a run of a routine in a context. The proofs' pure parts follow those
proofs line for line.

Main names:
  `InLong h t X lam hdOf zc`: what those proofs take from the run's return: at each head of keys and
    values the head's features are lawful and the blocks read lie in the table.
  `readHeadT_qry`, `readHeadT_out`, `readGroupT_key`, `readGroupT_val`: ‹written form›.value ρ W =
    rd3 (L5.dimOf h.S) (pt ρ zg) (the table's token weights, read) (pt ρ zc) (qryV, outV, keyV, valV
    (cellsK h.S M) …).
  `product_ends`: W.slot (scE.sEnd + 2 b) = Aext … .s8 (w.lam HA + w.a) (pt ρ scE.r) ∧ W.slot
    (scE.sEnd + (2 b + 1)) = Bext … .s8 ….
What these reach, and what not: as the head of Johnson/Desc/First/Att/Claims/EndsQ.lean says.
Used: as Johnson/Desc/First/Att/Claims/EndsQ.lean, and qa_lt, qa_aligned, eqTab_eqT, aext8, bext8;
the library's outV, denV.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds14Proofs
import Johnson.Desc.First.Att.Claims.MeanRd3

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Calls Pub rd2 rd3 eqT sh qryV outV keyV valV denV Aext Bext)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- What the proofs of Johnson/Road/Rows take from the run's return, at a long table. -/
structure InLong (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam : ℕ) (hdOf : ℕ → ℕ) (zc : Array E) :
    Prop where
  feat : ∀ g < 2 ^ h.S.cf.lgk, headFeat X (hdOf g) h.S.dh = .ok (hdOf g * h.S.dh)
  inn : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < (hiOf h.S zc).size, ∀ l < X.nl,
    tenCell X l lam (hdOf g * h.S.dh) / 2 ^ h.S.ls + ch < (h.t.tabLen.lookup t).getD 0

variable {t : ℕ} {zg zc tok : Array E} {lam a : ℕ}

/-- The queries. -/
theorem readHeadT_qry (A : AttAt ρ W tl K3 M h lid cf fs)
    (Tb : TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (ha : a < h.S.HA) (I : InLong h t h.S.atQ lam (fun g => g * h.S.HA + a) zc) :
    (Fo.readHeadT h K3 t h.S.atQ zg zc lam a).value ρ W =
      rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
        (qryV (cellsK h.S M) (lam * h.S.HA + a)) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  have hnl : h.S.atQ.nl = 2 := by rw [N.atQ]
  unfold Fo.readHeadT
  refine headF_rd3 A (fun g => g * h.S.HA + a) Tb (qa_lt A) A.mats.qaM Z.wcQ htok hzg hzc
    (fun g l => (qa_aligned N Z l lam _).1) _ (fun g i n => ?_) I.feat I.inn
  show ∑ k ∈ range 2, 256 ^ k * mAt M (L5.featCell h.S (h.S.cf.NAs + 3) h.S.cf.wcQ
    (tenCell h.S.atQ k ((lam * h.S.HA + a) / h.S.HA)
      ((g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) * h.S.dh) + n) i) = _
  rw [hb.1, hb.2, hnl]

/-- The outputs. -/
theorem readHeadT_out (A : AttAt ρ W tl K3 M h lid cf fs)
    (Tb : TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (ha : a < h.S.HA) (I : InLong h t h.S.atO lam (fun g => g * h.S.HA + a) zc) :
    (Fo.readHeadT h K3 t h.S.atO zg zc lam a).value ρ W =
      rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
        (outV (cellsK h.S M) (lam * h.S.HA + a)) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  have hnl : h.S.atO.nl = 2 := by rw [N.atO]
  unfold Fo.readHeadT
  refine headF_rd3 A (fun g => g * h.S.HA + a) Tb (qa_lt A) A.mats.qaM Z.wcQ htok hzg hzc
    (fun g l => (qa_aligned N Z l lam _).2.2.2) _ (fun g i n => ?_) I.feat I.inn
  show ∑ k ∈ range 2, 256 ^ k * mAt M (L5.featCell h.S (h.S.cf.NAs + 3) h.S.cf.wcQ
    (tenCell h.S.atO k ((lam * h.S.HA + a) / h.S.HA)
      ((g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) * h.S.dh) + n) i) = _
  rw [hb.1, hb.2, hnl]

/-- The keys. -/
theorem readGroupT_key (A : AttAt ρ W tl K3 M h lid cf fs)
    (Tb : TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (I : InLong h t h.S.atK lam (fun g => g) zc) :
    (Fo.readGroupT h K3 t h.S.atK zg zc lam).value ρ W =
      rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
        (keyV (cellsK h.S M) lam) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hnl : h.S.atK.nl = 2 := by rw [N.atK]
  unfold Fo.readGroupT
  refine headF_rd3 A (fun g => g) Tb (qa_lt A) A.mats.qaM Z.wcQ htok hzg hzc
    (fun g l => (qa_aligned N Z l lam _).2.1) _ (fun g i n => ?_) I.feat I.inn
  show ∑ k ∈ range 2, 256 ^ k * mAt M (L5.featCell h.S (h.S.cf.NAs + 3) h.S.cf.wcQ
    (tenCell h.S.atK k lam (g * h.S.dh) + n) i) = _
  rw [hnl]

/-- The values. -/
theorem readGroupT_val (A : AttAt ρ W tl K3 M h lid cf fs)
    (Tb : TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (I : InLong h t h.S.atV lam (fun g => g) zc) :
    (Fo.readGroupT h K3 t h.S.atV zg zc lam).value ρ W =
      rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
        (valV (cellsK h.S M) lam) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hnl : h.S.atV.nl = 2 := by rw [N.atV]
  unfold Fo.readGroupT
  refine headF_rd3 A (fun g => g) Tb (qa_lt A) A.mats.qaM Z.wcQ htok hzg hzc
    (fun g l => (qa_aligned N Z l lam _).2.2.1) _ (fun g i n => ?_) I.feat I.inn
  show ∑ k ∈ range 2, 256 ^ k * mAt M (L5.featCell h.S (h.S.cf.NAs + 3) h.S.cf.wcQ
    (tenCell h.S.atV k lam (g * h.S.dh) + n) i) = _
  rw [hnl]

/-- **The twin of ProductEnd**: the end values of "denominator × output". -/
theorem product_ends (A : AttAt ρ W tl K3 M h lid cf fs) (C : Calls) (p : Pub Kf) {b : ℕ} {w : PW}
    (hr : h.d.scE.r.size = h.S.nvE) (hzc : h.d.zcW.size = h.S.cf.ldh) (ha : w.a < h.S.HA)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j)
    (TbE : TabAt tl h h.t.hE h.S.cf.NAs h.S.T
      (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))))
    (TbO : TabAt tl h h.t.qO (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S h.d.zcW)
        (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt)))))
    (hinE : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, h.S.oZr + (l * h.S.Lam + w.lam) * h.S.cf.H +
      (g * h.S.HA + w.a) < (h.t.tabLen.lookup h.t.hE).getD 0)
    (IO : InLong h h.t.qO h.S.atO w.lam (fun g => g * h.S.HA + w.a) h.d.zcW)
    (vz : W.slot (h.d.scE.sEnd + 2 * b) =
      (Fo.readDenominatorF h K3 h.t.hE h.d.scE.r w.lam w.a).value ρ W)
    (vo : W.slot (h.d.scE.sEnd + (2 * b + 1)) =
      (Fo.readHeadT h K3 h.t.qO h.S.atO h.d.scE.r h.d.zcW w.lam w.a).value ρ W) :
    W.slot (h.d.scE.sEnd + 2 * b) =
        Aext (L5.dimOf h.S) C p (cellsK h.S M) .s8 (w.lam * h.S.HA + w.a) (pt ρ h.d.scE.r) ∧
      W.slot (h.d.scE.sEnd + (2 * b + 1)) =
        Bext (L5.dimOf h.S) C p (cellsK h.S M) .s8 (w.lam * h.S.HA + w.a) (pt ρ h.d.scE.r) := by
  have hr' : h.d.scE.r.size = h.S.cf.lgk + h.S.cf.lt := hr
  have hT := dim_T A
  have es : (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))).size = h.S.T := by
    rw [OnBytes.Road.eqTab_size, (sizes_of_hid A.shape).T]
    congr 1
    rw [Array.size_extract]
    omega
  have hzg : h.S.cf.lgk ≤ h.d.scE.r.size := by omega
  have e1 := readDenominatorF_rd2 A TbE hzg ha hinE
  have e2 := readHeadT_out A TbO es hzg hzc ha IO
  rw [e1] at vz
  rw [e2] at vo
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

end K5Law

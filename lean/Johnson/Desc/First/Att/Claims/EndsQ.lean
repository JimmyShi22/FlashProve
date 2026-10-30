-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsQ.lean: kind K5: twins, for the written forms, of ScoreAtIndexEnd
and KeyAtIndexEndK (Johnson/Road/Rows/AttEnds58.lean; proved in
Johnson/Road/Rows/AttEnds58ProofsQ.lean of a run of a routine in a context): the first end values of
the score at the index are the queries of the library's step s16; the key's end values for the
layers are the library's rvKC. The proofs follow those proofs line for line, with headF_rd3
(Johnson/Desc/First/Att/Claims/MeanRd3.lean) where head_rd3 stood.

Main names:
  `score_query`: W.slot (scF.sEnd + 2 b) = Aext (L5.dimOf h.S) C p (cellsK h.S M) .s16 b (pt ρ
    scF.r).
  `key_keys`: W.slot (sKC + lam) = rvKC (L5.dimOf h.S) p (cellsK h.S M) (pt ρ scd.r) lam. With
    key_bits (Johnson/Desc/First/Att/Claims/MeanRd.lean): all end values of the key's sumcheck.
What these reach, and what not: they end at the library's own maps on cellsK h.S M (the cells read
in the matrices M at the addresses of Johnson/Road/Lane5AttDef.lean) at the verifier's own points.
EndsMean (Johnson/Desc/First/Att/K5Mean.lean) speaks of S.T.map D.st (S.msg m) x at the output's
point: that P.rd (P.msg m) is cellsK h.S M, and that the typed state's points are these, is not made
here.
Premises beyond those of Johnson/Road/Rows, which takes both from the run's return: headFeat … =
.ok; the indices read lie in the table.
Used: as Johnson/Desc/First/Att/Claims/MeanRd3.lean, and QaAt, norm_of_hid, tensor_dvd, ls_dvd,
head_dvd, eqTab_vec, rd3_congr, aext16, size_cut, pt_extract, dim_lT; the library's Aext, rvKC,
qryV, keyV.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds58ProofsQ
import Johnson.Desc.First.Att.Claims.MeanRd3

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Dim Calls Pub rd3 eqT sh qryV keyV valV rvKC Aext)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- **The twin of ScoreAtIndexEnd.** -/
theorem score_query (A : AttAt ρ W tl K3 M h lid cf fs) (C : Calls) (p : Pub Kf) {b : ℕ}
    (hr : h.x.scF.r.size = h.S.nvF) (Tb : QaAt tl h h.t.qF (h.x.rc h.S) (eqTab (h.x.ri h.S)))
    (hfeat : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atQ (g * h.S.HA + b % h.S.HA) h.S.dh =
      .ok ((g * h.S.HA + b % h.S.HA) * h.S.dh))
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < (hiOf h.S (h.x.rc h.S)).size, ∀ l < h.S.atQ.nl,
      tenCell h.S.atQ l (b / h.S.HA) ((g * h.S.HA + b % h.S.HA) * h.S.dh) / 2 ^ h.S.ls + ch <
        (h.t.tabLen.lookup h.t.qF).getD 0)
    (hval : W.slot (h.x.scF.sEnd + 2 * b) = (Fo.readHeadT h K3 h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S)
      (b / h.S.HA) (b % h.S.HA)).value ρ W) :
    W.slot (h.x.scF.sEnd + 2 * b) =
      Aext (L5.dimOf h.S) C p (cellsK h.S M) .s16 b (pt ρ h.x.scF.r) := by
  have hlT := dim_lT A
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hr' : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh := hr
  have s1 : (h.x.rg h.S).size = h.S.cf.lgk := by
    show (h.x.scF.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.ri h.S).size = h.S.cf.lt := by
    show (h.x.scF.r.extract 0 h.S.cf.lt).size = _
    rw [size_cut _ (by omega)]
    omega
  have s3 : (h.x.rc h.S).size = h.S.cf.ldh := by
    show (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size).size = _
    rw [size_cut _ (Nat.le_refl _)]
    omega
  have hT : (eqTab (h.x.ri h.S)).size = h.S.T := by rw [OnBytes.Road.eqTab_size, s2, Z.T]
  have e := headF_rd3 A (fun g => g * h.S.HA + b % h.S.HA) Tb (by rw [A.mats.nm]; omega)
    A.mats.qaM Z.wcQ hT (Nat.le_of_eq s1.symm) s3
    (fun g l => tensor_dvd (by rw [N.atQ]; exact Nat.dvd_zero _)
      (by rw [N.atQ]; exact Dvd.dvd.mul_left (ls_dvd A) _) l _ (head_dvd A _))
    (qryV (cellsK h.S M) b)
    (fun g i n => by
      have e2 : h.S.atQ.nl = 2 := by rw [N.atQ]
      rw [e2]
      rfl)
    hfeat hin
  unfold Fo.readHeadT at hval
  rw [hval, e, aext16]
  refine rd3_congr _ (fun j hj => ?_) (fun i hi => ?_) (fun j hj => ?_) _
  · show pt ρ (h.x.scF.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
      pt ρ h.x.scF.r ((L5.dimOf h.S).lT + j)
    have hj' : j < h.S.cf.lgk := hj
    rw [hlT]
    exact pt_extract ρ _ (by omega) (by omega)
  · refine eqTab_vec A s2 (fun j hj => ?_) hi
    show pt ρ (h.x.scF.r.extract 0 h.S.cf.lt) j = pt ρ h.x.scF.r j
    rw [pt_extract ρ _ (by omega) (by omega), Nat.zero_add]
  · show pt ρ (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size) j =
      pt ρ h.x.scF.r ((L5.dimOf h.S).lT + h.S.cf.lgk + j)
    have hj' : j < h.S.cf.ldh := hj
    rw [hlT]
    exact pt_extract ρ _ (Nat.le_refl _) (by omega)

/-- **The twin of KeyAtIndexEndK.** -/
theorem key_keys (A : AttAt ρ W tl K3 M h lid cf fs) (p : Pub Kf) {lam : ℕ}
    (hrF : h.x.scF.r.size = h.S.nvF) (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    (hfn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = p.fn j)
    (Tb : QaAt tl h h.t.qKx (h.x.rc h.S) (eqTab (h.x.pj h.S)))
    (hfeat : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atK g h.S.dh = .ok (g * h.S.dh))
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < (hiOf h.S (h.x.rc h.S)).size, ∀ l < h.S.atK.nl,
      tenCell h.S.atK l lam (g * h.S.dh) / 2 ^ h.S.ls + ch < (h.t.tabLen.lookup h.t.qKx).getD 0)
    (hval : W.slot (h.x.sKC + lam) =
      (Fo.readGroupT h K3 h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) lam).value ρ W) :
    W.slot (h.x.sKC + lam) = rvKC (L5.dimOf h.S) p (cellsK h.S M) (pt ρ h.x.scd.r) lam := by
  have hlT := dim_lT A
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hrF' : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh := hrF
  have s1 : (h.x.pg h.S).size = h.S.cf.lgk := by
    show (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.pj h.S).size = h.S.cf.lt := by
    show (h.x.scd.r.extract 0 h.S.cf.lt).size = _
    rw [size_cut _ (by omega)]
    omega
  have s3 : (h.x.rc h.S).size = h.S.cf.ldh := by
    show (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size).size = _
    rw [size_cut _ (Nat.le_refl _)]
    omega
  have hT : (eqTab (h.x.pj h.S)).size = h.S.T := by rw [OnBytes.Road.eqTab_size, s2, Z.T]
  have e := headF_rd3 A (fun g => g) Tb (by rw [A.mats.nm]; omega)
    A.mats.qaM Z.wcQ hT (Nat.le_of_eq s1.symm) s3
    (fun g l => tensor_dvd
      (by rw [N.atK]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (ls_dvd A) _) _)
      (by rw [N.atK]; exact Dvd.dvd.mul_left (ls_dvd A) _) l _ (head_dvd A _))
    (keyV (cellsK h.S M) lam)
    (fun g i n => by
      have e2 : h.S.atK.nl = 2 := by rw [N.atK]
      rw [e2]
      rfl)
    hfeat hin
  unfold Fo.readGroupT at hval
  rw [hval, e]
  show _ = rd3 (L5.dimOf h.S) (sh (pt ρ h.x.scd.r) (L5.dimOf h.S).lT)
    (eqT (L5.dimOf h.S) (pt ρ h.x.scd.r)) p.fn (keyV (cellsK h.S M) lam)
  refine rd3_congr _ (fun j hj => ?_) (fun i hi => ?_) (fun j hj => hfn j hj) _
  · show pt ρ (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
      pt ρ h.x.scd.r ((L5.dimOf h.S).lT + j)
    have hj' : j < h.S.cf.lgk := hj
    rw [hlT]
    exact pt_extract ρ _ (by omega) (by omega)
  · refine eqTab_vec A s2 (fun j hj => ?_) hi
    show pt ρ (h.x.scd.r.extract 0 h.S.cf.lt) j = pt ρ h.x.scd.r j
    rw [pt_extract ρ _ (by omega) (by omega), Nat.zero_add]

end K5Law

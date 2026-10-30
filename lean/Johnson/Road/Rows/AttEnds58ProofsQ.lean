-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds58ProofsQ.lean: proofs of statements of Johnson/Road/Rows/AttEnds58.lean.

Proved here: two statements whose claims read the matrix qa: ScoreAtIndexEnd (scoreAtIndexEnd) and
KeyAtIndexEndK (keyAtIndexEndK).

The way. Johnson/Road/Rows/AttReadHead.lean values the verifier's form on a tensor of qa as the
library's read rd3, under the table's own weights on the positions (head_rd3). It asks that the
tensor begins at a block's first feature: tensor_dvd. The library's maps are such reads (aext16 in
Cb/Pv/Att/Mean/Reads.lean; rvKC by definition). What is left is to compare the points and the
weights on the positions: eqTab_vec.


-/
import Johnson.Road.Rows.AttEnds58Proofs
import Johnson.Road.Rows.AttReadHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HTailF2 TenAt tenCell eqTab)
open OnBytes.Attention (Shape Heard sc3A sc3B)
open Inst.Model.AttSeg (Dim rd3 eqT sh qryV keyV valV rvKC)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A feature of a tensor is a multiple of P if the tensor's first feature, the features of a layer
and the tensor's own feature are. -/
theorem tensor_dvd {P : ℕ} {X : TenAt} (h1 : P ∣ X.off) (h2 : P ∣ X.J) (l lam : ℕ) {j : ℕ}
    (h3 : P ∣ j) : P ∣ tenCell X l lam j :=
  Nat.dvd_add (Nat.dvd_add h1 (Dvd.dvd.mul_left h2 _)) h3

section
variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- A block's features divide a head's. -/
theorem ls_dvd (A : AttAt ρ W tl K3 M h lid cf fs) : 2 ^ h.S.ls ∣ 2 ^ h.S.cf.ldh :=
  pow_dvd_pow 2 (sizes_of_hid A.shape).ls

/-- A head's first feature in its tensor is a block's first. -/
theorem head_dvd (A : AttAt ρ W tl K3 M h lid cf fs) (hd : ℕ) : 2 ^ h.S.ls ∣ hd * h.S.dh := by
  rw [(norm_of_hid A.shape).dh]
  exact Dvd.dvd.mul_left (ls_dvd A) _

/-- The weights of a table at the equality weights of a point are the library's equality vector
over the positions. -/
theorem eqTab_vec (A : AttAt ρ W tl K3 M h lid cf fs) {zi : Array E} {ui : ℕ → K}
    (hi : zi.size = h.S.cf.lt) (hu : ∀ j < h.S.cf.lt, pt ρ zi j = ui j) {i : ℕ}
    (h' : i < (L5.dimOf h.S).T) :
    ρ.val ((eqTab zi).getD i zeroE) = eqT (L5.dimOf h.S) ui i := by
  have hlT := dim_lT A
  have hi2 : i < 2 ^ zi.size := by
    rw [hi, ← hlT, ← Dim.T_eq]
    exact h'
  unfold eqT
  rw [eqTab_value ρ zi i hi2, hi, hlT]
  exact eqN_agree (fun k hk => by rw [Nat.zero_add]; exact hu k hk) i

end

/-! ## The score at the index: the queries -/

/-- **ScoreAtIndexEnd holds.** -/
theorem scoreAtIndexEnd : ScoreAtIndexEnd := by
  intro K _ ρ W tl K3 M h F lid cf fs C p b q G c c1 A hc hr hb Tb hrun hval
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
  have hT : (eqTab (h.x.ri h.S)).size = h.S.T := by rw [eqTab_size, s2, Z.T]
  have e := head_rd3 A hc (fun g => g * h.S.HA + b % h.S.HA) Tb (by rw [A.mats.nm]; omega)
    A.mats.qaM Z.wcQ hT (Nat.le_of_eq s1.symm) s3
    (fun g l => tensor_dvd (by rw [N.atQ]; exact Nat.dvd_zero _)
      (by rw [N.atQ]; exact Dvd.dvd.mul_left (ls_dvd A) _) l _ (head_dvd A _))
    (qryV (cellsK h.S M) b)
    (fun g i n => by
      have e2 : h.S.atQ.nl = 2 := by rw [N.atQ]
      rw [e2]
      rfl)
    (ok_of_yields hrun)
  have e0 : (sc3A h.x.scF b).value ρ W = W.slot (h.x.scF.sEnd + 2 * b) := Aff.value_slot ρ W _
  rw [Aff.value_sub, e0, e, sub_eq_zero] at hval
  rw [hval, aext16]
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

/-! ## The key at the index: the keys -/

/-- **KeyAtIndexEndK holds.** -/
theorem keyAtIndexEndK : KeyAtIndexEndK := by
  intro K _ ρ W tl K3 M h F lid cf fs p lam kx G c c1 A hc hrF hr _ hfn Tb hrun hval
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
  have hT : (eqTab (h.x.pj h.S)).size = h.S.T := by rw [eqTab_size, s2, Z.T]
  have e := head_rd3 A hc (fun g => g) Tb (by rw [A.mats.nm]; omega)
    A.mats.qaM Z.wcQ hT (Nat.le_of_eq s1.symm) s3
    (fun g l => tensor_dvd
      (by rw [N.atK]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (ls_dvd A) _) _)
      (by rw [N.atK]; exact Dvd.dvd.mul_left (ls_dvd A) _) l _ (head_dvd A _))
    (keyV (cellsK h.S M) lam)
    (fun g i n => by
      have e2 : h.S.atK.nl = 2 := by rw [N.atK]
      rw [e2]
      rfl)
    (ok_of_yields hrun)
  rw [Aff.value_sub, Aff.value_slot, e, sub_eq_zero] at hval
  rw [hval]
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

end OnBytes.Road.Rows

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortFirst.lean: the forms that the verifier's claims 4, 5 and 6 of an attention
sub-proof read on the end values of the first four sumchecks are the library-side reading forms, at
any values of the late entries.

As Johnson/Road/Rows/AttPortLate.lean, for the reading forms of Cb/Pv/Att/End/First.lean: rA6b,
rB6b, rA6d, rB6d (the scores of a unit below and on the diagonal), rA8, rB8 (the denominator times
the output), rA11, rB11 (the value product below the diagonal). No table is taken to be true.

Main definitions: FirstTabs h tbM tbD tabOf: where the eight tables of these claims begin. tbM, tbD:
the tables of the unit below the diagonal and of the unit on it.
Main theorems.
 - head_port, group_port: readHead and readGroup, for a tensor and the names of its cells, against
   rdLong at the verifier's own points.
 - unit_port: the query and the key of a unit of the scores, for both kinds of units: rA6b, rB6b,
   rA6d and rB6d are its right sides, by their definitions.
 - den_port, out_port, valueM_port, weightM_port.

What the theorems take as given, and what is not claimed: as in Johnson/Road/Rows/AttPortLate.lean.
With this file the places of eight more tables are shown to be the numbers at which the verifier's
functions read: tQm, tKm, tQd, tKd, hE, qO, tVM, qVM.


-/
import Johnson.Road.Rows.AttPortLate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork SubM TenAt eqTab ofNat)
open OnBytes.Attention (Heard Score ScoreTables)
open OnBytes.Road.Hd (Ok)
open Inst.Model.AttSeg (Raw Calls Pub sh yn)
open Cb.Pv.Att (ptBelow)
open Cb.Pv.Att.End (LateLay AttTab rdRow rdLong rdCol rdRow_congr rdLong_congr rdCol_congr rA6b
  rB6b rA6d rB6d rA8 rB8 rA11 rB11 val_aSmul val_aAdd val_aConst)

variable {K : Type} [Field K]

/-- Where the eight tables of the claims 4, 5 and 6 on the end values of the first four sumchecks
begin. -/
structure FirstTabs (h : Heard) (tbM tbD : ScoreTables) (tabOf : AttTab → ℕ) : Prop where
  tQm : tabOf .tQm = tbM.tQ
  tKm : tabOf .tKm = tbM.tK
  tQd : tabOf .tQd = tbD.tQ
  tKd : tabOf .tKd = tbD.tK
  hE : tabOf .hE = h.t.hE
  qO : tabOf .qO = h.t.qO
  tVM : tabOf .tVM = h.t.tVM
  qVM : tabOf .qVM = h.t.qVM

section
variable {ρ : Reading K} {W : World K} {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → K} (m : J₁ → K)
  {F : Fork} {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}

/-! ## A tensor with features for each query head, or for each head of keys and values -/

/-- readHead against rdLong. mk l g n: the name of the cell of limb l, head g of keys and values and
feature n, at position 0, for the pair lam HA + a. -/
theorem head_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (T : AttTab) {t : ℕ} (ht : tabOf T = t)
    {X : TenAt} {nl : ℕ} (hnl : X.nl = nl) {zg zc : Array E} {lam a : ℕ} (mk : ℕ → ℕ → ℕ → Raw)
    (hadd : ∀ l g c, (mk l g 0).addN c = mk l g (0 + c))
    (hpl : ∀ l < nl, ∀ g n, placeAtt h.S T (mk l g n) = placeTen h.S X l lam (g * h.S.HA + a) n)
    (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < nl,
      Y.good (T, (mk l g 0).addN (ch * 2 ^ h.S.ls)))
    (hh : Ok (Attention.readHead h t X zg zc lam a) F C q G D) :
    q.value ρ W = (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T (pt ρ zg) (pt ρ zc) nl
      fun l g => mk l g 0).val (Sum.elim m u) := by
  rw [← ht] at hh
  rw [head_long m A hc L T (fun g => g * h.S.HA + a) hzg hzc (fun l g => mk l g 0)
    (by rw [hnl]; exact hg)
    (fun g ch l hl => by
      rw [hadd, hpl l (by rw [← hnl]; exact hl)]
      unfold placeTen
      rw [blk_div]) hh, hnl]

/-- readGroup against rdLong. -/
theorem group_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (T : AttTab) {t : ℕ} (ht : tabOf T = t)
    {X : TenAt} {nl : ℕ} (hnl : X.nl = nl) {zg zc : Array E} {lam : ℕ} (mk : ℕ → ℕ → ℕ → Raw)
    (hadd : ∀ l g c, (mk l g 0).addN c = mk l g (0 + c))
    (hpl : ∀ l < nl, ∀ g n, placeAtt h.S T (mk l g n) = placeTen h.S X l lam g n)
    (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < nl,
      Y.good (T, (mk l g 0).addN (ch * 2 ^ h.S.ls)))
    (hh : Ok (Attention.readGroup h t X zg zc lam) F C q G D) :
    q.value ρ W = (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T (pt ρ zg) (pt ρ zc) nl
      fun l g => mk l g 0).val (Sum.elim m u) := by
  rw [← ht] at hh
  rw [head_long m A hc L T (fun g => g) hzg hzc (fun l g => mk l g 0)
    (by rw [hnl]; exact hg)
    (fun g ch l hl => by
      rw [hadd, hpl l (by rw [← hnl]; exact hl)]
      unfold placeTen
      rw [blk_div]) hh, hnl]

/-! ## The scores of a unit -/

/-- The last ldh coordinates of a unit's point. n: the coordinates before them. -/
theorem last_pt {r : Array E} {n : ℕ} (hr : r.size = n + h.S.cf.ldh) {ξ : ℕ → K}
    (hξ : ∀ j < n + h.S.cf.ldh, ξ j = pt ρ r j) {j : ℕ} (hj : j < h.S.cf.ldh) :
    pt ρ (r.extract (r.size - h.S.cf.ldh) r.size) j = sh ξ n j := by
  show _ = ξ (n + j)
  rw [hξ _ (by omega), pt_extract ρ _ (Nat.le_refl _) (by omega)]
  exact congrArg _ (by omega)

/-- The query and the key of a unit, in one statement for both kinds of units. T, T': the tables'
names; n: the coordinates of the unit's point before the features'. -/
theorem unit_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) {k : Score} {tb : ScoreTables} (T T' : AttTab)
    (hT : tabOf T = tb.tQ) (hT' : tabOf T' = tb.tK) (hpT : placeAtt h.S T = placeLong h.S)
    (hpT' : placeAtt h.S T' = placeLong h.S) (hq2 : h.S.atQ.nl = 2) (hk2 : h.S.atK.nl = 2)
    {n : ℕ} (hn : h.S.cf.lgk ≤ n) (hr : k.sc.r.size = n + h.S.cf.ldh) {ξ : ℕ → K}
    (hξ : ∀ j < n + h.S.cf.ldh, ξ j = pt ρ k.sc.r j) {lam a : ℕ} (ha : a < h.S.HA)
    (hgQ : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (T, (Raw.qry l (lam * h.S.HA + a) g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hgK : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (T', (Raw.key l lam g 0 0).addN (ch * 2 ^ h.S.ls)))
    {q' : Aff} {F' G' : Fork} {C' D' : Ctx} (hc' : Cols F' h K3)
    (hh : Ok (Attention.readHead h tb.tQ h.S.atQ k.sc.r
      (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) lam a) F C q G D)
    (hh' : Ok (Attention.readGroup h tb.tK h.S.atK k.sc.r
      (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) lam) F' C' q' G' D') :
    q.value ρ W = (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T ξ (sh ξ n) 2
        fun l g => .qry l (lam * h.S.HA + a) g 0 0).val (Sum.elim m u) ∧
      q'.value ρ W = (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T' ξ (sh ξ n) 2
        fun l g => .key l lam g 0 0).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  have s2 : (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size).size = h.S.cf.ldh := by
    rw [size_cut _ (Nat.le_refl _)]
    omega
  constructor
  · rw [head_port m A hc L T hT hq2 (fun l g n => .qry l (lam * h.S.HA + a) g 0 n)
      (fun _ _ _ => rfl)
      (fun l _ g n => by
        rw [hpT]
        show placeTen h.S h.S.atQ l ((lam * h.S.HA + a) / h.S.HA)
          (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) n = _
        rw [hb.1, hb.2]) (by omega) s2 hgQ hh]
    exact rdLong_congr _ _ _ _ _ (fun j hj => (hξ j (by
      have hj' : j < h.S.cf.lgk := hj
      omega)).symm) (fun j hj => last_pt hr hξ (by
      have hj' : j < h.S.cf.ldh - h.S.ls := hj
      omega)) _ _
  · rw [group_port m A hc' L T' hT' hk2 (fun l g n => .key l lam g 0 n) (fun _ _ _ => rfl)
      (fun l _ g n => by
        rw [hpT']
        rfl) (by omega) s2 hgK hh']
    exact rdLong_congr _ _ _ _ _ (fun j hj => (hξ j (by
      have hj' : j < h.S.cf.lgk := hj
      omega)).symm) (fun j hj => last_pt hr hξ (by
      have hj' : j < h.S.cf.ldh - h.S.ls := hj
      omega)) _ _

/-! ## The denominator times the output -/

/-- The denominator of claim 5. ξ: the point of the denominator times the output. -/
theorem den_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .hE = h.t.hE) {ξ : ℕ → K}
    {lam a : ℕ} (ha : a < h.S.HA) (hr : h.S.cf.lgk ≤ h.d.scE.r.size)
    (hξ : ∀ j < h.S.cf.lgk, ξ j = pt ρ h.d.scE.r j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (.hE, .den l (lam * h.S.HA + a) g 0))
    (hh : Ok (Attention.readDenominator h h.t.hE h.d.scE.r lam a) F C q G D) :
    q.value ρ W =
      (rA8 (J₁ := J₁) (L5.dimOf h.S) Y ξ (lam * h.S.HA + a)).val (Sum.elim m u) := by
  rw [← hT] at hh
  rw [readDenominator_row m A hc L .hE rfl hr ha hg hh]
  exact rdRow_congr _ _ _ _ (fun j hj => (hξ j hj).symm) _ _

/-- The output of claim 5. -/
theorem out_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .qO = h.t.qO) {Cc : Calls}
    {p : Pub K} {ξ : ℕ → K} {lam a : ℕ} (ha : a < h.S.HA) (hnl : h.S.atO.nl = 2)
    (hr : h.S.cf.lgk ≤ h.d.scE.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ξ j = pt ρ h.d.scE.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc p.z j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qO, (Raw.out l (lam * h.S.HA + a) g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hh : Ok (Attention.readHead h h.t.qO h.S.atO h.d.scE.r h.d.zcW lam a) F C q G D) :
    q.value ρ W = (rB8 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.ls Y p ξ (lam * h.S.HA + a)).val
      (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  rw [head_port m A hc L .qO hT hnl (fun l g n => .out l (lam * h.S.HA + a) g 0 n)
    (fun _ _ _ => rfl)
    (fun l _ g n => by
      show placeTen h.S h.S.atO l ((lam * h.S.HA + a) / h.S.HA)
        (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) n = _
      rw [hb.1, hb.2]) hr hzc hg hh]
  exact rdLong_congr _ _ _ _ _ (fun j hj => (hξ j hj).symm) (fun j hj => hyn j (by
    have hj' : j < h.S.cf.ldh - h.S.ls := hj
    omega)) _ _

/-! ## The value product below the diagonal -/

/-- The value of claim 6, below the diagonal. ξ: the point of the value product there. -/
theorem valueM_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .qVM = h.t.qVM) {Cc : Calls}
    {p : Pub K} {ξ : ℕ → K} {b lam : ℕ} (hlam : (L5.dimOf h.S).lamOf b = lam)
    (hnl : h.S.atV.nl = 2) (hr : h.S.cf.lgk ≤ h.d.vpm.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ξ j = pt ρ h.d.vpm.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc p.z j)
    (hgam : ρ.val h.d.gam = p.th)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qVM, (Raw.val l lam g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hh : Ok (Attention.readGroup h h.t.qVM h.S.atV h.d.vpm.r h.d.zcW lam) F C q G D) :
    (Aff.ofConst h.d.gam + q).value ρ W =
      (rB11 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.ls Y p ξ b).val (Sum.elim m u) := by
  unfold Cb.Pv.Att.End.rB11
  rw [Aff.value_add, Aff.value_ofConst, hgam, val_aAdd, val_aConst, hlam,
    group_port m A hc L .qVM hT hnl (fun l g n => .val l lam g 0 n) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) hr hzc hg hh]
  congr 1
  exact rdLong_congr _ _ _ _ _ (fun j hj => (hξ j hj).symm) (fun j hj => hyn j (by
    have hj' : j < h.S.cf.ldh - h.S.ls := hj
    omega)) _ _

/-- The softmax weight of claim 6, below the diagonal. p3, p4: the forms of the two planes. -/
theorem weightM_port (hN : Numerals ρ) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .tVM = h.t.tVM) {Cc : Calls}
    {p : Pub K} {ξ : ℕ → K} {lam a : ℕ} (ha : a < h.S.HA) (hnM : (L5.dimOf h.S).lM = h.S.nM)
    (hz : h.t.ptM.size = h.S.nM)
    (hpt : ∀ j < h.S.nM - h.S.cf.lmS, pt ρ h.t.ptM j = ptBelow (L5.dimOf h.S) Cc p ξ j)
    (hg : ∀ jj < 5, ∀ hi < 2 ^ (h.S.nM - h.S.cf.lmS),
      Y.good (.tVM, (Raw.c .M jj (lam * h.S.HA + a) 0).addX (hi * 2 ^ h.S.cf.lmS)))
    {p3 p4 : Aff} {F' G' : Fork} {C' D' : Ctx} (hc' : Cols F' h K3)
    (h3 : Ok (Attention.plane h h.t.tVM 3 lam a h.t.ptM false) F C p3 G D)
    (h4 : Ok (Attention.plane h h.t.tVM 4 lam a h.t.ptM false) F' C' p4 G' D') :
    (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256)).value ρ W =
      (rA11 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.cf.lmS Y p ξ (lam * h.S.HA + a)).val
        (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  rw [← hT] at h3 h4
  have pl : ∀ x hi, placeAtt h.S .tVM
      ((Raw.c .M x (lam * h.S.HA + a) 0).addX (hi * 2 ^ h.S.cf.lmS)) =
      planeFirst h.S x lam a false >>> h.S.cf.lmS + hi := by
    intro x hi
    show planeFirst h.S x ((lam * h.S.HA + a) / h.S.HA) ((lam * h.S.HA + a) % h.S.HA) false >>>
      h.S.cf.lmS + (0 + hi * 2 ^ h.S.cf.lmS) / 2 ^ h.S.cf.lmS = _
    rw [hb.1, hb.2, blk_div]
  have i0 : (if false = true then h.S.nD else h.S.nM) = h.S.nM := if_neg (by simp)
  have e3 := plane_col (ρ := ρ) m hc L .tVM (nb := h.S.nM) i0 hz
    (.c .M 3 (lam * h.S.HA + a) 0) (hg 3 (by norm_num)) (pl 3) h3
  have e4 := plane_col (ρ := ρ) m hc' L .tVM (nb := h.S.nM) i0 hz
    (.c .M 4 (lam * h.S.HA + a) 0) (hg 4 (by norm_num)) (pl 4) h4
  unfold Cb.Pv.Att.End.rA11
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale, hN.ofNat, hN.ofNat, e3, e4,
    val_aAdd, val_aAdd, val_aConst, val_aSmul, hnM,
    rdCol_congr _ _ _ _ _ hpt, rdCol_congr _ _ _ _ _ hpt]
  push_cast
  ring

end

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.unit_port
#print axioms OnBytes.Road.Rows.den_port
#print axioms OnBytes.Road.Rows.out_port
#print axioms OnBytes.Road.Rows.valueM_port
#print axioms OnBytes.Road.Rows.weightM_port

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortFirst.lean: kind K5: the written forms that claims 4, 5 and 6 read
on the end values of the first four sumchecks are the library-side reading forms
(Cb/Pv/Att/End/First.lean: rA6b, rB6b, rA6d, rB6d, rA8, rB8, rA11, rB11), at any values of the late
entries. Twins of head_port, group_port, unit_port, den_port, out_port, valueM_port and weightM_port
(Johnson/Road/Rows/AttPortFirst.lean), which speak of a run of a routine in a context ("if the
routine returns"). No table is taken to be true. The proofs follow those proofs line for line, with
the lemma of Johnson/Desc/First/Att/Claims/PortRow.lean or
Johnson/Desc/First/Att/Claims/PortLong.lean where the run's stood.

Main names: `headF_port`, `groupF_port`, `unitF_port` (rA6b, rB6b, rA6d and rB6d are its right
sides, by their definitions), `denF_port`, `outF_port`, `valueMF_port`, `weightMF_port`.
Premise beyond those of Johnson/Road/Rows: the heads' features are lawful.
Used: as Johnson/Desc/First/Att/Claims/PortLate.lean, and FirstTabs, last_pt, ptBelow; the library's
rA6b … rB11.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttPortFirst
import Johnson.Desc.First.Att.Claims.PortLate

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Calls Pub sh yn)
open Cb.Pv.Att (ptBelow)
open Cb.Pv.Att.End (LateLay AttTab rdRow rdLong rdCol rdRow_congr rdLong_congr rdCol_congr rA6b
  rB6b rA6d rB6d rA8 rB8 rA11 rB11 val_aSmul val_aAdd val_aConst)

variable {Kf : Type} [Field Kf]

section
variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → Kf} (m : J₁ → Kf)

/-- readHead's written form against rdLong. mk l g n: the name of the cell of limb l, head g of keys and values and feature n, at position 0, for the pair lam HA + a. -/
theorem headF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (T : AttTab) {t : ℕ} (ht : tabOf T = t)
    {X : TenAt} {nl : ℕ} (hnl : X.nl = nl) {zg zc : Array E} {lam a : ℕ} (mk : ℕ → ℕ → ℕ → Raw)
    (hadd : ∀ l g c, (mk l g 0).addN c = mk l g (0 + c))
    (hpl : ∀ l < nl, ∀ g n, placeAtt h.S T (mk l g n) = placeTen h.S X l lam (g * h.S.HA + a) n)
    (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < nl,
      Y.good (T, (mk l g 0).addN (ch * 2 ^ h.S.ls)))
    (hf : ∀ g < 2 ^ h.S.cf.lgk, headFeat X (g * h.S.HA + a) h.S.dh = .ok ((g * h.S.HA + a) * h.S.dh)) :
    (Fo.readHeadT h K3 t X zg zc lam a).value ρ W =
      (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T (pt ρ zg) (pt ρ zc) nl
        fun l g => mk l g 0).val (Sum.elim m u) := by
  rw [← ht]
  unfold Fo.readHeadT
  rw [headF_long m A L T (fun g => g * h.S.HA + a) hzg hzc (fun l g => mk l g 0)
    (by rw [hnl]; exact hg)
    (fun g ch l hl => by
      rw [hadd, hpl l (by rw [← hnl]; exact hl)]
      unfold placeTen
      rw [blk_div]) hf, hnl]

/-- readGroup's written form against rdLong. -/
theorem groupF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (T : AttTab) {t : ℕ} (ht : tabOf T = t)
    {X : TenAt} {nl : ℕ} (hnl : X.nl = nl) {zg zc : Array E} {lam : ℕ} (mk : ℕ → ℕ → ℕ → Raw)
    (hadd : ∀ l g c, (mk l g 0).addN c = mk l g (0 + c))
    (hpl : ∀ l < nl, ∀ g n, placeAtt h.S T (mk l g n) = placeTen h.S X l lam g n)
    (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < nl,
      Y.good (T, (mk l g 0).addN (ch * 2 ^ h.S.ls)))
    (hf : ∀ g < 2 ^ h.S.cf.lgk, headFeat X g h.S.dh = .ok (g * h.S.dh)) :
    (Fo.readGroupT h K3 t X zg zc lam).value ρ W =
      (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T (pt ρ zg) (pt ρ zc) nl
        fun l g => mk l g 0).val (Sum.elim m u) := by
  rw [← ht]
  unfold Fo.readGroupT
  rw [headF_long m A L T (fun g => g) hzg hzc (fun l g => mk l g 0)
    (by rw [hnl]; exact hg)
    (fun g ch l hl => by
      rw [hadd, hpl l (by rw [← hnl]; exact hl)]
      unfold placeTen
      rw [blk_div]) hf, hnl]

/-- The query and the key of a unit, in one statement for both kinds of units. T, T': the tables' names; n: the coordinates of the unit's point before the features'. -/
theorem unitF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) {k : Score} {tb : ScoreTables} (T T' : AttTab)
    (hT : tabOf T = tb.tQ) (hT' : tabOf T' = tb.tK) (hpT : placeAtt h.S T = placeLong h.S)
    (hpT' : placeAtt h.S T' = placeLong h.S) (hq2 : h.S.atQ.nl = 2) (hk2 : h.S.atK.nl = 2)
    {n : ℕ} (hn : h.S.cf.lgk ≤ n) (hr : k.sc.r.size = n + h.S.cf.ldh) {ξ : ℕ → Kf}
    (hξ : ∀ j < n + h.S.cf.ldh, ξ j = pt ρ k.sc.r j) {lam a : ℕ} (ha : a < h.S.HA)
    (hgQ : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (T, (Raw.qry l (lam * h.S.HA + a) g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hgK : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (T', (Raw.key l lam g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hfQ : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atQ (g * h.S.HA + a) h.S.dh =
      .ok ((g * h.S.HA + a) * h.S.dh))
    (hfK : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atK g h.S.dh = .ok (g * h.S.dh)) :
    (Fo.readHeadT h K3 tb.tQ h.S.atQ k.sc.r
        (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) lam a).value ρ W =
      (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T ξ (sh ξ n) 2
        fun l g => .qry l (lam * h.S.HA + a) g 0 0).val (Sum.elim m u) ∧
    (Fo.readGroupT h K3 tb.tK h.S.atK k.sc.r
        (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) lam).value ρ W =
      (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T' ξ (sh ξ n) 2
        fun l g => .key l lam g 0 0).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  have s2 : (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size).size = h.S.cf.ldh := by
    rw [size_cut _ (Nat.le_refl _)]
    omega
  constructor
  · rw [headF_port m A L T hT hq2 (fun l g n => .qry l (lam * h.S.HA + a) g 0 n)
      (fun _ _ _ => rfl)
      (fun l _ g n => by
        rw [hpT]
        show placeTen h.S h.S.atQ l ((lam * h.S.HA + a) / h.S.HA)
          (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) n = _
        rw [hb.1, hb.2]) (by omega) s2 hgQ hfQ]
    exact rdLong_congr _ _ _ _ _ (fun j hj => (hξ j (by
      have hj' : j < h.S.cf.lgk := hj
      omega)).symm) (fun j hj => last_pt hr hξ (by
      have hj' : j < h.S.cf.ldh - h.S.ls := hj
      omega)) _ _
  · rw [groupF_port m A L T' hT' hk2 (fun l g n => .key l lam g 0 n) (fun _ _ _ => rfl)
      (fun l _ g n => by
        rw [hpT']
        rfl) (by omega) s2 hgK hfK]
    exact rdLong_congr _ _ _ _ _ (fun j hj => (hξ j (by
      have hj' : j < h.S.cf.lgk := hj
      omega)).symm) (fun j hj => last_pt hr hξ (by
      have hj' : j < h.S.cf.ldh - h.S.ls := hj
      omega)) _ _

/-- The denominator of claim 5. ξ: the point of the denominator times the output. -/
theorem denF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .hE = h.t.hE) {ξ : ℕ → Kf}
    {lam a : ℕ} (ha : a < h.S.HA) (hr : h.S.cf.lgk ≤ h.d.scE.r.size)
    (hξ : ∀ j < h.S.cf.lgk, ξ j = pt ρ h.d.scE.r j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (.hE, .den l (lam * h.S.HA + a) g 0)) :
    (Fo.readDenominatorF h K3 h.t.hE h.d.scE.r lam a).value ρ W =
      (rA8 (J₁ := J₁) (L5.dimOf h.S) Y ξ (lam * h.S.HA + a)).val (Sum.elim m u) := by
  rw [← hT]
  rw [readDenominatorF_row m A L .hE rfl hr ha hg]
  exact rdRow_congr _ _ _ _ (fun j hj => (hξ j hj).symm) _ _

/-- The output of claim 5. -/
theorem outF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .qO = h.t.qO) {Cc : Calls}
    {p : Pub Kf} {ξ : ℕ → Kf} {lam a : ℕ} (ha : a < h.S.HA) (hnl : h.S.atO.nl = 2)
    (hr : h.S.cf.lgk ≤ h.d.scE.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ξ j = pt ρ h.d.scE.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc p.z j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qO, (Raw.out l (lam * h.S.HA + a) g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hf : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atO (g * h.S.HA + a) h.S.dh =
      .ok ((g * h.S.HA + a) * h.S.dh)) :
    (Fo.readHeadT h K3 h.t.qO h.S.atO h.d.scE.r h.d.zcW lam a).value ρ W =
      (rB8 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.ls Y p ξ (lam * h.S.HA + a)).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  rw [headF_port m A L .qO hT hnl (fun l g n => .out l (lam * h.S.HA + a) g 0 n)
    (fun _ _ _ => rfl)
    (fun l _ g n => by
      show placeTen h.S h.S.atO l ((lam * h.S.HA + a) / h.S.HA)
        (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) n = _
      rw [hb.1, hb.2]) hr hzc hg hf]
  exact rdLong_congr _ _ _ _ _ (fun j hj => (hξ j hj).symm) (fun j hj => hyn j (by
    have hj' : j < h.S.cf.ldh - h.S.ls := hj
    omega)) _ _

/-- The value of claim 6, below the diagonal. ξ: the point of the value product there. -/
theorem valueMF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .qVM = h.t.qVM) {Cc : Calls}
    {p : Pub Kf} {ξ : ℕ → Kf} {b lam : ℕ} (hlam : (L5.dimOf h.S).lamOf b = lam)
    (hnl : h.S.atV.nl = 2) (hr : h.S.cf.lgk ≤ h.d.vpm.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ξ j = pt ρ h.d.vpm.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc p.z j)
    (hgam : ρ.val h.d.gam = p.th)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qVM, (Raw.val l lam g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hf : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atV g h.S.dh = .ok (g * h.S.dh)) :
    (Aff.ofConst h.d.gam + Fo.readGroupT h K3 h.t.qVM h.S.atV h.d.vpm.r h.d.zcW lam).value ρ W =
      (rB11 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.ls Y p ξ b).val (Sum.elim m u) := by
  unfold Cb.Pv.Att.End.rB11
  rw [Aff.value_add, Aff.value_ofConst, hgam, val_aAdd, val_aConst, hlam,
    groupF_port m A L .qVM hT hnl (fun l g n => .val l lam g 0 n) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) hr hzc hg hf]
  congr 1
  exact rdLong_congr _ _ _ _ _ (fun j hj => (hξ j hj).symm) (fun j hj => hyn j (by
    have hj' : j < h.S.cf.ldh - h.S.ls := hj
    omega)) _ _

/-- The softmax weight of claim 6, below the diagonal. -/
theorem weightMF_port (hN : Numerals ρ)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .tVM = h.t.tVM) {Cc : Calls}
    {p : Pub Kf} {ξ : ℕ → Kf} {lam a : ℕ} (ha : a < h.S.HA) (hnM : (L5.dimOf h.S).lM = h.S.nM)
    (hz : h.t.ptM.size = h.S.nM)
    (hpt : ∀ j < h.S.nM - h.S.cf.lmS, pt ρ h.t.ptM j = ptBelow (L5.dimOf h.S) Cc p ξ j)
    (hg : ∀ jj < 5, ∀ hi < 2 ^ (h.S.nM - h.S.cf.lmS),
      Y.good (.tVM, (Raw.c .M jj (lam * h.S.HA + a) 0).addX (hi * 2 ^ h.S.cf.lmS))) :
    (Fo.planeF h K3 h.t.tVM 3 lam a h.t.ptM false + Aff.ofConst (ofNat 128) +
      Aff.scale (Fo.planeF h K3 h.t.tVM 4 lam a h.t.ptM false) (ofNat 256)).value ρ W =
      (rA11 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.cf.lmS Y p ξ (lam * h.S.HA + a)).val
        (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  rw [← hT]
  have pl : ∀ x hi, placeAtt h.S .tVM
      ((Raw.c .M x (lam * h.S.HA + a) 0).addX (hi * 2 ^ h.S.cf.lmS)) =
      Rows.planeFirst h.S x lam a false >>> h.S.cf.lmS + hi := by
    intro x hi
    show Rows.planeFirst h.S x ((lam * h.S.HA + a) / h.S.HA) ((lam * h.S.HA + a) % h.S.HA) false >>>
      h.S.cf.lmS + (0 + hi * 2 ^ h.S.cf.lmS) / 2 ^ h.S.cf.lmS = _
    rw [hb.1, hb.2, blk_div]
  have i0 : (if false = true then h.S.nD else h.S.nM) = h.S.nM := if_neg (by simp)
  have e3 := planeF_col (ρ := ρ) m L .tVM (x := 3) (lam := lam) (a := a) (z := h.t.ptM) (isD := false)
    (nb := h.S.nM) i0 hz (.c .M 3 (lam * h.S.HA + a) 0) (hg 3 (by norm_num)) (pl 3)
  have e4 := planeF_col (ρ := ρ) m L .tVM (x := 4) (lam := lam) (a := a) (z := h.t.ptM) (isD := false)
    (nb := h.S.nM) i0 hz (.c .M 4 (lam * h.S.HA + a) 0) (hg 4 (by norm_num)) (pl 4)
  unfold Cb.Pv.Att.End.rA11
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale, hN.ofNat, hN.ofNat, e3, e4,
    val_aAdd, val_aAdd, val_aConst, val_aSmul, hnM,
    rdCol_congr _ _ _ _ _ hpt, rdCol_congr _ _ _ _ _ hpt]
  push_cast
  ring

end

end K5Law

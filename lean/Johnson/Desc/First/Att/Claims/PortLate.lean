-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortLate.lean: kind K5: the written forms that claims 6, 7 and 8 read
are the library-side reading forms of the last four sumchecks (Cb/Pv/Att/End/Last.lean: rM6, rIBP,
rA21, rA16, rKC, rB12, rA12), at any values of the late entries. Twins of max_port, ibit_port,
bits_port, query_port, key_port, value_port and weight_port (Johnson/Road/Rows/AttPortLate.lean),
which speak of a run of a routine in a context ("if the routine returns"). No table is taken to be
true; the tie is the dictionary LateAt at the places placeAtt, with LateTabs (where the seven tables
begin). The proofs follow those proofs line for line, with the lemma of
Johnson/Desc/First/Att/Claims/PortRow.lean or Johnson/Desc/First/Att/Claims/PortLong.lean where the
run's stood; the fold in bitsF_port is foldl_pos (Johnson/Desc/First/Att/Claims/Worth.lean).

Main names: `maxF_port`, `ibitF_port`, `bitsF_port` (of bitsF,
Johnson/Desc/First/Att/Claims/Say58.lean: the weighted bits of pair b's index are worth rA21 with 4
variables for the number of a bit), `queryF_port`, `keyF_port`, `valueF_port`, `weightF_port`.
Premise beyond those of Johnson/Road/Rows: the heads' features are lawful (queryF_port, keyF_port,
valueF_port).
Used: as Johnson/Desc/First/Att/Claims/PortLong.lean, and placeAtt, placeLong, placeTen, placeCol,
blk_div, LateTabs, pub_lT, size_cut, pt_extract, heads_pos, lt_le_16, eqN_agree; the library's rM6 …
rB12, ptOn, rdRow_congr, rdLong_congr, rdCol_congr, val_aSum, val_aSmul, val_aAdd, val_aConst.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttPortLate
import Johnson.Desc.First.Att.Claims.PortLong
import Johnson.Desc.First.Att.Claims.Say58

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw Calls Pub sh yn)
open Cb.Pv.Att (eqN_agree)
open Cb.Pv.Att.End (LateLay AttTab rdRow rdLong rdCol rdRow_congr rdLong_congr rdCol_congr rM6
  rA16 rKC rIBP rA21 rA12 rB12 ptOn val_aSum val_aSmul val_aAdd val_aConst)

variable {Kf : Type} [Field Kf]

section
variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → Kf} (m : J₁ → Kf)

/-- The row maximum of claim 7. -/
theorem maxF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {p : Pub Kf} {b : ℕ}
    (hb : b < h.S.NP) (htg : h.x.tg.size = h.S.cf.lgk)
    (hp : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (.hT, .mx l b g 0)) :
    (Fo.readMaximumF h K3 h.t.hT h.x.tg (b / h.S.HA) (b % h.S.HA)).value ρ W =
      (rM6 (J₁ := J₁) (L5.dimOf h.S) Y p b).val (Sum.elim m u) := by
  have e0 : b / h.S.HA * h.S.HA + b % h.S.HA = b := Nat.div_add_mod' b h.S.HA
  rw [← Tb.hT]
  rw [readMaximumF_row m A L .hT rfl (Nat.le_of_eq htg.symm) (Nat.mod_lt b (heads_pos hb))
    (by rw [e0]; exact hg), e0]
  exact rdRow_congr _ _ _ _ hp _ _

/-- A bit of the index, of claim 7. ξ: the point of the key at the index. -/
theorem ibitF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {ξ : ℕ → Kf} {b k : ℕ}
    (hb : b < h.S.NP) (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    (hξ : ∀ j < 2 * h.S.cf.lt + h.S.cf.lgk, ξ j = pt ρ h.x.scd.r j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, Y.good (.hPi, .ib k b g 0)) :
    (Fo.readIndexBitF h K3 h.t.hPi (h.x.pg h.S) (b / h.S.HA) (b % h.S.HA) k).value ρ W =
      (rIBP (J₁ := J₁) (L5.dimOf h.S) Y ξ b k).val (Sum.elim m u) := by
  have e0 : b / h.S.HA * h.S.HA + b % h.S.HA = b := Nat.div_add_mod' b h.S.HA
  have hlT := pub_lT A
  have s1 : (h.x.pg h.S).size = h.S.cf.lgk := by
    show (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  rw [← Tb.hPi]
  rw [readIndexBitF_row m A L .hPi rfl (Nat.le_of_eq s1.symm) (Nat.mod_lt b (heads_pos hb))
    (by rw [e0]; exact hg), e0]
  refine rdRow_congr _ _ _ _ (fun j hj => ?_) _ _
  have hj' : j < h.S.cf.lgk := hj
  show pt ρ (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j = ξ ((L5.dimOf h.S).lT + j)
  rw [hlT, hξ _ (by omega)]
  exact pt_extract ρ _ (by omega) (by omega)

/-- The weighted bits of pair b's index are worth what rA21, with 4 variables for the number of a bit, is worth. ξ: the point of the sumcheck for the bits. -/
theorem bitsF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {ξ : ℕ → Kf} {b : ℕ}
    (hb : b < h.S.NP) (hr : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + 4, ξ j = pt ρ h.x.scH.r j)
    (hg : ∀ k < h.S.cf.lt, ∀ g < 2 ^ h.S.cf.lgk, Y.good (.hR2, .ib k b g 0)) :
    (bitsF h K3 b).value ρ W = (rA21 (J₁ := J₁) (L5.dimOf h.S) Y 4 ξ b).val (Sum.elim m u) := by
  have e0 : b / h.S.HA * h.S.HA + b % h.S.HA = b := Nat.div_add_mod' b h.S.HA
  have hlT := pub_lT A
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have h16 : h.S.cf.lt ≤ 16 := by
    rw [(L5.shaped_of_hid A.shape).cfg]
    exact lt_le_16 hS0
  have s1 : (h.x.rg2 h.S).size = h.S.cf.lgk := by
    show (h.x.scH.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s3 : (h.x.rk h.S).size = 4 := by
    show (h.x.scH.r.extract (h.S.cf.lt + h.S.cf.lgk) (h.S.cf.lt + h.S.cf.lgk + 4)).size = _
    rw [size_cut _ (by omega)]
    omega
  have ha := Nat.mod_lt b (heads_pos hb)
  unfold bitsF
  rw [foldl_pos ρ W _ (fun k => (eqTab (h.x.rk h.S)).getD k zeroE), Aff.value_ofConst, ρ.zero, zero_add,
    list_sum_range, ← hlT]
  unfold Cb.Pv.Att.End.rA21
  rw [val_aSum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < h.S.cf.lt := by rw [← hlT]; exact mem_range.mp hk
  rw [val_aSmul]
  have a3 := readIndexBitF_row m A L .hR2 rfl (Nat.le_of_eq s1.symm) ha (k := k)
    (by rw [e0]; exact hg k hk')
  rw [e0, Tb.hR2] at a3
  have w1 : ρ.val ((eqTab (h.x.rk h.S)).getD k zeroE) =
      Blocks.eqN 4 0 (sh ξ ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg)) k := by
    rw [eqTab_value ρ _ k (by rw [s3]; omega), s3]
    refine eqN_agree (fun j hj => ?_) k
    show pt ρ (h.x.scH.r.extract (h.S.cf.lt + h.S.cf.lgk) (h.S.cf.lt + h.S.cf.lgk + 4))
      (0 + j) = ξ ((L5.dimOf h.S).lT + h.S.cf.lgk + (0 + j))
    rw [hlT, Nat.zero_add, hξ _ (by omega)]
    exact pt_extract ρ _ (by omega) (by omega)
  have w2 : (rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hR2 (pt ρ (h.x.rg2 h.S)) 1
      fun _ g => .ib k b g 0).val (Sum.elim m u) =
      (rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hR2 (sh ξ (L5.dimOf h.S).lT) 1
        fun _ g => .ib k b g 0).val (Sum.elim m u) := by
    refine rdRow_congr _ _ _ _ (fun j hj => ?_) _ _
    have hj' : j < h.S.cf.lgk := hj
    show pt ρ (h.x.scH.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
      ξ ((L5.dimOf h.S).lT + j)
    rw [hlT, hξ _ (by omega)]
    exact pt_extract ρ _ (by omega) (by omega)
  rw [w1, a3, w2]

/-- The query of claim 7. ξ: the point of the score at the index. -/
theorem queryF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {ξ : ℕ → Kf} {b : ℕ}
    (hnl : h.S.atQ.nl = 2)
    (hr : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh, ξ j = pt ρ h.x.scF.r j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qF, (Raw.qry l b g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hf : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atQ (g * h.S.HA + b % h.S.HA) h.S.dh =
      .ok ((g * h.S.HA + b % h.S.HA) * h.S.dh)) :
    (Fo.readHeadT h K3 h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S) (b / h.S.HA) (b % h.S.HA)).value ρ W =
      (rA16 (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y ξ b).val (Sum.elim m u) := by
  have hlT := pub_lT A
  have s1 : (h.x.rg h.S).size = h.S.cf.lgk := by
    show (h.x.scF.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.rc h.S).size = h.S.cf.ldh := by
    show (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size).size = _
    rw [size_cut _ (Nat.le_refl _)]
    omega
  rw [← Tb.qF]
  unfold Fo.readHeadT
  rw [headF_long m A L .qF (fun g => g * h.S.HA + b % h.S.HA) (Nat.le_of_eq s1.symm) s2
    (fun l g => .qry l b g 0 0) (by rw [hnl]; exact hg)
    (fun g ch l _ => by
      show placeTen h.S h.S.atQ l (b / h.S.HA) (g * h.S.HA + b % h.S.HA) (0 + ch * 2 ^ h.S.ls) = _
      unfold placeTen
      rw [blk_div]) hf, hnl]
  refine rdLong_congr _ _ _ _ _ (fun j hj => ?_) (fun j hj => ?_) _ _
  · have hj' : j < h.S.cf.lgk := hj
    show pt ρ (h.x.scF.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j = ξ ((L5.dimOf h.S).lT + j)
    rw [hlT, hξ _ (by omega)]
    exact pt_extract ρ _ (by omega) (by omega)
  · have hj' : j < h.S.cf.ldh - h.S.ls := hj
    show pt ρ (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size) j =
      ξ ((L5.dimOf h.S).lT + h.S.cf.lgk + j)
    rw [hlT, hξ _ (by omega)]
    exact pt_extract ρ _ (Nat.le_refl _) (by omega)

/-- The key of claim 7. ξ: the point of the key at the index. -/
theorem keyF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {p : Pub Kf} {ξ : ℕ → Kf}
    {lam : ℕ} (hnl : h.S.atK.nl = 2)
    (hrF : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    (hξ : ∀ j < 2 * h.S.cf.lt + h.S.cf.lgk, ξ j = pt ρ h.x.scd.r j)
    (hfn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = p.fn j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qKx, (Raw.key l lam g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hf : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atK g h.S.dh = .ok (g * h.S.dh)) :
    (Fo.readGroupT h K3 h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) lam).value ρ W =
      (rKC (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y p ξ lam).val (Sum.elim m u) := by
  have hlT := pub_lT A
  have s1 : (h.x.pg h.S).size = h.S.cf.lgk := by
    show (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.rc h.S).size = h.S.cf.ldh := by
    show (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size).size = _
    rw [size_cut _ (Nat.le_refl _)]
    omega
  rw [← Tb.qKx]
  unfold Fo.readGroupT
  rw [headF_long m A L .qKx (fun g => g) (Nat.le_of_eq s1.symm) s2
    (fun l g => .key l lam g 0 0) (by rw [hnl]; exact hg)
    (fun g ch l _ => by
      show placeTen h.S h.S.atK l lam g (0 + ch * 2 ^ h.S.ls) = _
      unfold placeTen
      rw [blk_div]) hf, hnl]
  refine rdLong_congr _ _ _ _ _ (fun j hj => ?_) (fun j hj => ?_) _ _
  · have hj' : j < h.S.cf.lgk := hj
    show pt ρ (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j = ξ ((L5.dimOf h.S).lT + j)
    rw [hlT, hξ _ (by omega)]
    exact pt_extract ρ _ (by omega) (by omega)
  · have hj' : j < h.S.cf.ldh - h.S.ls := hj
    exact hfn j (by omega)

/-- The value of claim 6, on the diagonal tiles. ξ: the point of the value product there. -/
theorem valueF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {Cc : Calls} {p : Pub Kf}
    {ξ : ℕ → Kf} {b lam : ℕ} (hlam : (L5.dimOf h.S).lamOf b = lam) (hnl : h.S.atV.nl = 2)
    (hr : h.S.cf.lgk ≤ h.d.vpd.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ξ j = pt ρ h.d.vpd.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc p.z j)
    (hgam : ρ.val h.d.gam = p.th)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qVD, (Raw.val l lam g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hf : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atV g h.S.dh = .ok (g * h.S.dh)) :
    (Aff.ofConst h.d.gam + Fo.readGroupT h K3 h.t.qVD h.S.atV h.d.vpd.r h.d.zcW lam).value ρ W =
      (rB12 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.ls Y p ξ b).val (Sum.elim m u) := by
  rw [← Tb.qVD]
  unfold Cb.Pv.Att.End.rB12 Fo.readGroupT
  rw [Aff.value_add, Aff.value_ofConst, hgam, val_aAdd, val_aConst, hlam,
    headF_long m A L .qVD (fun g => g) hr hzc
    (fun l g => .val l lam g 0 0) (by rw [hnl]; exact hg)
    (fun g ch l _ => by
      show placeTen h.S h.S.atV l lam g (0 + ch * 2 ^ h.S.ls) = _
      unfold placeTen
      rw [blk_div]) hf, hnl]
  congr 1
  refine rdLong_congr _ _ _ _ _ (fun j hj => (hξ j hj).symm) (fun j hj => ?_) _ _
  have hj' : j < h.S.cf.ldh - h.S.ls := hj
  exact hyn j (by omega)

/-- The softmax weight of claim 6, on the diagonal tiles. ξ: the point of the value product there. -/
theorem weightF_port (hN : Numerals ρ)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {Cc : Calls} {p : Pub Kf}
    {ξ : ℕ → Kf} {lam a : ℕ} (ha : a < h.S.HA) (hnD : (L5.dimOf h.S).lD = h.S.nD)
    (hz : h.t.ptD.size = h.S.nD)
    (hpt : ∀ j < h.S.nD - h.S.cf.lmS, pt ρ h.t.ptD j = ptOn (L5.dimOf h.S) Cc p ξ j)
    (hg : ∀ jj < 5, ∀ hi < 2 ^ (h.S.nD - h.S.cf.lmS),
      Y.good (.tVD, (Raw.c .D jj (lam * h.S.HA + a) 0).addX (hi * 2 ^ h.S.cf.lmS))) :
    (Fo.planeF h K3 h.t.tVD 3 lam a h.t.ptD true + Aff.ofConst (ofNat 128) +
      Aff.scale (Fo.planeF h K3 h.t.tVD 4 lam a h.t.ptD true) (ofNat 256)).value ρ W =
      (rA12 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.cf.lmS Y p ξ (lam * h.S.HA + a)).val
        (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  rw [← Tb.tVD]
  have pl : ∀ x hi, placeAtt h.S .tVD
      ((Raw.c .D x (lam * h.S.HA + a) 0).addX (hi * 2 ^ h.S.cf.lmS)) =
      Rows.planeFirst h.S x lam a true >>> h.S.cf.lmS + hi := by
    intro x hi
    show Rows.planeFirst h.S x ((lam * h.S.HA + a) / h.S.HA) ((lam * h.S.HA + a) % h.S.HA) true >>>
      h.S.cf.lmS + (0 + hi * 2 ^ h.S.cf.lmS) / 2 ^ h.S.cf.lmS = _
    rw [hb.1, hb.2, blk_div]
  have e3 := planeF_col (ρ := ρ) m L .tVD (x := 3) (lam := lam) (a := a) (z := h.t.ptD) (isD := true)
    (nb := h.S.nD) (if_pos rfl) hz (.c .D 3 (lam * h.S.HA + a) 0) (hg 3 (by norm_num)) (pl 3)
  have e4 := planeF_col (ρ := ρ) m L .tVD (x := 4) (lam := lam) (a := a) (z := h.t.ptD) (isD := true)
    (nb := h.S.nD) (if_pos rfl) hz (.c .D 4 (lam * h.S.HA + a) 0) (hg 4 (by norm_num)) (pl 4)
  unfold Cb.Pv.Att.End.rA12
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale, hN.ofNat, hN.ofNat, e3, e4,
    val_aAdd, val_aAdd, val_aConst, val_aSmul, hnD,
    rdCol_congr _ _ _ _ _ hpt, rdCol_congr _ _ _ _ _ hpt]
  push_cast
  ring

end

end K5Law

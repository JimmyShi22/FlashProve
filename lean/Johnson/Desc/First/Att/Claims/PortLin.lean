-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortLin.lean: kind K5: the written forms of the claims on the named
scalars are the library-side forms (Cb/Pv/Att/End/Lin.lean: overPairs of rdRow, rdLong or rdCol: the
cases of rvF), at any values of the late entries. Twins of less_port, row_port, zc_port, ib_port,
ms_port, high_port and cell_port (Johnson/Road/Rows/AttPortLin.lean), which speak of a run of a
routine in a context ("if the routine returns"). No table is taken to be true. The proofs follow
those proofs line for line, with lessF_value (Johnson/Desc/First/Att/Claims/Worth.lean) where
lessPieces_value stood and the twins of Johnson/Desc/First/Att/Claims/PortRow.lean,
Johnson/Desc/First/Att/Claims/PortLong.lean and Johnson/Desc/First/Att/Claims/PortFirst.lean where
the ports stood.

Main names: `lessF_port`, `rowF_port`, `zcF_port`, `ibF_port`, `msF_port`, `highF_port`,
`cellF_port`: (Fo.lessF (Aff.slot s) pw fun w => ‹the reader's written form›).value ρ W = W.slot s −
(overPairs …).val (Sum.elim m u).
rowF_port is the twin of row_port; it is another thing than the library's rowF (the claim on a
sumcheck's row).
Premise beyond those of Johnson/Road/Rows: the heads' features are lawful (highF_port).
Used: as Johnson/Desc/First/Att/Claims/PortFirst.lean, and PiecesAll, sum_pieces, piece_at,
pair_parts; the library's Fam, wp, overPairs, val_overPairs.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttPortLin
import Johnson.Desc.First.Att.Claims.PortFirst

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Reg Calls Fam wp)
open Cb.Pv.Att.End (LateLay AttTab rdRow rdLong rdCol rdRow_congr rdLong_congr rdCol_congr
  overPairs val_overPairs)

variable {Kf : Type} [Field Kf]

section
variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → Kf} (m : J₁ → Kf)

omit [DecidableEq J₁] [DecidableEq J₂] in
/-- A written form lessF on a slot. r b: the library-side form of pair b. -/
theorem lessF_port (s : ℕ) {pw : Array PW} (P : PiecesAll h.S pw) (f : PW → Aff)
    (Cc : Calls) (z : ℕ → Kf) (fam : Fam) (r : ℕ → TWhole.Aff Kf (J₁ ⊕ J₂)) (x : J₁ ⊕ J₂ → Kf)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hf : ∀ b < h.S.NP, (f (pw.getD b default)).value ρ W = (r b).val x) :
    (Fo.lessF (Aff.slot s) pw f).value ρ W =
      W.slot s - (overPairs (L5.dimOf h.S) Cc z fam r).val x := by
  rw [lessF_value, Aff.value_slot, sum_pieces P, val_overPairs]
  congr 1
  refine sum_congr rfl fun b hb => ?_
  rw [hw b (mem_range.mp hb), hf b (mem_range.mp hb)]

/-- A scalar whose pieces are read by a form in limbs on ah. T: the table; vg: the library's point on the heads. -/
theorem rowF_port (s : ℕ) {pw : Array PW}
    (P : PiecesAll h.S pw) (Cc : Calls) (z : ℕ → Kf) (fam : Fam) (T : AttTab) {zg : Array E}
    {vg : ℕ → Kf} (hvg : ∀ j < h.S.cf.lgk, pt ρ zg j = vg j) (n : ℕ) (base : ℕ → ℕ → ℕ → Raw)
    (f : PW → Aff)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hf : ∀ lam a, a < h.S.HA → lam * h.S.HA + a < h.S.NP → ∀ w : PW, w.lam = lam → w.a = a →
      (f w).value ρ W =
        (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) n (base (lam * h.S.HA + a))).val
          (Sum.elim m u)) :
    (Fo.lessF (Aff.slot s) pw f).value ρ W = W.slot s - (overPairs (L5.dimOf h.S) Cc z fam fun b =>
      rdRow (J₁ := J₁) (L5.dimOf h.S) Y T vg n (base b)).val (Sum.elim m u) := by
  refine lessF_port s P f Cc z fam _ _ hw (fun b hb => ?_)
  obtain ⟨-, p2, p3⟩ := piece_at P hb
  rw [hf _ _ p2 (by rw [p3]; exact hb) _ rfl rfl, p3]
  exact rdRow_congr _ _ _ _ hvg _ _

/-- ZC of claim 5: the denominators. -/
theorem zcF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .hW = h.t.hW)
    (P : PiecesAll h.S h.d.pwW) (Cc : Calls) (z : ℕ → Kf) {vg : ℕ → Kf}
    (hz : h.S.cf.lgk ≤ h.d.zgW.size) (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = vg j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp (L5.dimOf h.S) Cc z .w3 b)
    (hg : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (.hW, .den l b g 0)) :
    (Fo.lessF (Aff.slot h.d.sZC) h.d.pwW fun w =>
      Fo.readDenominatorF h K3 h.t.hW h.d.zgW w.lam w.a).value ρ W =
      W.slot h.d.sZC - (overPairs (L5.dimOf h.S) Cc z .w3 fun b =>
        rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hW vg 4 fun k g => .den k b g 0).val
          (Sum.elim m u) := by
  refine rowF_port m _ P Cc z .w3 .hW hvg 4 (fun b k g => .den k b g 0) _ hw
    (fun lam a ha hb w h1 h2 => ?_)
  rw [h1, h2, ← hT]
  exact readDenominatorF_row m A L .hW rfl hz ha (hg _ hb)

/-- IB_k of claim 5: a bit of the index. -/
theorem ibF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .hX = h.t.hX)
    (P : PiecesAll h.S h.d.pwX) (Cc : Calls) (z : ℕ → Kf) {vg : ℕ → Kf} (k : ℕ)
    (hz : h.S.cf.lgk ≤ h.d.zgX.size) (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = vg j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp (L5.dimOf h.S) Cc z .x3 b)
    (hg : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, Y.good (.hX, .ib k b g 0)) :
    (Fo.lessF (Aff.slot (h.d.sIB + k)) h.d.pwX fun w =>
      Fo.readIndexBitF h K3 h.t.hX h.d.zgX w.lam w.a k).value ρ W =
      W.slot (h.d.sIB + k) - (overPairs (L5.dimOf h.S) Cc z .x3 fun b =>
        rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hX vg 1 fun _ g => .ib k b g 0).val
          (Sum.elim m u) := by
  refine rowF_port m _ P Cc z .x3 .hX hvg 1 (fun b _ g => .ib k b g 0) _ hw
    (fun lam a ha hb w h1 h2 => ?_)
  rw [h1, h2, ← hT]
  exact readIndexBitF_row m A L .hX rfl hz ha (hg _ hb)

/-- The row maxima of a unit of the scores. T: the unit's table on the maxima; t: where it begins. -/
theorem msF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (T : AttTab) {t : ℕ} (hT : tabOf T = t)
    (hpl : placeAtt h.S T = placeRow h.S) (s : ℕ) {pw : Array PW} (P : PiecesAll h.S pw)
    (Cc : Calls) (z : ℕ → Kf) (fam : Fam) {zg : Array E} {vg : ℕ → Kf}
    (hz : h.S.cf.lgk ≤ zg.size) (hvg : ∀ j < h.S.cf.lgk, pt ρ zg j = vg j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hg : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (T, .mx l b g 0)) :
    (Fo.lessF (Aff.slot s) pw fun w => Fo.readMaximumF h K3 t zg w.lam w.a).value ρ W =
      W.slot s - (overPairs (L5.dimOf h.S) Cc z fam fun b =>
        rdRow (J₁ := J₁) (L5.dimOf h.S) Y T vg 4 fun k g => .mx k b g 0).val (Sum.elim m u) := by
  refine rowF_port m _ P Cc z fam T hvg 4 (fun b k g => .mx k b g 0) _ hw
    (fun lam a ha hb w h1 h2 => ?_)
  rw [h1, h2, ← hT]
  exact readMaximumF_row m A L T hpl hz ha (hg _ hb)

/-- A scalar whose pieces are read by readHead in the table tO. X: where the tensor lies; mk b g n: the names of its cells. It serves RH and RH2 (with Attention.atRh and the names qh), RHP and RHP2 (with Attention.atRhp and the names qh'). -/
theorem highF_port (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .tO = h.t.tO) {X : TenAt}
    (hnl : X.nl = 1) (mk : ℕ → ℕ → ℕ → Raw)
    (hadd : ∀ b g c, (mk b g 0).addN c = mk b g (0 + c))
    (hpl : ∀ b g n, placeLong h.S (mk b g n) =
      placeTen h.S X 0 (b / h.S.HA) (g * h.S.HA + b % h.S.HA) n)
    (s : ℕ) {pw : Array PW} (P : PiecesAll h.S pw) (Cc : Calls) (z : ℕ → Kf) (fam : Fam)
    {zg zc : Array E} {vg vn : ℕ → Kf} (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zg j = vg j) (hvn : ∀ j < h.S.cf.ldh, pt ρ zc j = vn j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hg : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls),
      Y.good (.tO, (mk b g 0).addN (ch * 2 ^ h.S.ls)))
    (hfe : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk,
      headFeat X (g * h.S.HA + (pw.getD b default).a) h.S.dh =
        .ok ((g * h.S.HA + (pw.getD b default).a) * h.S.dh)) :
    (Fo.lessF (Aff.slot s) pw fun w => Fo.readHeadT h K3 h.t.tO X zg zc w.lam w.a).value ρ W =
      W.slot s - (overPairs (L5.dimOf h.S) Cc z fam fun b =>
        rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y .tO vg vn 1 fun _ g => mk b g 0).val
          (Sum.elim m u) := by
  refine lessF_port s P _ Cc z fam _ _ hw (fun b hb => ?_)
  obtain ⟨-, p2, p3⟩ := piece_at P hb
  have hb2 := pair_parts (lam := (pw.getD b default).lam) p2
  rw [p3] at hb2
  rw [headF_port m A L .tO hT hnl (fun _ g n => mk b g n) (fun _ g c => hadd b g c)
    (fun l hl g n => by
      have hl0 : l = 0 := by omega
      show placeLong h.S (mk b g n) = _
      rw [hpl, hl0, hb2.1, hb2.2]) hzg hzc (fun g hg' ch hch _ _ => hg b hb g hg' ch hch) (hfe b hb)]
  exact rdLong_congr _ _ _ _ _ hvg (fun j hj => hvn j (by
    have hj' : j < h.S.cf.ldh - h.S.ls := hj
    omega)) _ _

/-- A plane of a plane claim. isD, reg: the region; nb: the number of bits of one of its places; x: the plane's number. -/
theorem cellF_port (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hT : tabOf .tA = h.t.tA) (s x : ℕ) {pw : Array PW} (P : PiecesAll h.S pw) (Cc : Calls)
    (z : ℕ → Kf) (fam : Fam) {zz : Array E} {isD : Bool} {nb : ℕ} (reg : Reg)
    (hreg : reg = if isD then Reg.D else Reg.M)
    (hnb : (if isD then h.S.nD else h.S.nM) = nb) (hz : zz.size = nb) {vz : ℕ → Kf}
    (hvz : ∀ j < nb - h.S.cf.lmS, pt ρ zz j = vz j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hg : ∀ b < h.S.NP, ∀ hi < 2 ^ (nb - h.S.cf.lmS),
      Y.good (.tA, (Raw.c reg x b 0).addX (hi * 2 ^ h.S.cf.lmS))) :
    (Fo.lessF (Aff.slot s) pw fun w => Fo.planeF h K3 h.t.tA x w.lam w.a zz isD).value ρ W =
      W.slot s - (overPairs (L5.dimOf h.S) Cc z fam fun b =>
        rdCol (J₁ := J₁) h.S.cf.lmS Y .tA nb vz (.c reg x b 0)).val (Sum.elim m u) := by
  refine lessF_port s P _ Cc z fam _ _ hw (fun b hb => ?_)
  obtain ⟨-, p2, p3⟩ := piece_at P hb
  have hb2 := pair_parts (lam := (pw.getD b default).lam) p2
  rw [p3] at hb2
  rw [← hT]
  rw [planeF_col (ρ := ρ) m L .tA hnb hz (.c reg x b 0) (hg b hb)
    (fun hi => by
      rw [hreg]
      cases isD with
      | false =>
        show Rows.planeFirst h.S x (b / h.S.HA) (b % h.S.HA) false >>> h.S.cf.lmS +
          (0 + hi * 2 ^ h.S.cf.lmS) / 2 ^ h.S.cf.lmS = _
        rw [hb2.1, hb2.2, blk_div]
      | true =>
        show Rows.planeFirst h.S x (b / h.S.HA) (b % h.S.HA) true >>> h.S.cf.lmS +
          (0 + hi * 2 ^ h.S.cf.lmS) / 2 ^ h.S.cf.lmS = _
        rw [hb2.1, hb2.2, blk_div])]
  exact rdCol_congr _ _ _ _ _ hvz _

end

end K5Law

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortLin.lean: the forms of the verifier's claims on the named scalars of an
attention sub-proof are the library-side forms, at any values of the late entries.

Most scalars that the prover of an attention sub-proof sends beside its sumchecks are tied by one
claim each: the scalar's hidden value, less the sum over the pieces of the piece's weight times a
form that reads a table, is 0 (lessPieces in OnBytes/Model/AttentionClaimsA.lean).
Cb/Pv/Att/End/Lin.lean writes the sums in the library's names (rvF). This file holds the two against
each other. No table is taken to be true.

Main theorems.
 - less_port: a form lessPieces on a slot is worth the slot's hidden value less what overPairs is
   worth, if each piece's form is worth what the pair's library-side form is worth.
 - zc_port, ib_port, high_port, ms_port, cell_port: the forms of claim 5, of the row maxima of a
   unit and of the planes. Their right sides are the cases of rvF, by its definition. high_port
   serves RH, RHP (family w3) and RH2, RHP2 (family f4).

What the theorems take as given: the dictionary LateAt with the places of
Johnson/Road/Rows/AttPortLate.lean; that the names read are names of late entries; that the list of
pieces has a piece for each pair, with the library's weights; that the verifier's points are the
library's, coordinate by coordinate; that the routine has returned.

What is not claimed: as in Johnson/Road/Rows/AttPortLate.lean. With this file the places of the last
six tables are shown to be the numbers at which the verifier's functions read: tA, tMm, tMd, hW, hX,
tO.


-/
import Johnson.Road.Rows.AttPortFirst
import Johnson.Road.Rows.AttLin
import Cb.Pv.Att.End.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork SubM TenAt)
open OnBytes.Attention (Heard PW ScoreTables lessPieces)
open OnBytes.Road.Hd (Ok)
open Inst.Model.AttSeg (Raw Reg Calls Fam wp)
open Cb.Pv.Att.End (LateLay AttTab rdRow rdLong rdCol rdRow_congr rdLong_congr rdCol_congr
  overPairs val_overPairs)

variable {K : Type} [Field K]

section
variable {ρ : Reading K} {W : World K} {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → K} (m : J₁ → K)
  {F : Fork} {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}

omit [DecidableEq J₁] [DecidableEq J₂] in
/-- A form lessPieces on a slot. r b: the library-side form of pair b. -/
theorem less_port (s : ℕ) {pw : Array PW} (P : PiecesAll h.S pw) (f : PW → SubM Aff)
    (Cc : Calls) (z : ℕ → K) (fam : Fam) (r : ℕ → TWhole.Aff K (J₁ ⊕ J₂)) (x : J₁ ⊕ J₂ → K)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hf : ∀ b < h.S.NP, ∀ y G D, Ok (f (pw.getD b default)) F C y G D →
      G = F ∧ D = C ∧ y.value ρ W = (r b).val x)
    (hq : Ok (lessPieces (Aff.slot s) pw f) F C q G D) :
    q.value ρ W = W.slot s - (overPairs (L5.dimOf h.S) Cc z fam r).val x := by
  obtain ⟨-, -, e⟩ := lessPieces_value ρ W (Aff.slot s) pw f
    (fun w => (r (w.lam * h.S.HA + w.a)).val x)
    (by
      intro w hw' y G1 D1 hy
      rw [Array.mem_toList_iff] at hw'
      obtain ⟨b, hb, rfl⟩ := Array.getElem_of_mem hw'
      have hb' : b < h.S.NP := by rw [← P.1]; exact hb
      have e1 : pw.getD b default = pw[b] := by
        simp [Array.getD, hb]
      have e2 := (piece_at P hb').2.2
      rw [e1] at e2
      beta_reduce
      rw [e2]
      rw [← e1] at hy
      exact hf b hb' y G1 D1 hy) hq
  rw [e, Aff.value_slot, sum_pieces P, val_overPairs, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun b hb => ?_
  rw [hw b (mem_range.mp hb), (piece_at P (mem_range.mp hb)).2.2]

/-! ## The scalars on single features -/

/-- A scalar whose pieces are read by a form in limbs on ah. rd': the verifier's function; T: the
table; vg: the library's point on the heads. -/
theorem row_port (s : ℕ) {pw : Array PW}
    (P : PiecesAll h.S pw) (Cc : Calls) (z : ℕ → K) (fam : Fam) (T : AttTab) {zg : Array E}
    {vg : ℕ → K} (hvg : ∀ j < h.S.cf.lgk, pt ρ zg j = vg j) (n : ℕ) (base : ℕ → ℕ → ℕ → Raw)
    (f : PW → SubM Aff)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hf : ∀ lam a, a < h.S.HA → lam * h.S.HA + a < h.S.NP → ∀ w : PW, w.lam = lam → w.a = a →
      ∀ y G D, Ok (f w) F C y G D → G = F ∧ D = C ∧ y.value ρ W =
        (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) n (base (lam * h.S.HA + a))).val
          (Sum.elim m u))
    (hq : Ok (lessPieces (Aff.slot s) pw f) F C q G D) :
    q.value ρ W = W.slot s - (overPairs (L5.dimOf h.S) Cc z fam fun b =>
      rdRow (J₁ := J₁) (L5.dimOf h.S) Y T vg n (base b)).val (Sum.elim m u) := by
  refine less_port s P f Cc z fam _ _ hw (fun b hb y G1 D1 hy => ?_) hq
  obtain ⟨-, p2, p3⟩ := piece_at P hb
  obtain ⟨e1, e2, e3⟩ := hf _ _ p2 (by rw [p3]; exact hb) _ rfl rfl y G1 D1 hy
  refine ⟨e1, e2, ?_⟩
  rw [e3, p3]
  exact rdRow_congr _ _ _ _ hvg _ _

/-- ZC of claim 5: the denominators. -/
theorem zc_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .hW = h.t.hW)
    (P : PiecesAll h.S h.d.pwW) (Cc : Calls) (z : ℕ → K) {vg : ℕ → K}
    (hz : h.S.cf.lgk ≤ h.d.zgW.size) (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = vg j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp (L5.dimOf h.S) Cc z .w3 b)
    (hg : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (.hW, .den l b g 0))
    (hq : Ok (lessPieces (Aff.slot h.d.sZC) h.d.pwW fun w =>
      Attention.readDenominator h h.t.hW h.d.zgW w.lam w.a) F C q G D) :
    q.value ρ W = W.slot h.d.sZC - (overPairs (L5.dimOf h.S) Cc z .w3 fun b =>
      rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hW vg 4 fun k g => .den k b g 0).val
        (Sum.elim m u) := by
  refine row_port m _ P Cc z .w3 .hW hvg 4 (fun b k g => .den k b g 0) _ hw
    (fun lam a ha hb w h1 h2 y G1 D1 hy => ?_) hq
  rw [h1, h2] at hy
  obtain ⟨e1, e2, -⟩ := limbs_ent W A hc hz (fun g => g * h.S.HA + a) hy
  rw [← hT] at hy
  exact ⟨e1, e2, readDenominator_row m A hc L .hW rfl hz ha (hg _ hb) hy⟩

/-- IB_k of claim 5: a bit of the index. -/
theorem ib_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .hX = h.t.hX)
    (P : PiecesAll h.S h.d.pwX) (Cc : Calls) (z : ℕ → K) {vg : ℕ → K} (k : ℕ)
    (hz : h.S.cf.lgk ≤ h.d.zgX.size) (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = vg j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp (L5.dimOf h.S) Cc z .x3 b)
    (hg : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, Y.good (.hX, .ib k b g 0))
    (hq : Ok (lessPieces (Aff.slot (h.d.sIB + k)) h.d.pwX fun w =>
      Attention.readIndexBit h h.t.hX h.d.zgX w.lam w.a k) F C q G D) :
    q.value ρ W = W.slot (h.d.sIB + k) - (overPairs (L5.dimOf h.S) Cc z .x3 fun b =>
      rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hX vg 1 fun _ g => .ib k b g 0).val
        (Sum.elim m u) := by
  refine row_port m _ P Cc z .x3 .hX hvg 1 (fun b _ g => .ib k b g 0) _ hw
    (fun lam a ha hb w h1 h2 y G1 D1 hy => ?_) hq
  rw [h1, h2] at hy
  obtain ⟨e1, e2, -⟩ := limbs_ent W A hc hz (fun g => k * h.S.cf.H + g * h.S.HA + a) hy
  rw [← hT] at hy
  exact ⟨e1, e2, readIndexBit_row m A hc L .hX rfl hz ha (hg _ hb) hy⟩

/-- The row maxima of a unit of the scores. T: the unit's table on the maxima; t: where it begins.
-/
theorem ms_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (T : AttTab) {t : ℕ} (hT : tabOf T = t)
    (hpl : placeAtt h.S T = placeRow h.S) (s : ℕ) {pw : Array PW} (P : PiecesAll h.S pw)
    (Cc : Calls) (z : ℕ → K) (fam : Fam) {zg : Array E} {vg : ℕ → K}
    (hz : h.S.cf.lgk ≤ zg.size) (hvg : ∀ j < h.S.cf.lgk, pt ρ zg j = vg j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hg : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (T, .mx l b g 0))
    (hq : Ok (lessPieces (Aff.slot s) pw fun w => Attention.readMaximum h t zg w.lam w.a)
      F C q G D) :
    q.value ρ W = W.slot s - (overPairs (L5.dimOf h.S) Cc z fam fun b =>
      rdRow (J₁ := J₁) (L5.dimOf h.S) Y T vg 4 fun k g => .mx k b g 0).val (Sum.elim m u) := by
  refine row_port m _ P Cc z fam T hvg 4 (fun b k g => .mx k b g 0) _ hw
    (fun lam a ha hb w h1 h2 y G1 D1 hy => ?_) hq
  rw [h1, h2] at hy
  obtain ⟨e1, e2, -⟩ := limbs_ent W A hc hz (fun g => g * h.S.HA + a) hy
  rw [← hT] at hy
  exact ⟨e1, e2, readMaximum_row m A hc L T hpl hz ha (hg _ hb) hy⟩

/-! ## The remainders' high parts -/

/-- A scalar whose pieces are read by readHead in the table tO. X: where the tensor lies; mk b g n:
the names of its cells. It serves RH and RH2 (with Attention.atRh and the names qh), RHP and RHP2
(with Attention.atRhp and the names qh'). -/
theorem high_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (hT : tabOf .tO = h.t.tO) {X : TenAt}
    (hnl : X.nl = 1) (mk : ℕ → ℕ → ℕ → Raw)
    (hadd : ∀ b g c, (mk b g 0).addN c = mk b g (0 + c))
    (hpl : ∀ b g n, placeLong h.S (mk b g n) =
      placeTen h.S X 0 (b / h.S.HA) (g * h.S.HA + b % h.S.HA) n)
    (s : ℕ) {pw : Array PW} (P : PiecesAll h.S pw) (Cc : Calls) (z : ℕ → K) (fam : Fam)
    {zg zc : Array E} {vg vn : ℕ → K} (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zg j = vg j) (hvn : ∀ j < h.S.cf.ldh, pt ρ zc j = vn j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hg : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls),
      Y.good (.tO, (mk b g 0).addN (ch * 2 ^ h.S.ls)))
    (hq : Ok (lessPieces (Aff.slot s) pw fun w =>
      Attention.readHead h h.t.tO X zg zc w.lam w.a) F C q G D) :
    q.value ρ W = W.slot s - (overPairs (L5.dimOf h.S) Cc z fam fun b =>
      rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y .tO vg vn 1 fun _ g => mk b g 0).val
        (Sum.elim m u) := by
  refine less_port s P _ Cc z fam _ _ hw (fun b hb y G1 D1 hy => ?_) hq
  obtain ⟨-, p2, p3⟩ := piece_at P hb
  have hb2 := pair_parts (lam := (pw.getD b default).lam) p2
  rw [p3] at hb2
  obtain ⟨e1, e2, -⟩ := head_ent W A hc
    (fun g => g * h.S.HA + (pw.getD b default).a) hzg hzc hy
  refine ⟨e1, e2, ?_⟩
  rw [head_port m A hc L .tO hT hnl (fun _ g n => mk b g n) (fun _ g c => hadd b g c)
    (fun l hl g n => by
      have hl0 : l = 0 := by omega
      show placeLong h.S (mk b g n) = _
      rw [hpl, hl0, hb2.1, hb2.2]) hzg hzc (fun g hg' ch hch _ _ => hg b hb g hg' ch hch) hy]
  exact rdLong_congr _ _ _ _ _ hvg (fun j hj => hvn j (by
    have hj' : j < h.S.cf.ldh - h.S.ls := hj
    omega)) _ _

/-! ## The planes -/

/-- A plane of a plane claim. isD, reg: the region; nb: the number of bits of one of its places; x:
the plane's number. -/
theorem cell_port (hc : Cols F h K3) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hT : tabOf .tA = h.t.tA) (s x : ℕ) {pw : Array PW} (P : PiecesAll h.S pw) (Cc : Calls)
    (z : ℕ → K) (fam : Fam) {zz : Array E} {isD : Bool} {nb : ℕ} (reg : Reg)
    (hreg : reg = if isD then Reg.D else Reg.M)
    (hnb : (if isD then h.S.nD else h.S.nM) = nb) (hz : zz.size = nb) {vz : ℕ → K}
    (hvz : ∀ j < nb - h.S.cf.lmS, pt ρ zz j = vz j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hg : ∀ b < h.S.NP, ∀ hi < 2 ^ (nb - h.S.cf.lmS),
      Y.good (.tA, (Raw.c reg x b 0).addX (hi * 2 ^ h.S.cf.lmS)))
    (hq : Ok (lessPieces (Aff.slot s) pw fun w =>
      Attention.plane h h.t.tA x w.lam w.a zz isD) F C q G D) :
    q.value ρ W = W.slot s - (overPairs (L5.dimOf h.S) Cc z fam fun b =>
      rdCol (J₁ := J₁) h.S.cf.lmS Y .tA nb vz (.c reg x b 0)).val (Sum.elim m u) := by
  refine less_port s P _ Cc z fam _ _ hw (fun b hb y G1 D1 hy => ?_) hq
  obtain ⟨-, p2, p3⟩ := piece_at P hb
  have hb2 := pair_parts (lam := (pw.getD b default).lam) p2
  rw [p3] at hb2
  obtain ⟨e1, e2, -⟩ := plane_ent (ρ := ρ) W hc hy
  refine ⟨e1, e2, ?_⟩
  rw [← hT] at hy
  rw [plane_col (ρ := ρ) m hc L .tA hnb hz (.c reg x b 0) (hg b hb)
    (fun hi => by
      rw [hreg]
      cases isD with
      | false =>
        show planeFirst h.S x (b / h.S.HA) (b % h.S.HA) false >>> h.S.cf.lmS +
          (0 + hi * 2 ^ h.S.cf.lmS) / 2 ^ h.S.cf.lmS = _
        rw [hb2.1, hb2.2, blk_div]
      | true =>
        show planeFirst h.S x (b / h.S.HA) (b % h.S.HA) true >>> h.S.cf.lmS +
          (0 + hi * 2 ^ h.S.cf.lmS) / 2 ^ h.S.cf.lmS = _
        rw [hb2.1, hb2.2, blk_div]) hy]
  exact rdCol_congr _ _ _ _ _ hvz _

end

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.less_port
#print axioms OnBytes.Road.Rows.zc_port
#print axioms OnBytes.Road.Rows.ib_port
#print axioms OnBytes.Road.Rows.ms_port
#print axioms OnBytes.Road.Rows.high_port
#print axioms OnBytes.Road.Rows.cell_port

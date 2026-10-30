-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttLin.lean: the claims of the attention sub-proof that tie one sent scalar to a
table, said on cells.

Most scalars that the prover of an attention sub-proof sends are tied by one claim each: the scalar
minus the sum, over the pieces of a segment, of the piece's weight times a form on a table is 0
(OnBytes/Model/AttentionClaimsA.lean: lessPieces, linPlanes, unitKFD;
OnBytes/Model/AttentionClaimsB.lean: claim5). The library gives each such scalar a rule value on the
cells (rv in Inst/Model/Att/KeyForms.lean). This file shows that in a world in which every table is
true of the matrices, such a claim with the value 0 makes the scalar's hidden value its rule value.

Main theorems.
 - lessPieces_value: what the form lessPieces is worth. sum_pieces: a sum over a list of pieces that
   has a piece for each pair, as a sum over the pairs. less_rule: the two together.
 - rd3_atY: the library's extension atY of an array on (g, i, n) is a read.
 - linZc, linIb: the denominator; a bit of the index.
 - linCellM: a plane below the diagonal.

What a theorem takes as given, beside the setting: that piece b is pair b, that the pieces' weights
and the verifier's points are the library's, that the table lies in the list with its weights, that
the form has been made, and that it has the value 0.

What this file does not claim. The high parts of the two remainders, the row maxima (the scalars ms)
and the planes on the diagonal are not treated here: Johnson/Road/Rows/AttLinMore.lean. Nothing is
said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttEnds14Below
import Johnson.Road.Rows.AttEnds58Proofs
import Cb.Pv.Att.Mean.RowSum
import Johnson.Road.Rows.AttEndsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HFun HTailF2 TenAt tenCell eqTab blockRows)
open OnBytes.Attention (Shape Heard PW lessPieces minusOne lastN)
open OnBytes.Road.Hd (Ok ok_pure ok_bind)
open Inst.Model.AttSeg (Calls Pub rd2 rd3 eqT sh denV ibV rv wp atY conN KSc)

variable {K : Type} [Field K]

/-! ## The form lessPieces -/

/-- The element -1. -/
theorem minusOne_value (ρ : Reading K) : ρ.val minusOne = -1 := by
  unfold Attention.minusOne
  rw [ρ.sub, ρ.zero, ρ.one, zero_sub]

/-- The form lessPieces: the start form less the sum over the pieces of the piece's weight times the
piece's form. -/
theorem lessPieces_value (ρ : Reading K) (W : World K) {F : Fork} {C : Ctx} (start : Aff)
    (pw : Array PW) (f : PW → SubM Aff) (v : PW → K)
    (hf : ∀ w ∈ pw.toList, ∀ x G D, Ok (f w) F C x G D → G = F ∧ D = C ∧ x.value ρ W = v w)
    {q : Aff} {G : Fork} {D : Ctx} (hq : Ok (lessPieces start pw f) F C q G D) :
    G = F ∧ D = C ∧
      q.value ρ W = start.value ρ W + (pw.toList.map fun w => -(ρ.val w.wp * v w)).sum := by
  unfold Attention.lessPieces at hq
  rw [← Array.foldlM_toList] at hq
  obtain ⟨e1, e2, -, e4⟩ := foldlM_value ρ W F C
    (fun s w => f w >>= fun x => pure (Aff.addMul s x (mulE minusOne w.wp)))
    (fun w => -(ρ.val w.wp * v w)) (fun _ => True) pw.toList
    (by
      intro w hw s y G1 D1 hy
      have hy' : Ok (f w >>= fun x => pure (Aff.addMul s x (mulE minusOne w.wp))) F C y G1 D1 :=
        hy
      rw [ok_bind] at hy'
      obtain ⟨x, F1, C1, h1, h2⟩ := hy'
      obtain ⟨a1, a2, a3⟩ := hf w hw x F1 C1 h1
      rw [ok_pure] at h2
      obtain ⟨b1, b2, b3⟩ := h2
      rw [b1, b2, b3]
      refine ⟨a1, a2, trivial, ?_⟩
      rw [Aff.value_addMul, a3, ρ.mul, minusOne_value]
      ring)
    start q G D hq
  exact ⟨e1, e2, e4⟩

/-- The sum of the values of a list, by the places of the list. -/
theorem sum_map_getD {α : Type} (l : List α) (g : α → K) (d : α) :
    (l.map g).sum = ∑ i ∈ range l.length, g (l.getD i d) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, sum_range_succ', ih, add_comm]
    simp

/-- A sum over a list of pieces that has a piece for each pair, as a sum over the pairs. -/
theorem sum_pieces {S : Shape} {pw : Array PW} (P : PiecesAll S pw) (g : PW → K) :
    (pw.toList.map g).sum = ∑ b ∈ range S.NP, g (pw.getD b default) := by
  rw [sum_map_getD _ g default, Array.length_toList, P.1]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- Piece number b of a list that has a piece for each pair. -/
theorem piece_at {S : Shape} {pw : Array PW} (P : PiecesAll S pw) {b : ℕ} (hb : b < S.NP) :
    pw.getD b default ∈ pw.toList ∧ (pw.getD b default).a < S.HA ∧
      (pw.getD b default).lam * S.HA + (pw.getD b default).a = b := by
  obtain ⟨w, hw, h1, h2⟩ := pair_of_piece P hb
  have e : pw.getD b default = w := by
    rw [Array.getD_eq_getD_getElem?, hw]
    rfl
  rw [e]
  refine ⟨?_, h1, h2⟩
  rw [Array.mem_toList_iff]
  exact Array.mem_of_getElem? hw

/-- A claim of the form lessPieces on a slot, with the value 0: the slot's hidden value is the sum
over the pairs of the pair's weight om b times the value V b of the pair's form. -/
theorem less_rule (ρ : Reading K) (W : World K) {S : Shape} {F : Fork} {C : Ctx} (s : ℕ)
    {pw : Array PW} (P : PiecesAll S pw) (f : PW → SubM Aff) (om V : ℕ → K)
    (hw : ∀ b < S.NP, ρ.val (pw.getD b default).wp = om b)
    (hf : ∀ b < S.NP, ∀ x G D, Ok (f (pw.getD b default)) F C x G D →
      G = F ∧ D = C ∧ x.value ρ W = V b)
    {q : Aff} {G : Fork} {D : Ctx} (hq : Ok (lessPieces (Aff.slot s) pw f) F C q G D)
    (h0 : q.value ρ W = 0) : W.slot s = ∑ b ∈ range S.NP, om b * V b := by
  obtain ⟨-, -, e⟩ := lessPieces_value ρ W (Aff.slot s) pw f
    (fun w => V (w.lam * S.HA + w.a))
    (by
      intro w hw' x G1 D1 hx
      rw [Array.mem_toList_iff] at hw'
      obtain ⟨b, hb, rfl⟩ := Array.getElem_of_mem hw'
      have hb' : b < S.NP := by rw [← P.1]; exact hb
      have e1 : pw.getD b default = pw[b] := by
        simp [Array.getD, hb]
      have e2 := (piece_at P hb').2.2
      rw [e1] at e2
      beta_reduce
      rw [e2]
      rw [← e1] at hx
      exact hf b hb' x G1 D1 hx) hq
  rw [h0, Aff.value_slot, sum_pieces P] at e
  have e3 : ∑ b ∈ range S.NP, -(ρ.val (pw.getD b default).wp *
      V ((pw.getD b default).lam * S.HA + (pw.getD b default).a)) =
      -∑ b ∈ range S.NP, om b * V b := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun b hb => ?_
    rw [hw b (mem_range.mp hb), (piece_at P (mem_range.mp hb)).2.2]
  rw [e3] at e
  linear_combination -e

/-! ## The library's extension atY -/

/-- The library's extension atY of an array on (g, i, n) is the read of the array at the lookup's
point. -/
theorem rd3_atY (D : Inst.Model.AttSeg.Dim) (C : Calls) (p : Pub K) (a : ℕ → ℕ → ℕ → K) :
    rd3 D (Inst.Model.AttSeg.yg D C p.z) (eqT D (Inst.Model.AttSeg.yi D C p.z))
      (Inst.Model.AttSeg.yn D C p.z) a = atY D C p a := by
  rw [atY_rd2]
  unfold rd3 rd2 conN
  refine sum_congr rfl fun g _ => sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

section Forms

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} {p : Pub K}

/-- The number of pairs. -/
theorem dim_nb (S : Shape) : (L5.dimOf S).nb = S.NP := rfl

/-! ## The denominator and the bits of the index -/

/-- The scalar ZC is its rule value. -/
theorem linZc (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3)
    (P : PiecesAll h.S h.d.pwW)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp (L5.dimOf h.S) C p.z .w3 b)
    (hzg : h.d.zgW.size = h.S.cf.lgk) (hzi : h.d.ziW.size = h.S.cf.lt)
    (hg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ h.d.ziW j = Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.hW h.S.cf.NAs h.S.T (eqTab h.d.ziW))
    {c : Ctx} {q : Aff} {G : Fork} {c1 : Ctx}
    (hq : Ok (lessPieces (Aff.slot h.d.sZC) h.d.pwW fun w =>
      Attention.readDenominator h h.t.hW h.d.zgW w.lam w.a) F c q G c1)
    (h0 : q.value ρ W = 0) :
    W.slot h.d.sZC = rv (L5.dimOf h.S) C p (cellsK h.S M) .zc := by
  refine less_rule ρ W h.d.sZC P _ _
    (fun b => rd2 (L5.dimOf h.S) (Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z)
      (eqT (L5.dimOf h.S) (Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z))
      (denV (cellsK h.S M) b)) hw (fun b hb x G1 D1 hx => ?_) hq h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  obtain ⟨a1, a2, a3⟩ := readDenominator_rd2 A hc Tb (Nat.le_of_eq hzg.symm) ha hx
  refine ⟨a1, a2, ?_⟩
  rw [a3, e]
  exact rd2_pts A hzi hg hi _

/-- The scalar IB_k is its rule value. -/
theorem linIb (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3)
    (P : PiecesAll h.S h.d.pwX)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp (L5.dimOf h.S) C p.z .x3 b)
    (hzg : h.d.zgX.size = h.S.cf.lgk) (hzi : h.d.ziX.size = h.S.cf.lt)
    (hg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = Inst.Model.AttSeg.xg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ h.d.ziX j = Inst.Model.AttSeg.xi (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.hX h.S.cf.NAs h.S.T (eqTab h.d.ziX)) (k : ℕ)
    {c : Ctx} {q : Aff} {G : Fork} {c1 : Ctx}
    (hq : Ok (lessPieces (Aff.slot (h.d.sIB + k)) h.d.pwX fun w =>
      Attention.readIndexBit h h.t.hX h.d.zgX w.lam w.a k) F c q G c1)
    (h0 : q.value ρ W = 0) :
    W.slot (h.d.sIB + k) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.ib k) := by
  refine less_rule ρ W (h.d.sIB + k) P _ _
    (fun b => rd2 (L5.dimOf h.S) (Inst.Model.AttSeg.xg (L5.dimOf h.S) C p.z)
      (eqT (L5.dimOf h.S) (Inst.Model.AttSeg.xi (L5.dimOf h.S) C p.z))
      (ibV (cellsK h.S M) k b)) hw (fun b hb x G1 D1 hx => ?_) hq h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  obtain ⟨a1, a2, a3⟩ := readIndexBit_rd2 A hc Tb (Nat.le_of_eq hzg.symm) ha hx
  refine ⟨a1, a2, ?_⟩
  rw [a3, e]
  exact rd2_pts A hzi hg hi _

/-! ## A plane below the diagonal -/

/-- A scalar on a plane below the diagonal is its rule value. u: the family (m1 or m2), with its
region M; s0 + jj: the scalar's slot; z: the unit's inner point. -/
theorem linCellM (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3)
    (u : Inst.Model.AttSeg.Fam) (hu : u.reg = .M) (hl : u.l (L5.dimOf h.S) = h.S.nM)
    {pw : Array PW} (P : PiecesAll h.S pw)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) C p.z u b)
    {z : Array E} (hz : z.size = h.S.nM)
    (hv : ∀ j < h.S.nM, pt ρ z j = Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u j)
    (Tb : AsAt h h.t.tA (lastN z h.S.cf.lmS)) (s0 jj : ℕ)
    {c : Ctx} {q : Aff} {G : Fork} {c1 : Ctx}
    (hq : Ok (lessPieces (Aff.slot (s0 + jj)) pw fun w =>
      Attention.plane h h.t.tA jj w.lam w.a z false) F c q G c1)
    (h0 : q.value ρ W = 0) :
    W.slot (s0 + jj) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.cell u jj) := by
  refine less_rule ρ W (s0 + jj) P _ _
    (fun b => Blocks.ext (u.l (L5.dimOf h.S)) (fun x => cellsK h.S M (.c u.reg jj b x))
      (Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u)) hw (fun b hb x G1 D1 hx => ?_) hq h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  obtain ⟨a1, a2, -⟩ := plane_value A hc Tb hx
  refine ⟨a1, a2, ?_⟩
  rw [plane_below A hc Tb hz ha hx, e, hu, hl]
  exact Blocks.ext_congr_point hv _

end Forms

end OnBytes.Road.Rows

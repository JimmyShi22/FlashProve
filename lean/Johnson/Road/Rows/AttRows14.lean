-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttRows14.lean: the public weights of the first four sumchecks of the attention
sub-proof, in the library's words.

A sumcheck of products of the attention sub-proof ends in a row, which the verifier makes from the
weights W_b at the point of the challenges (OnBytes/Model/AttentionScores.lean: scoreFactor;
OnBytes/Model/AttentionDivide.lean: productIn, valueBelowIn). The library has these weights as
polynomials in the point (Wb in Inst/Model/Att/Sums.lean). This file shows that the verifier's
numbers read as the library's polynomials at the verifier's point.

Main theorems.
 - onesOf_value: the product of all coordinates of a point.
 - overTileRows_value: a sum over the tile rows.
 - blkRow_sum: a sum over the blocks under the weights of the row blocks, as a sum over the pairs
   (P, s) that stand for a block.
 - weightProduct, weightFd, weightFm, weightBelow: the weights are Wb at the steps s8, s6d, s6b and
   s11.

What a theorem on a weight takes as given: the lengths of the points, and that the verifier's points
and the weights of its pieces are the library's. For the scores the library cuts its points and
takes its pieces' weights from the first call of the lookup, the verifier from the call of the
scores; the premises ask that they agree.

What this file does not claim. Nothing is said about a run of the verifier: the theorems are on the
expressions that the text of the routines passes to sc3Row. Nothing is said about probabilities or
about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttRows58
import Johnson.Road.Rows.AttEnds14Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading eqTab)
open OnBytes.Attention (Shape PW Seg eqPts onesOf timesW scoreFactor overTileRows tileSums)
open Inst.Model.AttSeg (Dim Calls Pub Wb eqPt sh wp ones blkRow)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Tools -/

/-- The equality polynomial of a point x and the first coordinates of r. -/
theorem eqPts_head {x r : Array E} {n : ℕ} {u : ℕ → K} (hx : x.size = n) (hr : n ≤ r.size)
    (hu : ∀ k < n, pt ρ x k = u k) : ρ.val (eqPts x (r.extract 0 n)) = eqPt n u (pt ρ r) := by
  have e0 := eqPts_cut ρ (r := r) (a := 0) hx (by omega) hu
  rw [Nat.zero_add] at e0
  rw [e0]
  exact eqPt_agree (fun _ _ => rfl) fun k _ => by
    show pt ρ r (0 + k) = pt ρ r k
    rw [Nat.zero_add]

/-- The product of a list of elements, read in the field. -/
theorem foldl_mul (l : List E) (a : E) :
    ρ.val (l.foldl mulE a) = ρ.val a * (l.map ρ.val).prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, ρ.mul, List.map_cons, List.prod_cons, mul_assoc]

/-- The product of the values of a list, by the places of the list. -/
theorem prod_map_getD (l : List E) :
    (l.map ρ.val).prod = ∏ k ∈ range l.length, ρ.val (l.getD k zeroE) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, prod_range_succ', ih, mul_comm]
    simp

/-- The product of all coordinates of a point. -/
theorem onesOf_value (z : Array E) : ρ.val (onesOf z) = ones z.size (pt ρ z) := by
  unfold onesOf ones pt
  rw [← Array.foldl_toList, foldl_mul, ρ.one, one_mul, prod_map_getD, Array.length_toList]
  refine prod_congr rfl fun k _ => ?_
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- The library's product of coordinates reads the first n coordinates alone. -/
theorem ones_agree {n : ℕ} {u u' : ℕ → K} (h : ∀ k < n, u k = u' k) : ones n u = ones n u' := by
  unfold ones
  exact prod_congr rfl fun k hk => h k (mem_range.mp hk)

/-- A sum over the tile rows. -/
theorem overTileRows_value (S : Shape) (wI eI : Array E) :
    ρ.val (overTileRows S wI eI) =
      ∑ I ∈ range S.nT, ρ.val (wI.getD I zeroE) * ρ.val (eI.getD I zeroE) := by
  unfold overTileRows
  generalize S.nT = n
  induction n with
  | zero => simp [ρ.zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.add, ih,
      sum_range_succ, ρ.mul]

/-- A sum over the blocks under the weights of the row blocks, as a sum over the pairs (P, s) that
stand for a block. -/
theorem blkRow_sum (D : Dim) (vP vs : ℕ → K) (H : ℕ → K) :
    ∑ I ∈ range D.nBlk, blkRow D vP vs I * H I =
      ∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1),
        Blocks.eqN D.lP 0 vP P * Blocks.eqN (D.lP + 1) 0 vs s * H (D.rowBlk P s) := by
  unfold blkRow
  simp only [sum_mul]
  refine Eq.trans sum_comm ?_
  refine sum_congr rfl fun P hP => ?_
  refine Eq.trans sum_comm ?_
  refine sum_congr rfl fun s hs => ?_
  have hr := (D.blk_of_slot (mem_range.mp hP) (mem_range.mp hs)).2.1
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq, if_pos (mem_range.mpr hr)]

/-! ## The weights -/

variable (D : Dim) (C : Calls) (p : Pub K)

/-- The weight of pair b in the denominator times the output. -/
theorem weightProduct {pwW : Array PW} {zgW ziW r : Array E} {b : ℕ} (hb : b < pwW.size)
    (hzg : zgW.size = D.lg) (hzi : ziW.size = D.lT) (hr : D.lg + D.lT ≤ r.size)
    (hw : ρ.val (pwW.getD b default).wp = wp D C p.z .w3 b)
    (hg : ∀ k < D.lg, pt ρ zgW k = Inst.Model.AttSeg.yg D C p.z k)
    (hi : ∀ k < D.lT, pt ρ ziW k = Inst.Model.AttSeg.yi D C p.z k) :
    ρ.val ((timesW pwW (mulE (eqPts zgW (r.extract 0 D.lg))
      (eqPts ziW (r.extract D.lg (D.lg + D.lT))))).getD b zeroE) = Wb D C p .s8 b (pt ρ r) := by
  unfold timesW
  rw [getD_map_lt pwW _ hb zeroE default, ρ.mul, ρ.mul, hw, eqPts_cut ρ hzi hr hi,
    eqPts_head ρ hzg (by omega) hg]
  show _ = wp D C p.z .w3 b * eqPt D.lg (Inst.Model.AttSeg.yg D C p.z) (pt ρ r) *
    eqPt D.lT (Inst.Model.AttSeg.yi D C p.z) (sh (pt ρ r) D.lg)
  ring

/-- The weight of pair b in the scores of a unit on the diagonal. S: a shape with the sizes D. -/
theorem weightFd {S : Shape} (hlg : S.cf.lgk = D.lg) (hlP : S.lnT = D.lP + 1) {pw : Array PW}
    {zg zP zs zI r : Array E} {b : ℕ} (hb : b < pw.size)
    (hzg : zg.size = D.lg) (hzI : zI.size = D.lP + 1) (hr : D.lg + (D.lP + 1) ≤ r.size)
    (hw : ρ.val (pw.getD b default).wp = wp D C p.z .d1 b)
    (hg : ∀ k < D.lg, pt ρ zg k = Inst.Model.AttSeg.zgD D C p.z k)
    (hI : ∀ k < D.lP + 1, pt ρ zI k = Inst.Model.AttSeg.zID D C p.z k) :
    ρ.val ((timesW pw (scoreFactor S .fd zg zP zs zI r)).getD b zeroE) =
      Wb D C p .s6d b (pt ρ r) := by
  have e : scoreFactor S .fd zg zP zs zI r = mulE (eqPts zg (r.extract 0 D.lg))
      (eqPts zI (r.extract D.lg (D.lg + (D.lP + 1)))) := by
    rw [← hlg, ← hlP]
    rfl
  unfold timesW
  rw [getD_map_lt pw _ hb zeroE default, e, ρ.mul, ρ.mul, hw, eqPts_cut ρ hzI hr hI,
    eqPts_head ρ hzg (by omega) hg]
  show _ = wp D C p.z .d1 b * eqPt D.lg (Inst.Model.AttSeg.zgD D C p.z) (pt ρ r) *
    eqPt (D.lP + 1) (Inst.Model.AttSeg.zID D C p.z) (sh (pt ρ r) D.lg)
  ring

/-- The weight of pair b in the scores of a unit below the diagonal. -/
theorem weightFm {S : Shape} (hlg : S.cf.lgk = D.lg) (hlP : S.lnT = D.lP + 1) {pw : Array PW}
    {zg zP zs zI r : Array E} {b : ℕ} (hb : b < pw.size)
    (hzg : zg.size = D.lg) (hzP : zP.size = D.lP) (hzs : zs.size = D.lP + 1)
    (hr : D.lg + D.lP + (D.lP + 1) ≤ r.size)
    (hw : ρ.val (pw.getD b default).wp = wp D C p.z .m1 b)
    (hg : ∀ k < D.lg, pt ρ zg k = Inst.Model.AttSeg.zg D C p.z k)
    (hP : ∀ k < D.lP, pt ρ zP k = Inst.Model.AttSeg.zP D C p.z k)
    (hs : ∀ k < D.lP + 1, pt ρ zs k = Inst.Model.AttSeg.zs D C p.z k) :
    ρ.val ((timesW pw (scoreFactor S .fm zg zP zs zI r)).getD b zeroE) =
      Wb D C p .s6b b (pt ρ r) := by
  have hl : S.lnT - 1 = D.lP := by omega
  have e : scoreFactor S .fm zg zP zs zI r =
      mulE (mulE (eqPts zg (r.extract 0 D.lg)) (eqPts zP (r.extract D.lg (D.lg + D.lP))))
        (subE (eqPts zs (r.extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1))))
          (mulE (onesOf zs) (onesOf (r.extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1)))))) := by
    rw [← hlg, ← hlP, ← hl]
    rfl
  have s1 : (r.extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1))).size = D.lP + 1 := by
    rw [sizeCut _ hr]
    omega
  unfold timesW
  rw [getD_map_lt pw _ hb zeroE default, e, ρ.mul, ρ.mul, ρ.mul, ρ.sub, ρ.mul, hw,
    eqPts_cut ρ hzs hr hs, eqPts_cut ρ hzP (by omega) hP, eqPts_head ρ hzg (by omega) hg,
    onesOf_value, onesOf_value, hzs, s1, ones_agree hs,
    ones_agree (u' := sh (pt ρ r) (D.lg + D.lP)) fun k hk => ptCut ρ r hr (by omega)]
  show _ = wp D C p.z .m1 b * eqPt D.lg (Inst.Model.AttSeg.zg D C p.z) (pt ρ r) *
    eqPt D.lP (Inst.Model.AttSeg.zP D C p.z) (sh (pt ρ r) D.lg) *
    (eqPt (D.lP + 1) (Inst.Model.AttSeg.zs D C p.z) (sh (pt ρ r) (D.lg + D.lP)) -
      ones (D.lP + 1) (Inst.Model.AttSeg.zs D C p.z) * ones (D.lP + 1) (sh (pt ρ r) (D.lg + D.lP)))
  ring

/-- The weight of pair b in the value product below the diagonal, at a shape S with its sizes. -/
theorem weightBelow {S : Shape} (Z : Sizes S) {pwW : Array PW} {zgW zihi r : Array E} {b : ℕ}
    (hb : b < pwW.size) (hzg : zgW.size = S.cf.lgk) (hzi : zihi.size = S.lnT)
    (hr : S.cf.lgk + (S.lnT - 1) + S.lnT ≤ r.size)
    (hw : ρ.val (pwW.getD b default).wp = wp (L5.dimOf S) C p.z .w3 b)
    (hg : ∀ k < S.cf.lgk, pt ρ zgW k = Inst.Model.AttSeg.yg (L5.dimOf S) C p.z k)
    (hi : ∀ k < S.lnT, pt ρ zihi k = Inst.Model.AttSeg.yI (L5.dimOf S) C p.z k) :
    ρ.val ((timesW pwW (mulE
      (overTileRows S (tileSums S (eqTab (r.extract S.cf.lgk (S.cf.lgk + (S.lnT - 1))))
        (eqTab (r.extract (S.cf.lgk + (S.lnT - 1)) (S.cf.lgk + (S.lnT - 1) + S.lnT)))).1
        (eqTab zihi))
      (eqPts zgW (r.extract 0 S.cf.lgk)))).getD b zeroE) =
      Wb (L5.dimOf S) C p .s11 b (pt ρ r) := by
  have hl := Z.lnT
  have e1 : S.lnT = S.lnT - 1 + 1 := by omega
  have sP : (r.extract S.cf.lgk (S.cf.lgk + (S.lnT - 1))).size = S.lnT - 1 := by
    rw [sizeCut _ (by omega)]
    omega
  have sS : (r.extract (S.cf.lgk + (S.lnT - 1)) (S.cf.lgk + (S.lnT - 1) + S.lnT)).size =
      S.lnT := by
    rw [sizeCut _ hr]
    omega
  have vP : ∀ j < S.lnT - 1, pt ρ (r.extract S.cf.lgk (S.cf.lgk + (S.lnT - 1))) j =
      sh (pt ρ r) (L5.dimOf S).lg j := fun j hj => ptCut ρ _ (by omega) (by omega)
  have vS : ∀ j < S.lnT,
      pt ρ (r.extract (S.cf.lgk + (S.lnT - 1)) (S.cf.lgk + (S.lnT - 1) + S.lnT)) j =
        sh (pt ρ r) ((L5.dimOf S).lg + (L5.dimOf S).lP) j :=
    fun j hj => ptCut ρ _ hr (by omega)
  have hsum : ρ.val (overTileRows S
      (tileSums S (eqTab (r.extract S.cf.lgk (S.cf.lgk + (S.lnT - 1))))
        (eqTab (r.extract (S.cf.lgk + (S.lnT - 1)) (S.cf.lgk + (S.lnT - 1) + S.lnT)))).1
      (eqTab zihi)) =
      ∑ I ∈ range (L5.dimOf S).nBlk,
        blkRow (L5.dimOf S) (sh (pt ρ r) (L5.dimOf S).lg)
          (sh (pt ρ r) ((L5.dimOf S).lg + (L5.dimOf S).lP)) I *
          Blocks.eqN ((L5.dimOf S).lP + 1) 0 (Inst.Model.AttSeg.yI (L5.dimOf S) C p.z) I := by
    rw [overTileRows_value, dim_nBlk Z]
    refine sum_congr rfl fun I hI => ?_
    have hI' : I < S.nT := by rw [dim_nBlk Z]; exact mem_range.mp hI
    rw [tiles_row ρ Z sP sS vP vS hI', eqTab_at ρ hzi hi (by rw [← Z.nT]; exact hI')]
    show _ * Blocks.eqN S.lnT 0 _ I = _ * Blocks.eqN (S.lnT - 1 + 1) 0 _ I
    rw [← e1]
  unfold timesW
  rw [getD_map_lt pwW _ hb zeroE default, ρ.mul, ρ.mul, hw, hsum, blkRow_sum,
    eqPts_head ρ hzg (by omega) hg]
  show _ * (_ * eqPt (L5.dimOf S).lg (Inst.Model.AttSeg.yg (L5.dimOf S) C p.z) (pt ρ r)) =
    wp (L5.dimOf S) C p.z .w3 b *
      eqPt (L5.dimOf S).lg (Inst.Model.AttSeg.yg (L5.dimOf S) C p.z) (pt ρ r) * _
  ring

end OnBytes.Road.Rows

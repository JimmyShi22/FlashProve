-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidBaseMember.lean: BaseSeg has a member, and the guard of the sum can be met
at messages that ARE a packing.

Johnson/Goal/Meaning/HidBase.lean shows that BaseSeg can fail (notBase_big). This file shows that it
can hold: the messages msgOf (Johnson/Goal/Meaning/HidPack.lean) are, at every sub-proof, the
packing of the family from which they are made. And the guard sum_met
(Johnson/Goal/Meaning/HidSumGuard.lean) is met at such messages: the three premises of means_follows
and BaseSeg at all 25 sub-proofs hold together.

Main names:
  baseSeg_msgOf   under the premises of ownAt_msgOf: BaseSeg s (seatBy seat0 X s) (msgOf s seen) k.
  sum_met_base   sum_met with one conjunct more: BaseSeg at all 25 sub-proofs, at the same f and
    msg.
  closedAt_closedRec   in scope the records closedRec X funs
    (Johnson/Goal/Meaning/HidSumClosed.lean) meet ClosedAt.

What is not claimed. What the head of Johnson/Goal/Meaning/HidSumGuard.lean disclaims: the messages
are made up. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidSumClosed
import Johnson.Goal.Meaning.HidBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Cb.Pv.Tail (Size)

/-- **A member of BaseSeg**: the messages msgOf are the packing of the family from which they are
made. -/
theorem baseSeg_msgOf {X : Model.Verify.Public} {s : ℕ → Size} {seen : ℕ → Mats ℤ} {k : ℕ} (p : ℕ)
    [CharP Cb.Gl.E p] (U : (s k).Uniq p)
    (sm : ∀ a < (s k).NM, ∀ r < (s k).m a, ∀ c < (s k).k a,
      |seen k a r c| < 2 * ((s k).beta : ℤ))
    (O : OwnSame X s seen k) : BaseSeg s (seatBy seat0 X s) (msgOf s seen) k := by
  refine ⟨cutOf (s k) (seen k), Cb.Pv.Tail.baseAt_of_packs p U
    (fun μ c i => sm μ.val μ.isLt i.val i.isLt c.val c.isLt) fun μ c i' => ?_⟩
  show ((packTot ((s (ownerK (labAt X k μ.val))).rad : ℤ)
      ((s (ownerK (labAt X k μ.val))).m (ownerA (labAt X k μ.val)))
      (fun r => seen (ownerK (labAt X k μ.val)) (ownerA (labAt X k μ.val)) r c.val) i'.val : ℤ) :
        Cb.Gl.E) = ((Alg.pack ((s k).rad : ℤ) (cutOf (s k) (seen k) μ c) i'.val : ℤ) : Cb.Gl.E)
  rw [O.rad μ.val μ.isLt, O.m μ.val μ.isLt]
  unfold packTot
  congr 2
  funext r
  exact O.val μ.val μ.isLt r.val r.isLt c.val c.isLt

/-- **The premises of the sum can be met together at messages that are a packing**: sum_met with
BaseSeg at all 25 sub-proofs. -/
theorem sum_met_base {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) {s : ℕ → Size} (F : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20) :
    ∃ (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      (∀ k < 25, BaseSeg s (seatBy f X s) msg k) ∧
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
        (ownAt s (seatBy f X s) msg (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X (ownAt s (seatBy f X s) msg 24)) := by
  obtain ⟨w, -, M⟩ := means_of_true hZ hR h i x T
  have C := Hd.core_of_scope hZ hR h
  have N := xoNum_of_core h C
  have E : ∀ k < 25, ownAt s (seatBy seat0 X s) (msgOf s (seenC X w)) k =
      mzTot (cutOf (s k) (seenC X w k)) := fun k hk =>
    ownAt_msgOf Cb.Gl.p (Cb.Pv.Tail.uniq_gl (hb k hk) (hr k hk))
      (fun a _ r _ c _ => by
        rw [hb k hk]
        have := clip_small (seenOf X w k) a r c
        have e : (2 : ℤ) * ((2 ^ 17 : ℕ) : ℤ) = 2 ^ 18 := by norm_num
        rw [e]
        exact this)
      (ownSame_seenC h C F M hk)
  have sm : ∀ k < 25, ∀ a < (s k).NM, ∀ r < (s k).m a, ∀ c < (s k).k a,
      |seenC X w k a r c| < 2 * ((s k).beta : ℤ) := fun k hk a _ r _ c _ => by
    rw [hb k hk]
    have := clip_small (seenOf X w k) a r c
    have e : (2 : ℤ) * ((2 ^ 17 : ℕ) : ℤ) = 2 ^ 18 := by norm_num
    rw [e]
    exact this
  refine ⟨seat0, msgOf s (seenC X w), fun k hk => baseSeg_msgOf Cb.Gl.p
    (Cb.Pv.Tail.uniq_gl (hb k hk) (hr k hk)) (sm k hk) (ownSame_seenC h C F M hk),
    fun g hg => ?_, fun g hg => ?_, ?_⟩
  · rw [E _ (by omega)]
    refine layerOrd_congr_core h C hg (fun σ r c hz => ?_) (M.layers g hg).ord
    obtain ⟨a1, a2, a3⟩ := inZ_in h C F hg hz
    rw [mzTot_cutOf _ _ a1 a2 a3]
    show w.MG g (portNo X.y σ) r c = clip (seenOf X w (2 * g)) (portNo X.y σ) r c
    rw [seenOf_even X w hg, clip_of_small ((M.layers g hg).small σ r c hz)]
  · rw [E _ (by omega)]
    refine ord_of_ownA ((ownA_congr fun c hv => ?_).mp (ownA_of_ord (M.attention g hg).ord))
    obtain ⟨a1, a2, a3⟩ := inside_of_follows h C F hg c hv
    unfold zAt
    rw [mzTot_cutOf _ _ a1 a2 a3]
    show _ = clip (seenOf X w (2 * g + 1)) _ _ _
    rw [seenOf_odd, clip_of_small ((M.attention g hg).small c hv)]
  · rw [E 24 (by norm_num)]
    have H0 : HeadPlain pp i x (headStream X (seenOf X w 24)) := by
      refine SaysHead.congr (fun pos hp j hj => ?_) (fun _ _ _ => rfl) M.head.plain
      rw [M.head.seam pos hp j hj, lastOf_lastIn N (w.MG 11) pos hp j hj,
        ← lastIn_head h C (seenOf X w 24) pos hp j hj]
      rfl
    obtain ⟨Mh, b1, b2, b3, -⟩ := entryH h C
    have hn : X.hS.NHf + 3 < (matsAt X 24).size := (Array.getElem?_eq_some_iff.1 b1).1
    have e24 : ∀ r < 65536, ∀ c < 400, seenOf X w 24 (X.hS.NHf + 3) r c =
        mzTot (cutOf (s 24) (seenC X w 24)) (X.hS.NHf + 3) r c := by
      intro r hr' c hc'
      have a1 : X.hS.NHf + 3 < (s 24).NM := by
        rw [F.NM 24 (by norm_num)]
        exact hn
      have a2 : c < (s 24).k (X.hS.NHf + 3) := by
        rw [F.k 24 (by norm_num) _ hn, getD_of b1, b3]
        show c < X.y.kxb
        rw [N.kxb]
        exact hc'
      have a3 : r < (s 24).m (X.hS.NHf + 3) := by
        rw [F.m 24 (by norm_num) _ hn, getD_of b1, b2]
        show r < X.y.mxb
        rw [N.mxb]
        exact hr'
      rw [mzTot_cutOf _ _ a1 a2 a3]
      show _ = clip (seenOf X w 24) (X.hS.NHf + 3) r c
      refine (clip_of_small ?_).symm
      show |w.MG 11 (matIx X.y).iXO r c| < 2 ^ 18
      exact (M.layers 11 (by norm_num)).small 7 r c
        ⟨by norm_num, by show r < X.y.mxb; rw [N.mxb]; exact hr',
          by show c < X.y.kxb; rw [N.kxb]; exact hc'⟩
    exact SaysHead.congr (fun pos hp j hj =>
      (lastIn_head h C (seenOf X w 24) pos hp j hj).symm.trans
        ((lastIn_congr N e24 pos hp j hj).trans (lastIn_head h C _ pos hp j hj)))
      (fun _ _ _ => rfl) H0

/-- In scope the records closedRec X funs meet ClosedAt. -/
theorem closedAt_closedRec {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (funs : ℕ → Array Model.HFun) :
    ClosedAt X (closedRec X funs) := closedAt_core h C funs

end Meaning

#print axioms Meaning.baseSeg_msgOf
#print axioms Meaning.sum_met_base
#print axioms Meaning.closedAt_closedRec

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortCl.lean: if the verifier's claims 6, 7 and 8 on the end values of the last
four sumchecks of an attention sub-proof have the value 0, the library-side claims hold, at any
values of the late entries.

Cb/Pv/Att/End/LastOut.lean and Cb/Pv/Att/End/Cl.lean write the verifier's claims in the library's
names, as forms on early and late entries. Johnson/Road/Rows/AttPortLate.lean holds the forms that
the claims read against each other. This file draws the conclusion for the claims, for all pairs,
layers and bits at once. No table is taken to be true: the theorems hold for all values u of the
late entries that meet the dictionary.

Main definitions.
 - SlotAt W T o x j a: the hidden value under slot j is what the library-side claim on the end value
   a says it is: what was shown, less the last coordinate times the mask entry.
Main theorems. x is Sum.elim m u.
 - on_cl: the claims on both end values of every pair of the value product on the diagonal tiles.
 - m6_cl: the claims on the pairs' scalars.
 - score_cl: the claims on the first end values of the score at the index.
 - key_cl: the claims on all end values of the key at the index.
 - bits_cl: the claims on both end values of every pair of the sumcheck for the bits.

What the theorems take as given: that the forms have been made and the verifier's claims have the
value 0 (OnGiven, IndexGiven, BitsGiven in Johnson/Road/Rows/AttEndsAt58.lean); the dictionary
LateAt; the premises on names; SlotAt for each end value; the lengths of the verifier's points; that
the challenges and the point of the output statement are the verifier's.

What is not claimed. The claims on the sumchecks' rows are not treated. That the verifier adds just
these claims. That the dictionary and SlotAt hold of a run. Nothing is said about probabilities or
about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttPortLate
import Johnson.Road.Rows.AttEndsAt58
import Cb.Pv.Att.End.LastOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset Cb
open OnBytes.Model (Reading World Aff Fork)
open OnBytes.Attention (Heard sc3A sc3B)
open Inst.Model.AttSeg (Raw Calls Pub Step yn)
open Cb.Pv.Att (PlainSc stepSc3 step18 size18 bitsSc3)
open Cb.Pv.Att.End (LateLay AttTab endF endF_at ptN pick keyR bitsR slotF rA12 rB12 rM6 rA16 rA21
  ptOn linF Good12 GoodM Good16 Good18 GoodH val_aSub val_aConst val_aSmul val_aEnt)

variable {K : Type} [Field K] [Fintype K]

/-- The hidden value under slot j is what the library-side claim on the end value a says it is. -/
def SlotAt (W : World K) (T : PlainSc K) {J₂ : Type} (o : T.our.par.Out) (x : T.J ⊕ J₂ → K) (j : ℕ)
    (a : T.A) : Prop :=
  W.slot j = o.vals a - T.our.lst o.st (T.our.par.hp o.st o.pt) * x (.inl (T.cAt a))

variable {ρ : Reading K} {W : World K} {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → K} {m : J₁ → K}
  {rd : (J₁ → K) → Raw → K} {inc : Pub K → J₁ → K}

/-- The value product on the diagonal tiles. -/
theorem on_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (Cc : Calls) {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt K (Step.s12.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy K 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s12 inc wAt cAt).plain.our.par.Out)
    (g : OnGiven ρ W K3 h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2)
    (hnD : (L5.dimOf h.S).lD = h.S.nD) (hz : h.t.ptD.size = h.S.nD)
    (hr : h.S.cf.lgk ≤ h.d.vpd.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN _ o j = pt ρ h.d.vpd.r j)
    (hpt : ∀ j < h.S.nD - h.S.cf.lmS,
      pt ρ h.t.ptD j = ptOn (L5.dimOf h.S) Cc o.st (ptN _ o) j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc (Pub.z o.st) j)
    (hgam : ρ.val h.d.gam = Pub.th o.st) (hG : Good12 (L5.dimOf h.S) h.S.ls h.S.cf.lmS Y)
    (hs : ∀ b : Fin (L5.dimOf h.S).nb,
      SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s12 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.vpd.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s12 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.vpd.sEnd + (2 * b.val + 1)) (b, true))
    (a : Fin (L5.dimOf h.S).nb × Bool) :
    (endF (stepSc3 (L5.dimOf h.S) Cc rd .s12 inc wAt cAt).plain o a
      (pick (rA12 (L5.dimOf h.S) Cc h.S.cf.lmS Y o.st (ptN _ o))
        (rB12 (L5.dimOf h.S) Cc h.S.ls Y o.st (ptN _ o)) a)).Holds (Sum.elim m u) := by
  obtain ⟨b, s⟩ := a
  have hb : b.val < h.S.NP := b.isLt
  obtain ⟨hsz, hpw⟩ := P
  have hb' : b.val < h.d.pwW.size := by rw [hsz]; exact hb
  have hw : h.d.pwW[b.val]? = some h.d.pwW[b.val] := Array.getElem?_eq_getElem hb'
  obtain ⟨e1, e2⟩ := hpw b.val hb _ hw
  obtain ⟨p3, p4, v, F, F', G, G', G'', c, c1, c', c1', c'', c1'', k1, k2, r1, r2, r3, v1, v2⟩ :=
    g b.val _ hw
  have ha : h.d.pwW[b.val].a < h.S.HA := by
    rw [e2]
    exact Nat.mod_lt b.val (heads_pos hb)
  have eb : h.d.pwW[b.val].lam * h.S.HA + h.d.pwW[b.val].a = b.val := by
    rw [e1, e2]
    exact Nat.div_add_mod' b.val h.S.HA
  cases s with
  | false =>
    refine (end_port _ o (b, false) _ (Sum.elim m u) (h.d.vpd.sEnd + 2 * b.val) _ (hs b).1 ?_).mp v1
    have e := weight_port m A.num k1 L Tb (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnD hz hpt
      (by rw [eb, ← hnD]; exact hG.tVD b.val b.isLt) k1 (ok_of_yields r1) (ok_of_yields r2)
    rw [eb] at e
    exact e
  | true =>
    refine (end_port _ o (b, true) _ (Sum.elim m u) (h.d.vpd.sEnd + (2 * b.val + 1)) _ (hs b).2
      ?_).mp v2
    exact value_port m A k2 L Tb (Cc := Cc) (p := o.st) (ξ := ptN _ o) (b := b.val) e1.symm hnl hr
      hzc hξ hyn hgam (by rw [e1]; exact hG.qVD b.val b.isLt) (ok_of_yields r3)

omit [Fintype K] in
/-- The pairs' scalars. s b: what was sent for pair b; k b: the place of its mask entry. -/
theorem m6_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (p : Pub K) (g : IndexGiven ρ W K3 h)
    (htg : h.x.tg.size = h.S.cf.lgk) (hp : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j)
    (hG : GoodM (L5.dimOf h.S) Y) (s : ℕ → K) (k : ℕ → J₁)
    (hs : ∀ b < h.S.NP, W.slot (h.x.sM6 + b) = s b - m (k b)) (b : ℕ) (hb : b < h.S.NP) :
    (linF (s b) (k b) (rM6 (L5.dimOf h.S) Y p b)).Holds (Sum.elim m u) := by
  obtain ⟨q, F, G, c, c1, k1, r1, v1⟩ := g.m6 b hb
  have e := max_port m A k1 L Tb hb htg hp (hG.hT b hb) (ok_of_yields r1)
  rw [Aff.value_sub, Aff.value_slot, hs b hb, e] at v1
  unfold Cb.Pv.Att.End.linF Cb.Pv.Att.End.hidF
  rw [TWhole.Aff.claim_holds, val_aSub, val_aSub, val_aConst, val_aEnt]
  exact v1

/-- The score at the index: the first end values. -/
theorem score_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (Cc : Calls) {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt K (Step.s16.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy K 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s16 inc wAt cAt).plain.our.par.Out)
    (g : IndexGiven ρ W K3 h) (hnl : h.S.atQ.nl = 2)
    (hr : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh, ptN _ o j = pt ρ h.x.scF.r j)
    (hG : Good16 (L5.dimOf h.S) h.S.ls Y)
    (hs : ∀ b : Fin (L5.dimOf h.S).nb,
      SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s16 inc wAt cAt).plain o (Sum.elim m u)
        (h.x.scF.sEnd + 2 * b.val) (b, false))
    (b : Fin (L5.dimOf h.S).nb) :
    (endF (stepSc3 (L5.dimOf h.S) Cc rd .s16 inc wAt cAt).plain o (b, false)
      (rA16 (L5.dimOf h.S) h.S.ls Y (ptN _ o) b.val)).Holds (Sum.elim m u) := by
  obtain ⟨q, F, G, c, c1, k1, r1, v1⟩ := g.qry b.val b.isLt
  exact (end_port _ o (b, false) _ (Sum.elim m u) (h.x.scF.sEnd + 2 * b.val) _ (hs b)
    (query_port m A k1 L Tb hnl hr hξ (hG.qF b.val b.isLt) (ok_of_yields r1))).mp v1

/-- The key at the index, read at other public states St' through f. -/
theorem key_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) {St' : Type} (f : St' → Pub K) (inc' : St' → J₁ → K)
    {wAt : PIdx (ldPartFmt K (size18 (L5.dimOf h.S)).k (size18 (L5.dimOf h.S)).deg ++
      [pDummy K ((size18 (L5.dimOf h.S)).lt + 1)]) → J₁}
    {cAt : (size18 (L5.dimOf h.S)).A → J₁}
    (o : ((step18 (L5.dimOf h.S) rd inc wAt cAt).plain.pull f inc').our.par.Out)
    (g : IndexGiven ρ W K3 h) (hnl : h.S.atK.nl = 2)
    (hrF : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    (hξ : ∀ j < 2 * h.S.cf.lt + h.S.cf.lgk, ptN _ o j = pt ρ h.x.scd.r j)
    (hfn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = (f o.st).fn j)
    (hG : Good18 (L5.dimOf h.S) h.S.ls Y)
    (hsK : ∀ l : Fin (size18 (L5.dimOf h.S)).Lam,
      SlotAt W ((step18 (L5.dimOf h.S) rd inc wAt cAt).plain.pull f inc') o (Sum.elim m u)
        (h.x.sKC + l.val) (.inl l))
    (hsB : ∀ (b : Fin (size18 (L5.dimOf h.S)).pairs) (t : Fin (size18 (L5.dimOf h.S)).lt),
      SlotAt W ((step18 (L5.dimOf h.S) rd inc wAt cAt).plain.pull f inc') o (Sum.elim m u)
        (h.x.sIb h.S b.val t.val) (.inr (b, t)))
    (a : (size18 (L5.dimOf h.S)).A) :
    (endF ((step18 (L5.dimOf h.S) rd inc wAt cAt).plain.pull f inc') o a
      (keyR (L5.dimOf h.S) h.S.ls Y (f o.st) (ptN _ o) a)).Holds (Sum.elim m u) := by
  have hlT := pub_lT A
  rcases a with l | ⟨b, t⟩
  · obtain ⟨q, F, G, c, c1, k1, r1, v1⟩ := g.key l.val l.isLt
    exact (end_port _ o (.inl l) _ (Sum.elim m u) (h.x.sKC + l.val) _ (hsK l)
      (key_port m A k1 L Tb hnl hrF hr hξ hfn (hG.qKx l.val l.isLt) (ok_of_yields r1))).mp v1
  · have ht : t.val < h.S.cf.lt := by
      have := t.isLt
      have e : (size18 (L5.dimOf h.S)).lt = (L5.dimOf h.S).lT := rfl
      omega
    obtain ⟨q, F, G, c, c1, k1, r1, v1⟩ := g.bit b.val b.isLt t.val ht
    exact (end_port _ o (.inr (b, t)) _ (Sum.elim m u) (h.x.sIb h.S b.val t.val) _ (hsB b t)
      (ibit_port m A k1 L Tb b.isLt hr hξ (hG.hPi b.val b.isLt t.val t.isLt)
        (ok_of_yields r1))).mp v1

/-- The bits of the index. -/
theorem bits_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt K ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4) (fun _ => 3) ++
      [pDummy K 2]) → J₁}
    (o : (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain.our.par.Out)
    (g : BitsGiven ρ W K3 h) (hr : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + 4, ptN _ o j = pt ρ h.x.scH.r j)
    (hG : GoodH (L5.dimOf h.S) Y)
    (hs : ∀ b : Fin (L5.dimOf h.S).nb,
      SlotAt W (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o (Sum.elim m u)
          (h.x.scH.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o (Sum.elim m u)
          (h.x.scH.sEnd + (2 * b.val + 1)) (b, true))
    (a : Fin (L5.dimOf h.S).nb × Bool) :
    (endF (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o a
      (bitsR (L5.dimOf h.S) Y rd inc 4 cAt wAt o a)).Holds (Sum.elim m u) := by
  have hlT := pub_lT A
  obtain ⟨b, s⟩ := a
  obtain ⟨f, F, G, c, c1, k1, r1, v1, v2⟩ := g b.val b.isLt
  cases s with
  | false =>
    have e := bits_port m A k1 L Tb b.isLt hr hξ
      (fun k hk => hG.hR2 b.val b.isLt k (by rw [hlT]; exact hk)) (ok_of_yields r1)
    rw [v1, (hs b).1] at e
    rw [endF_at]
    show _ = (rA21 (L5.dimOf h.S) Y 4 (ptN _ o) b.val).val (Sum.elim m u)
    exact (sub_eq_zero.mp e.symm)
  | true =>
    have e1 : (sc3B h.x.scH b.val).value ρ W = W.slot (h.x.scH.sEnd + (2 * b.val + 1)) :=
      Aff.value_slot ρ W _
    have e2 : (sc3A h.x.scH b.val).value ρ W = W.slot (h.x.scH.sEnd + 2 * b.val) :=
      Aff.value_slot ρ W _
    rw [Aff.value_add, Aff.value_sub, Aff.value_ofConst, ρ.one, e1, e2] at v2
    have v3 : W.slot (h.x.scH.sEnd + (2 * b.val + 1)) = W.slot (h.x.scH.sEnd + 2 * b.val) - 1 := by
      linear_combination v2
    have sA : (slotF (J₂ := J₂) (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o (b, false)).val
        (Sum.elim m u) = W.slot (h.x.scH.sEnd + 2 * b.val) := by
      unfold Cb.Pv.Att.End.slotF
      rw [val_aSub, val_aConst, val_aSmul, val_aEnt]
      exact (hs b).1.symm
    rw [endF_at]
    show _ = (Cb.Pv.Att.End.aSub
      (slotF (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o (b, false))
      (Cb.Pv.Att.End.aConst 1)).val (Sum.elim m u)
    rw [val_aSub, val_aConst, sA, ← v3]
    exact (hs b).2.symm

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.on_cl
#print axioms OnBytes.Road.Rows.m6_cl
#print axioms OnBytes.Road.Rows.score_cl
#print axioms OnBytes.Road.Rows.key_cl
#print axioms OnBytes.Road.Rows.bits_cl

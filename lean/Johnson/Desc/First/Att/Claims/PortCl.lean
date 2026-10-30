-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortCl.lean: kind K5: what claims 6, 7 and 8 say on the end values of
the last four sumchecks (Johnson/Desc/First/Att/Claims/Say58.lean: Say6.on, Say7, Say8) gives the
library-side claims (Cb/Pv/Att/End/LastOut.lean, Cl.lean), at any values of the late entries. Twins
of on_cl, m6_cl, score_cl, key_cl and bits_cl (Johnson/Road/Rows/AttPortCl.lean), whose "…Given"
records hold runs of routines in a context: here Say6, Say7 and Say8 stand in their place. No table
is taken to be true. The proofs follow those proofs line for line, with the twin of
Johnson/Desc/First/Att/Claims/PortLate.lean where the port stood.

Main names:
  `end_of`: the equation "slot = the written form's worth", SlotAt and the port give the
    library-side claim on the end value.
  `onF_cl`, `m6F_cl`, `scoreF_cl`, `keyF_cl`, `bitsF_cl`.
Taken as given, as in Johnson/Road/Rows/AttPortCl.lean: AttPub; the dictionary LateAt; LateTabs; the
premises on names (Good12 …); SlotAt for each end value; the lengths of the verifier's points; that
the challenges and the point of the output statement are the verifier's. And InTail
(Johnson/Desc/First/Att/Claims/EndsAll.lean), for the lawful heads: paid by in_tail
(Johnson/Desc/First/Att/Claims/InRunAll.lean).
Limit: the claims on the sumchecks' rows are not treated.
Used: as Johnson/Desc/First/Att/Claims/PortLate.lean, and SlotAt, end_port, PiecesAll; the library's
stepSc3, step18, size18, bitsSc3, endF, endF_at, ptN, pick, keyR, bitsR, slotF, linF, hidF, Good12,
GoodM, Good16, Good18, GoodH.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttPortCl
import Johnson.Desc.First.Att.Claims.PortLate
import Johnson.Desc.First.Att.Claims.EndsAll

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset Cb
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Calls Pub Step yn)
open Cb.Pv.Att (PlainSc stepSc3 step18 size18 bitsSc3)
open Cb.Pv.Att.End (LateLay AttTab endF endF_at ptN pick keyR bitsR slotF rA12 rB12 rM6 rA16 rA21
  ptOn linF Good12 GoodM Good16 Good18 GoodH val_aSub val_aConst val_aSmul val_aEnt)

variable {Kf : Type} [Field Kf] [Fintype Kf]

/-- From "slot = the written form's worth" to the library-side claim on the end value. -/
theorem end_of {ρ : Reading Kf} {W : World Kf} (T : PlainSc Kf) {J₂ : Type}
    [Fintype J₂] [DecidableEq J₂] [DecidableEq T.J] (o : T.our.par.Out) (a : T.A)
    (r : TWhole.Aff Kf (T.J ⊕ J₂)) (x : T.J ⊕ J₂ → Kf) (j : ℕ) (q : Aff)
    (hs : SlotAt W T o x j a) (hq : q.value ρ W = r.val x) (e : W.slot j = q.value ρ W) :
    (endF T o a r).Holds x := by
  refine (end_port T o a r x j q hs hq).mp ?_
  rw [Aff.value_sub, Aff.value_slot, e, sub_self]

variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → Kf} {m : J₁ → Kf}
  {rd : (J₁ → Kf) → Raw → Kf} {inc : Pub Kf → J₁ → Kf}

/-- The value product on the diagonal tiles. -/
theorem onF_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (Cc : Calls) {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s12.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s12 inc wAt cAt).plain.our.par.Out)
    (s6 : Say6 ρ W h K3) (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2)
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
  have hgd := getD_of hw
  have v1 := s6.on.ends (2 * b.val) (by omega)
  have v2 := s6.on.ends (2 * b.val + 1) (by omega)
  unfold endsV at v1 v2
  rw [if_pos (by omega), show 2 * b.val / 2 = b.val by omega, hgd] at v1
  rw [if_neg (by omega), show (2 * b.val + 1) / 2 = b.val by omega, hgd] at v2
  have ha : h.d.pwW[b.val].a < h.S.HA := by
    rw [e2]
    exact Nat.mod_lt b.val (heads_pos hb)
  have eb : h.d.pwW[b.val].lam * h.S.HA + h.d.pwW[b.val].a = b.val := by
    rw [e1, e2]
    exact Nat.div_add_mod' b.val h.S.HA
  cases s with
  | false =>
    refine end_of _ o (b, false) _ (Sum.elim m u) (h.d.vpd.sEnd + 2 * b.val) _ (hs b).1 ?_ v1
    have e := weightF_port (K3 := K3) m A.num L Tb (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnD hz hpt
      (by rw [eb, ← hnD]; exact hG.tVD b.val b.isLt)
    rw [eb] at e
    exact e
  | true =>
    refine end_of _ o (b, true) _ (Sum.elim m u) (h.d.vpd.sEnd + (2 * b.val + 1)) _ (hs b).2 ?_ v2
    exact valueF_port m A L Tb (Cc := Cc) (p := o.st) (ξ := ptN _ o) (b := b.val) e1.symm hnl hr
      hzc hξ hyn hgam (by rw [e1]; exact hG.qVD b.val b.isLt) (I.qVD b.val hb _ hw).feat

omit [Fintype Kf] in
/-- The pairs' scalars. s b: what was sent for pair b; k b: the place of its mask entry. -/
theorem m6F_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (p : Pub Kf) (s7 : Say7 ρ W h K3)
    (htg : h.x.tg.size = h.S.cf.lgk) (hp : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j)
    (hG : GoodM (L5.dimOf h.S) Y) (s : ℕ → Kf) (k : ℕ → J₁)
    (hs : ∀ b < h.S.NP, W.slot (h.x.sM6 + b) = s b - m (k b)) (b : ℕ) (hb : b < h.S.NP) :
    (linF (s b) (k b) (rM6 (L5.dimOf h.S) Y p b)).Holds (Sum.elim m u) := by
  have v1 := s7.maxima b hb
  have e := maxF_port (K3 := K3) m A L Tb hb htg hp (hG.hT b hb)
  rw [hs b hb, e] at v1
  unfold Cb.Pv.Att.End.linF Cb.Pv.Att.End.hidF
  rw [TWhole.Aff.claim_holds, val_aSub, val_aSub, val_aConst, val_aEnt]
  exact sub_eq_zero.mpr v1

/-- The score at the index: the first end values. -/
theorem scoreF_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (Cc : Calls) {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s16.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s16 inc wAt cAt).plain.our.par.Out)
    (s7 : Say7 ρ W h K3) (I : InTail h) (hnl : h.S.atQ.nl = 2)
    (hr : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh, ptN _ o j = pt ρ h.x.scF.r j)
    (hG : Good16 (L5.dimOf h.S) h.S.ls Y)
    (hs : ∀ b : Fin (L5.dimOf h.S).nb,
      SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s16 inc wAt cAt).plain o (Sum.elim m u)
        (h.x.scF.sEnd + 2 * b.val) (b, false))
    (b : Fin (L5.dimOf h.S).nb) :
    (endF (stepSc3 (L5.dimOf h.S) Cc rd .s16 inc wAt cAt).plain o (b, false)
      (rA16 (L5.dimOf h.S) h.S.ls Y (ptN _ o) b.val)).Holds (Sum.elim m u) :=
  end_of _ o (b, false) _ (Sum.elim m u) (h.x.scF.sEnd + 2 * b.val) _ (hs b)
    (queryF_port m A L Tb hnl hr hξ (hG.qF b.val b.isLt) (I.qF b.val b.isLt).feat)
    (s7.endsF b.val b.isLt)

/-- The key at the index, read at other public states St' through f. -/
theorem keyF_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) {St' : Type} (f : St' → Pub Kf) (inc' : St' → J₁ → Kf)
    {wAt : PIdx (ldPartFmt Kf (size18 (L5.dimOf h.S)).k (size18 (L5.dimOf h.S)).deg ++
      [pDummy Kf ((size18 (L5.dimOf h.S)).lt + 1)]) → J₁}
    {cAt : (size18 (L5.dimOf h.S)).A → J₁}
    (o : ((step18 (L5.dimOf h.S) rd inc wAt cAt).plain.pull f inc').our.par.Out)
    (s7 : Say7 ρ W h K3) (I : InTail h) (hnl : h.S.atK.nl = 2)
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
  obtain ⟨k1, k2⟩ := (forall_block h.S.Lam h.S.NP h.S.cf.lt
    (fun j => W.slot (h.x.scd.sEnd + j) = (endsK h K3 j).value ρ W)).2 s7.endsK
  rcases a with l | ⟨b, t⟩
  · have e := k1 l.val l.isLt
    rw [endsK_lam h K3 l.isLt] at e
    exact end_of _ o (.inl l) _ (Sum.elim m u) (h.x.sKC + l.val) _ (hsK l)
      (keyF_port m A L Tb hnl hrF hr hξ hfn (hG.qKx l.val l.isLt) (I.qKx l.val l.isLt).feat) e
  · have ht : t.val < h.S.cf.lt := by
      have := t.isLt
      have e : (size18 (L5.dimOf h.S)).lt = (L5.dimOf h.S).lT := rfl
      omega
    have e := k2 b.val b.isLt t.val ht
    rw [endsK_bit h K3 b.val ht] at e
    exact end_of _ o (.inr (b, t)) _ (Sum.elim m u) (h.x.sIb h.S b.val t.val) _ (hsB b t)
      (ibitF_port m A L Tb b.isLt hr hξ (hG.hPi b.val b.isLt t.val t.isLt)) e

/-- The bits of the index. -/
theorem bitsF_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4) (fun _ => 3) ++
      [pDummy Kf 2]) → J₁}
    (o : (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain.our.par.Out)
    (s8 : Say8 ρ W h K3) (hr : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4)
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
  have hb : b.val < h.S.NP := b.isLt
  have v1 := s8.ends (2 * b.val) (by omega)
  have v2 := s8.ends (2 * b.val + 1) (by omega)
  unfold endsH at v1 v2
  rw [if_pos (by omega), show 2 * b.val / 2 = b.val by omega] at v1
  rw [if_neg (by omega), show (2 * b.val + 1) / 2 = b.val by omega, Aff.value_sub, Aff.value_ofConst,
    ρ.one, ← v1] at v2
  cases s with
  | false =>
    have e := bitsF_port (K3 := K3) m A L Tb b.isLt hr hξ
      (fun k hk => hG.hR2 b.val b.isLt k (by rw [hlT]; exact hk))
    rw [← v1, (hs b).1] at e
    rw [endF_at]
    show _ = (rA21 (L5.dimOf h.S) Y 4 (ptN _ o) b.val).val (Sum.elim m u)
    exact e
  | true =>
    have sA : (slotF (J₂ := J₂) (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o (b, false)).val
        (Sum.elim m u) = W.slot (h.x.scH.sEnd + 2 * b.val) := by
      unfold Cb.Pv.Att.End.slotF
      rw [val_aSub, val_aConst, val_aSmul, val_aEnt]
      exact (hs b).1.symm
    rw [endF_at]
    show _ = (Cb.Pv.Att.End.aSub
      (slotF (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o (b, false))
      (Cb.Pv.Att.End.aConst 1)).val (Sum.elim m u)
    rw [val_aSub, val_aConst, sA, ← v2]
    exact (hs b).2.symm

end K5Law

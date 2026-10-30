-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/OwnLaidPlans.lean: OwnLaid (Johnson/IMR/OwnLaid.lean) AT THE RECORD AND THE PLANNED
STATE OF EVERY SMALLNESS TEST IN WHAT Verify.publicOf RETURNS: every matrix of kind 0 of a
sub-proof's list has an array of the planned state, at one index of (ix.PK, pkMat) or of (ix.TX,
pxMat), with the rows and columns of its symbols. No scope. Statements and proofs.

  SameL a b         two records agree in what OwnLaid reads: mats · NM · pkMat · pxMat · ix
  RKSame G Fc       Fc has as many arrays as G, each with G's rows and columns · rkSame_trimL
  OwnLaid.of_same
  ownerIs_sameL · borderMeans_sameL · ownerHeld_sameL · ownerPlace_sameL · owners_sameL   the steps behind addTreesF turn none of the five
  planG_ownLaid · seam_ownLaid · planA_ownLaid · planH2_ownLaid   the three plans
  **public_G_ownLaid · public_A_ownLaid · public_H_ownLaid**

THE WALKS ARE THE LIBRARY's, STEP FOR STEP: planG_fromTrees and its fellows (OnBytes/Tie/Pv/Lookup/Ends/FoLayCols.lean), ownerPlaces_sameP and owners_sameP (FoZPublic.lean), borderMeans_sameP and ownerHeld_sameP (FoZMade.lean): there for the relations SameP and KSame, which hold neither the lists of own matrices nor the rows.
What is not claimed. That publicOf returns. Nothing on a matrix of kind 1. No soundness.

-/
import Johnson.IMR.OwnLaid
import OnBytes.Tie.Pv.Lookup.Ends.FoLayCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM.Own

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open Fo.BatRows (bindE_ok ite_ok)

/-- Two records agree in what OwnLaid reads. -/
structure SameL (a b : HTailF2) : Prop where
  mats : b.mats = a.mats
  NM : b.NM = a.NM
  pkMat : b.pkMat = a.pkMat
  pxMat : b.pxMat = a.pxMat
  ix : b.ix = a.ix

theorem SameL.refl (a : HTailF2) : SameL a a := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SameL.trans {a b c : HTailF2} (h : SameL a b) (k : SameL b c) : SameL a c :=
  ⟨k.mats.trans h.mats, k.NM.trans h.NM, k.pkMat.trans h.pkMat, k.pxMat.trans h.pxMat,
    k.ix.trans h.ix⟩

/-- Fc has as many arrays as G, each with G's rows and columns. -/
def RKSame (G Fc : Fork) : Prop :=
  Fc.trees.size = G.trees.size ∧ ∀ t, (Fc.trees.getD t {}).R = (G.trees.getD t {}).R ∧
    (Fc.trees.getD t {}).K = (G.trees.getD t {}).K

theorem RKSame.refl (F : Fork) : RKSame F F := ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem rkSame_trimL (F : Fork) : RKSame F F.trimL := by
  refine ⟨by unfold Fork.trimL; simp, fun t => ?_⟩
  unfold Fork.trimL
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases F.trees[t]? with
  | none => exact ⟨rfl, rfl⟩
  | some X => exact ⟨rfl, rfl⟩

theorem OwnLaid.of_same {tl tlc : HTailF2} {G Fc : Fork} (h : OwnLaid tl G) (hr : SameL tl tlc)
    (hF : RKSame G Fc) : OwnLaid tlc Fc := by
  intro mu hmu hk
  rw [hr.mats, hr.pkMat, hr.pxMat, hr.ix]
  rw [hr.NM] at hmu
  rw [hr.mats] at hk
  obtain ⟨i, t, w, s1, s2, s3⟩ := h mu hmu hk
  exact ⟨i, t, w, by rw [hF.1]; exact s1, by rw [(hF.2 t).1]; exact s2,
    by rw [(hF.2 t).2]; exact s3⟩

/-! ### the steps behind addTreesF -/

theorem ownerIs_sameL (tl : HTailF2) (no : Nat) : SameL tl (tl.ownerIs no) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem borderMeans_sameL {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') : SameL tl tl' := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ownerHeld_sameL {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : SameL tl tl' := by
  unfold Head.ownerHeld at e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hB, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := pureE_ok e
    exact borderMeans_sameL hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

theorem ownerPlace_sameL {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : SameL X.tl X'.tl := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_sameL h1

/-- What the loop keeps. -/
def SameLKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s → ∃ s0, A[i]? = some s0 ∧ SameL s0.tl s.tl

theorem ownerPlaces_sameL (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), SameLKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → SameLKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_sameL G A l out1 r ?_ h
    split at h1
    · rename_i O X hO hX
      obtain ⟨X', h2, h1⟩ := bindE_ok h1
      obtain rfl := Except.ok.inj h1
      intro i s hi
      by_cases hig : i = g
      · subst hig
        obtain ⟨s0, e0, a0⟩ := hk i X hX
        have hlt : i < out.size := by
          obtain ⟨hl, _⟩ := Array.getElem?_eq_some_iff.1 hX
          exact hl
        have e : (out.set! i X')[i]? = some X' := by
          simp [Array.set!, hlt]
        rw [e] at hi
        obtain rfl := Option.some.inj hi
        exact ⟨s0, e0, a0.trans (ownerPlace_sameL h2)⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_sameL {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : SameLKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_sameL G A _ A r (fun i s hi => ⟨s, hi, SameL.refl _⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, SameL.refl _⟩

/-! ### the three plans -/

theorem planG_ownLaid (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : OwnLaid hp.tl hp.Fp := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact (ownLaid_made hS hA).of_same (ownerIs_sameL tl1 g) (rkSame_trimL Fp)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact (ownLaid_made hS hA).of_same ((ownerIs_sameL tl1 g).trans (borderMeans_sameL hB))
        (rkSame_trimL Fp)
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seam_ownLaid {g : Settings} {m : Array TMat} {tau col0F ktO aO nU3 hb hbLine : Nat}
    {s s' : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s)
    (e' : s.plan nU3 hb hbLine = .ok s') (tlc : HTailF2) (hr : SameL s'.tl tlc) :
    OwnLaid tlc s'.Fp := by
  obtain ⟨tl₀, m1, txOf, f, hasU, hS⟩ := seamShape_cut e
  obtain ⟨T, hA⟩ := seamPlan_cut e'
  exact (ownLaid_made hS hA).of_same hr (RKSame.refl _)

theorem planA_ownLaid (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameL P.seam.tl tlc) : OwnLaid tlc P.seam.Fp := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  exact seam_ownLaid h0 h1 tlc hr

theorem planH2_ownLaid (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) (Fc : Fork) (hF : RKSame hp.Fp Fc) :
    OwnLaid hp.tl Fc := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact (ownLaid_made hS hA).of_same (ownerHeld_sameL hO) hF
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **At every layers' plan of what publicOf returns.** -/
theorem public_G_ownLaid (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : OwnLaid hp.tl hp.Fp :=
  planG_ownLaid X.layers g _ hp (public_G h g hp hg)

/-- **At the head's plan.** -/
theorem public_H_ownLaid (h : Verify.publicOf pol KL layout = .ok X) :
    OwnLaid X.H.tl X.H.Fp := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_ownLaid _ _ _ _ _ _ _ H0 h0 _ (rkSame_trimL H0.Fp)

/-- **At every attention's plan.** -/
theorem public_A_ownLaid (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : OwnLaid a.seam.tl a.seam.Fp := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameL k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show OwnLaid s.tl a0.seam.Fp
    rw [f3] at f2
    exact planA_ownLaid _ _ _ a0 m2 s.tl f2
  · simp at e1

end

end IM.Own

#print axioms IM.Own.public_G_ownLaid
#print axioms IM.Own.public_A_ownLaid
#print axioms IM.Own.public_H_ownLaid

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/StaticOfMade.lean: **THE FIELDS `apart` AND `units` OF `StaticOk`
(Law/OkJoin.lean beside this file) AT EVERY MEMBER OF THE PUBLIC PARAMETERS, FROM THE RETURN OF
`Verify.publicOf` ALONE.** One definition and eleven theorems. A corollary, carried as
Law/SortsOfMade.lean carries `sortsB`. No text already in the library turns.
Why. All three routines that lay out a sub-proof's arrays hand `shapeF` the literal list #[false,
false, true, false] for "which vectors": so the map's list U is #[none, none, some 0, none]
(`shapeF_U`, Johnson/Road/K4/Rec/U3Tree.lean), and `uOf tl Fn` IS 0 AT EVERY Fn.
Array 0 is a table with one row and one virtual row (`addTreesF_atU`,
Johnson/Desc/Kinds/Law/AddTreesLooks.lean), and its number is none of the other sorts'
(`oneRowTable_apart`).
  `TwoStatic tl F`: the two fields, the first at every Fn (the field asks it at Fn.tree = 0 | 2
  alone).
  `uOf_zero`; `apartAt_same`: `ApartAt` reads five fields alone. `static_at`: behind the two
  routines, at array 0. `static_made`: **`TwoStatic` at whatever agrees in the five fields and the
  looks.**
  `planG_two`, `seam_two`, `planA_two`, `planH2_two`: at the three routines' returns. (That the
  attention's routine hands over the literal list: `Fo.ZPlan.seamShape_lit`,
  OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean.) `public_G_two`, `public_A_two`, `public_H_two`: **at
  X's own members.**
Limits. Nothing on a structure that a later routine of a run has turned. Nothing on soundness.
At Fn.tree ≠ 2 `uOf` answers 0 by its default (the map's list has `none` there, or no entry): so
`apart` at Fn.tree = 0 and `units` at Fn.tree ≠ 2 say of array 0, the third vector's, what they
say at Fn.tree = 2: they say nothing of a vector of that table's own, since none is laid out.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.SortsOfMade
import Johnson.Desc.First.Link.Law.OkJoin
import Johnson.Road.K4.Rec.U3Tree
import OnBytes.Tie.Pv.Lookup.Ends.FoHasU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (uOf)
open _root_.Fo (SameP SameRec pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan
open VerifiableInference.Desc.Kinds.Head.Law.Plan (addTreesF_atU)

/-- The two fields, the first at every Fn. -/
def TwoStatic (tl : HTailF2) (F : Fork) : Prop :=
  (∀ Fn : HFun, ApartAt tl (uOf tl Fn)) ∧
    ∀ Fn : HFun, unitLook (F.trees.toList.map look) (uOf tl Fn) = true

/-- With the third vector alone, every table's vector's array is number 0. -/
theorem uOf_zero {tl : HTailF2} (hU : tl.ix.U = #[none, none, some 0, none]) (Fn : HFun) :
    uOf tl Fn = 0 := by
  unfold uOf
  rw [hU]
  have h : Fn.tree = 0 ∨ Fn.tree = 1 ∨ Fn.tree = 2 ∨ Fn.tree = 3 ∨ 4 ≤ Fn.tree := by omega
  rcases h with h | h | h | h | h
  · rw [h]
    rfl
  · rw [h]
    rfl
  · rw [h]
    rfl
  · rw [h]
    rfl
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using h)]
    rfl

/-- `ApartAt` reads five fields alone. -/
theorem apartAt_same {a b : HTailF2} (h : SameRec a b) {t : ℕ} (H : ApartAt a t) :
    ApartAt b t := by
  unfold ApartAt HTailF2.zOf at *
  rw [h.ix, h.NM, h.gtTree, h.z1, h.z2]
  exact H

variable {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
  {f : Array T2Foreign} {tau : Nat} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
  {hb hbLine : Nat}

/-- Behind the two routines, at array 0. -/
theorem static_at (hs : tl₀.shapeF m txOf f #[false, false, true, false] tau = .ok tl)
    (ha : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    ApartAt tl 0 ∧ unitLook (G.trees.toList.map look) 0 = true := by
  have hU := OnBytes.Road.K4.Rec.shapeF_U hs
  have h2 : tl.ix.U.getD 2 none = some 0 := by
    rw [hU]
    rfl
  obtain ⟨X, hX, hk, hR, -, hr⟩ := addTreesF_atU ha 2 (by decide) 0 h2
  obtain ⟨a1, a2, a3, a4, a5⟩ := oneRowTable_apart hs ha hX hk hr
  refine ⟨⟨2, by decide, h2, a1, a2, a3, fun k p hp => ?_⟩, ?_⟩
  · unfold HTailF2.zOf at hp
    split at hp
    · exact a4 p hp
    · exact a5 p hp
  · have e : (G.trees.toList.map look)[0]? = some (look X) := by
      rw [List.getElem?_map, Array.getElem?_toList, hX]
      rfl
    unfold unitLook
    rw [e]
    show (X.kind == HKind.table && X.R == 1 && decide (0 < X.rows.size)) = true
    rw [hk, hR, hr]
    rfl

/-- **At whatever agrees in the five fields and the looks.** -/
theorem static_made (hs : tl₀.shapeF m txOf f #[false, false, true, false] tau = .ok tl)
    (ha : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) (tlc : HTailF2)
    (hr : SameP tl' tlc) (Fc : Fork) (hL : Fc.trees.toList.map look = G.trees.toList.map look) :
    TwoStatic tlc Fc := by
  have hP : SameRec tl tlc := ((addTreesF_sameP ha).trans hr).same
  have hU : tlc.ix.U = #[none, none, some 0, none] := by
    rw [hP.ix]
    exact OnBytes.Road.K4.Rec.shapeF_U hs
  obtain ⟨A, B⟩ := static_at hs ha
  refine ⟨fun Fn => ?_, fun Fn => ?_⟩
  · rw [uOf_zero hU]
    exact apartAt_same hP A
  · rw [uOf_zero hU, hL]
    exact B

/-! ## The three routines -/

theorem planG_two (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : TwoStatic hp.tl hp.Fp := by
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
    exact static_made hS hA _ (ownerIs_sameP tl1 g) _ (looks_trimL Fp)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact static_made hS hA _ ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB)) _
        (looks_trimL Fp)
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seam_two {g : Settings} {m : Array TMat} {tau col0F ktO aO nU3 hb hbLine : Nat}
    {s s' : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s)
    (e' : s.plan nU3 hb hbLine = .ok s') (tlc : HTailF2) (hr : SameP s'.tl tlc) :
    TwoStatic tlc s'.Fp := by
  obtain ⟨tl₀, m1, txOf, f, hS⟩ := seamShape_lit e
  obtain ⟨T, hA⟩ := seamPlan_cut e'
  exact static_made hS hA tlc hr s'.Fp rfl

theorem planA_two (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameP P.seam.tl tlc) : TwoStatic tlc P.seam.Fp := by
  obtain ⟨seam0, h0, h1, -⟩ := planA_rows0 settings i cf P e
  exact seam_two h0 h1 tlc hr

theorem planH2_two (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) (Fc : Fork)
    (hL : Fc.trees.toList.map look = hp.Fp.trees.toList.map look) : TwoStatic hp.tl Fc := by
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
    exact static_made hS hA _ (ownerHeld_sameP hO) Fc hL
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ## The public parameters -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_two (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : TwoStatic hp.tl hp.Fp :=
  planG_two X.layers g _ hp (public_G h g hp hg)

theorem public_H_two (h : Verify.publicOf pol KL layout = .ok X) : TwoStatic X.H.tl X.H.Fp := by
  obtain ⟨H0, h0, e⟩ := public_H h
  have k : TwoStatic H0.tl H0.Fp.trimL := planH2_two _ _ _ _ _ _ _ H0 h0 _ (looks_trimL H0.Fp)
  rw [e]
  exact k

theorem public_A_two (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : TwoStatic a.seam.tl a.seam.Fp := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameP k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show TwoStatic s.tl a0.seam.Fp
    rw [f3] at f2
    exact planA_two _ _ _ a0 m2 s.tl f2
  · simp at e1

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.uOf_zero
#print axioms VerifiableInference.Desc.LinkJoin.apartAt_same
#print axioms VerifiableInference.Desc.LinkJoin.static_at
#print axioms VerifiableInference.Desc.LinkJoin.static_made
#print axioms VerifiableInference.Desc.LinkJoin.planG_two
#print axioms VerifiableInference.Desc.LinkJoin.seam_two
#print axioms VerifiableInference.Desc.LinkJoin.planA_two
#print axioms VerifiableInference.Desc.LinkJoin.planH2_two
#print axioms VerifiableInference.Desc.LinkJoin.public_G_two
#print axioms VerifiableInference.Desc.LinkJoin.public_H_two
#print axioms VerifiableInference.Desc.LinkJoin.public_A_two

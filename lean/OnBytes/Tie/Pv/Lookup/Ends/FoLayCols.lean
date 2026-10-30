-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLayCols.lean: at the record and the planned state of every smallness
test in what Verify.publicOf returns, each piece's columns lie inside the array ZZ, and the array
BZ has its columns.

HTailF2.addTreesF (OnBytes/Model/Tail.lean) adds the array ZZ with 2 * mz columns and the array BZ
with bzColumns columns. A piece of call q begins at column q * mz and has mz columns
(Fo.PiecesF.piecesF_pieceOK, OnBytes/Tie/Pv/Lookup/Ends/PiecesFPlaced.lean; piecesF_tail_lay,
OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailLay.lean). So the pieces of both calls lie inside ZZ.

 - t2AddN_K: the array that t2AddN adds has the number of columns that it is given. addTreesF_cols:
   so ZZ has 2 * tl.mz columns and BZ has tl.bzColumns in the state that addTreesF returns.
 - KSame G Fc: Fc's arrays have the numbers of columns of G's. KSame.refl, kSame_trimL.
 - FromTrees tlc Fc: there are runs of HTailF2.shapeF and, on what it returned, of addTreesF, such
   that tlc is what addTreesF returned up to fields that the tests do not read (SameP,
   OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsPlan.lean), and KSame of addTreesF's state and Fc.
   fromTrees_made.
 - planG_fromTrees, seam_fromTrees, planA_fromTrees, planH2_fromTrees; public_G_fromTrees,
   public_A_fromTrees, public_H_fromTrees: FromTrees at the plans' own records and planned states.
   The walks of the routines are those of planG_zMine and its fellows
   (OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean, OnBytes/Tie/Pv/Lookup/Ends/FoZPublic.lean).
 - LayCols tl Fp: for every piece a of tl: a.c0 + a.Cp is at most the number of columns of Fp's
   array ZZ; tl.bzColumns is at most that of Fp's array BZ. of_mem_allPieces. layCols_of: FromTrees
   gives LayCols.
 - public_layColsP: from Verify.publicOf pol KL layout = .ok X: LayCols at (hp.tl, hp.Fp) for every
   member hp of X.G, at (a.seam.tl, a.seam.Fp) for every member a of X.A, and at (X.H.tl, X.H.Fp).

Limits: the states are the planned ones. That a run's later states keep the arrays' numbers of
columns is not laid here. FromTrees's runs stand under an ∃: the two run equations bind what the
runs return; the arguments of the runs are bound by nothing, and FromTrees does not say that they
are the plan's. LayCols speaks of columns alone, not of rows. public_layColsP has no ∃.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that publicOf returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZPlaced1
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTailLay

set_option autoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.DgP OnBytes.Tie.Pv.Tail.Port Fo.Pub
open Fo.BatRows (bindE_ok ite_ok)

/-! ### the arrays' numbers of columns -/

/-- The array that t2AddN adds has the number of columns that it is given. -/
theorem t2AddN_K {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) :
    (F'.trees.getD got {}).K = K := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨e2, _⟩ := Prod.mk.inj e2
    subst e1 e2
    show ((F.trees.push _).getD F.trees.size {}).K = K
    rw [getD_push_last]

/-- The array ZZ has twice mz columns, the array BZ has bzColumns. -/
theorem addTreesF_cols {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    (G.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz ∧ (G.trees.getD tl.ix.BZ {}).K = tl.bzColumns := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨⟨F1, T1⟩, _, h⟩ := bindX h
  obtain ⟨⟨F2, T2⟩, _, h⟩ := bindX h
  obtain ⟨⟨F3, T3⟩, _, h⟩ := bindX h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := bindX h
  obtain ⟨gZ, h⟩ := jpX h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := bindX h
  obtain ⟨gB, h⟩ := jpX h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  obtain ⟨e2, _⟩ := Prod.mk.inj e2
  subst e1 e2
  have K4 : Ext FB F4 := forInX _ (fun s : MProd Fork Tail2 => Ext FB s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
      obtain ⟨_, hs⟩ := jpX hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩)
    _ _ _ (Ext.refl FB) h4
  obtain ⟨z1, z2, z3, z4, z5⟩ := t2AddN_ok hZ
  obtain ⟨b1, b2, b3, b4, b5⟩ := t2AddN_ok hB
  have gZ' : gotZ = tl.ix.ZZ := by simpa using gZ
  have gB' : gotB = tl.ix.BZ := by simpa using gB
  subst gZ'
  have lZ : tl.ix.ZZ < FZ.trees.size := by omega
  have lB : gotB < FB.trees.size := by omega
  have tZ : F4.trees.getD tl.ix.ZZ {} = FZ.trees.getD tl.ix.ZZ {} :=
    (K4.2 _ (Nat.lt_of_lt_of_le lZ b2.1)).trans (b2.2 _ lZ)
  have tB : F4.trees.getD gotB {} = FB.trees.getD gotB {} := K4.2 _ lB
  refine ⟨?_, ?_⟩
  · rw [tZ]
    exact t2AddN_K hZ
  · rw [← gB', tB]
    exact t2AddN_K hB

/-- Fc's arrays have the numbers of columns of G's. -/
def KSame (G Fc : Fork) : Prop := ∀ t, (Fc.trees.getD t {}).K = (G.trees.getD t {}).K

theorem KSame.refl (F : Fork) : KSame F F := fun _ => rfl

theorem kSame_trimL (F : Fork) : KSame F F.trimL := by
  intro t
  unfold Fork.trimL
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases F.trees[t]? with
  | none => rfl
  | some X => rfl

/-! ### where a plan's record and planned state come from -/

/-- Up to fields that the tests on the smallness test's lookup do not read: tlc is what addTreesF
returned on a record that shapeF returned, and Fc has the numbers of columns of addTreesF's state.
-/
def FromTrees (tlc : HTailF2) (Fc : Fork) : Prop :=
  ∃ (tl₀ tl tl' : HTailF2) (m : Array TMat) (txOf : Array (Option Nat)) (f : Array T2Foreign)
    (hasU : Array Bool) (tau : Nat) (F G : Fork) (T T' : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat), tl₀.shapeF m txOf f hasU tau = .ok tl ∧
    tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T') ∧ SameP tl' tlc ∧ KSame G Fc

theorem fromTrees_made {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (hs : tl₀.shapeF m txOf f hasU tau = .ok tl) {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    (tlc : HTailF2) (hr : SameP tl' tlc) (Fc : Fork) (hF : KSame G Fc) : FromTrees tlc Fc :=
  ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr, hF⟩

theorem planG_fromTrees (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : FromTrees hp.tl hp.Fp := by
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
    exact fromTrees_made hS hA _ (ownerIs_sameP tl1 g) _ (kSame_trimL Fp)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact fromTrees_made hS hA _ ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB)) _
        (kSame_trimL Fp)
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seam_fromTrees {g : Settings} {m : Array TMat} {tau col0F ktO aO nU3 hb hbLine : Nat}
    {s s' : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s)
    (e' : s.plan nU3 hb hbLine = .ok s') (tlc : HTailF2) (hr : SameP s'.tl tlc) :
    FromTrees tlc s'.Fp := by
  obtain ⟨tl₀, m1, txOf, f, hasU, hS⟩ := seamShape_cut e
  obtain ⟨T, hA⟩ := seamPlan_cut e'
  exact fromTrees_made hS hA tlc hr s'.Fp (KSame.refl _)

theorem planA_fromTrees (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameP P.seam.tl tlc) : FromTrees tlc P.seam.Fp := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  exact seam_fromTrees h0 h1 tlc hr

theorem planH2_fromTrees (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) (Fc : Fork) (hF : KSame hp.Fp Fc) :
    FromTrees hp.tl Fc := by
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
    exact fromTrees_made hS hA _ (ownerHeld_sameP hO) Fc hF
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_fromTrees (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : FromTrees hp.tl hp.Fp :=
  planG_fromTrees X.layers g _ hp (public_G h g hp hg)

theorem public_H_fromTrees (h : Verify.publicOf pol KL layout = .ok X) :
    FromTrees X.H.tl X.H.Fp := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_fromTrees _ _ _ _ _ _ _ H0 h0 _ (kSame_trimL H0.Fp)

theorem public_A_fromTrees (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : FromTrees a.seam.tl a.seam.Fp := by
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
    show FromTrees s.tl a0.seam.Fp
    rw [f3] at f2
    exact planA_fromTrees _ _ _ a0 m2 s.tl f2
  · simp at e1

end

/-! ### the columns -/

/-- Each piece's columns lie inside the array ZZ; the array BZ has at least bzColumns columns. -/
def LayCols (tl : HTailF2) (Fp : Fork) : Prop :=
  (∀ a ∈ allPieces tl, a.2.c0 + a.2.Cp ≤ (Fp.trees.getD tl.ix.ZZ {}).K) ∧
    tl.bzColumns ≤ (Fp.trees.getD tl.ix.BZ {}).K

theorem of_mem_allPieces {tl : HTailF2} {a : ℕ × Piece} (h : a ∈ allPieces tl) :
    a.1 < 2 ∧ a.2 ∈ piecesL tl a.1 := by
  unfold allPieces at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact ⟨by omega, hp⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact ⟨by omega, hp⟩

theorem layCols_of {tlc : HTailF2} {Fc : Fork} (h : FromTrees tlc Fc) : LayCols tlc Fc := by
  obtain ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr, hF⟩ :=
    h
  obtain ⟨tl0, hp⟩ := shapeF_pieces hs
  have hP : SameP tl tlc := (addTreesF_sameP ha).trans hr
  obtain ⟨kZ, kB⟩ := addTreesF_cols ha
  have hall : allPieces tlc = allPieces tl := by
    unfold allPieces HTailF2.zOf
    rw [hP.same.z1, hP.same.z2]
  have hNC : tl.f9.NC = 2 := by
    obtain ⟨f9, pub, h9, -, he⟩ := piecesF_cut hp
    rw [he]
    exact (Cb.Fo.shape_more h9).2.1
  refine ⟨fun a ha' => ?_, ?_⟩
  · rw [hall] at ha'
    obtain ⟨hq, hm⟩ := of_mem_allPieces ha'
    have c0 := (Fo.PiecesF.piecesF_pieceOK tl0 tl hp a.1 hq a.2 hm).c0
    have cp := ((Fo.PiecesF.piecesF_tail_lay tl0 tl hp).1 a.1 (by rw [hNC]; exact hq) a.2 hm).1
    rw [hP.same.ix, hF, kZ, c0, cp]
    have : a.1 = 0 ∨ a.1 = 1 := by omega
    rcases this with e | e <;> rw [e] <;> omega
  · have eb : tlc.bzColumns = tl.bzColumns := by
      unfold HTailF2.bzColumns
      rw [hP.f9]
    rw [hP.same.ix, hF, kB, eb]

/-- **At the record and planned state of every smallness test in what publicOf returns.** -/
theorem public_layColsP {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → LayCols hp.tl hp.Fp) ∧
    (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → LayCols a.seam.tl a.seam.Fp) ∧
    LayCols X.H.tl X.H.Fp :=
  ⟨fun g hp hg => layCols_of (public_G_fromTrees h g hp hg),
    fun g a hg => layCols_of (public_A_fromTrees h g a hg), layCols_of (public_H_fromTrees h)⟩

end Fo.ZPlan

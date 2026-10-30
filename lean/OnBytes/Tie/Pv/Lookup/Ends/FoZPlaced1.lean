-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean.
The tests on public numbers of the lookup on the digits: nine of the ten clauses of Fo.ZTests from
the success of the verifier's own routines; one test is left.

OnBytes/Tie/Pv/Lookup/Ends/FoZPublic.lean has seven of the ten clauses at every smallness test of
the byte-level verifier's record of public numbers, and leaves three (Fo.ZPlan.Placed3).
OnBytes/Tie/Pv/Lookup/Ends/PiecesFPlaced.lean shows two of the three, pieceTest and apartTest, of
whatever HTailF2.piecesF returns. A plan's record is what piecesF returned but for fields that these
tests do not read (Fo.SameP). So tailTest alone is left.

Main names:
  `pieceTest_same`, `apartTest_same`: the two tests read the fields of Fo.SameP alone.
  `FromPieces tl`: tl is, up to Fo.SameP, what piecesF returned at some record.
  `from_made`; `planG_from`, `planA_from`, `planH2_from`; `public_G_from`, `public_A_from`,
    `public_H_from`: FromPieces of the plans' records, and of the members of X.
  `placed3_of`: FromPieces tl and tailTest tl = true give Fo.ZPlan.Placed3 tl.
  `public_G_zTests1`, `public_A_zTests1`, `public_H_zTests1`: Fo.ZTests at X's own members, under
    tailTest of the member's record alone.
Under: tailTest stays a premise; it is not shown here of any record. By clauses it is the greater
part of the ten: the six clauses of OnBytes.DgP.TailOK (OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean),
the pieces' tiling of the rows among them. In FromPieces the record at which piecesF ran stands
under «there is»: which it is is not said, and nothing here needs it.
The walks of the plans follow OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean's, that of the loop
OnBytes/Tie/Pv/Lookup/Ends/FoZPublic.lean's.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZPublic
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFPlaced

set_option autoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo.Pub
open Fo.BatRows (bindE_ok ite_ok)

theorem pieceTest_same {a b : HTailF2} (h : SameP a b) (q : ℕ) :
    pieceTest b q = pieceTest a q := by
  rw [h.eq]
  rfl

theorem apartTest_same {a b : HTailF2} (h : SameP a b) (q : ℕ) :
    apartTest b q = apartTest a q := by
  rw [h.eq]
  rfl

/-- Up to the fields that the tests do not read: what piecesF returned. -/
def FromPieces (tl : HTailF2) : Prop :=
  ∃ tl0 tlp : HTailF2, tl0.piecesF = .ok tlp ∧ SameP tlp tl

theorem from_made {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (hs : tl₀.shapeF m txOf f hasU tau = .ok tl) {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    {tlc : HTailF2} (hr : SameP tl' tlc) : FromPieces tlc := by
  obtain ⟨tl0, hp⟩ := shapeF_pieces hs
  exact ⟨tl0, tl, hp, (addTreesF_sameP ha).trans hr⟩

theorem FromPieces.same {a b : HTailF2} (h : FromPieces a) (k : SameP a b) : FromPieces b := by
  obtain ⟨tl0, tlp, h1, h2⟩ := h
  exact ⟨tl0, tlp, h1, h2.trans k⟩

/-- With tailTest: the three clauses. -/
theorem placed3_of {tl : HTailF2} (h : FromPieces tl) (t1 : OnBytes.DgP.tailTest tl = true) :
    Placed3 tl := by
  obtain ⟨tl0, tlp, h1, h2⟩ := h
  refine ⟨t1, fun q hq => ?_, fun q hq => ?_⟩
  · rw [pieceTest_same h2]
    exact Fo.PiecesF.piecesF_pieceTest tl0 tlp h1 q hq
  · rw [apartTest_same h2]
    exact Fo.PiecesF.piecesF_apartTest tl0 tlp h1 q hq

/-! ### the three plans -/

theorem planG_from (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : FromPieces hp.tl := by
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
    exact from_made hS hA (ownerIs_sameP tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact from_made hS hA ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem planA_from (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) : FromPieces P.seam.tl := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  obtain ⟨tl₀, m1, txOf, f, hasU, hS⟩ := seamShape_cut h0
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  exact from_made hS hA (SameP.refl _)

theorem planH2_from (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : FromPieces hp.tl := by
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
    exact from_made hS hA (ownerHeld_sameP hO)
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ### the members of X -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_from (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : FromPieces hp.tl :=
  planG_from X.layers g _ hp (public_G h g hp hg)

theorem public_H_from (h : Verify.publicOf pol KL layout = .ok X) : FromPieces X.H.tl := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_from _ _ _ _ _ _ _ H0 h0

theorem public_A_from (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : FromPieces a.seam.tl := by
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
    show FromPieces s.tl
    rw [f3] at f2
    exact (planA_from _ _ _ a0 m2).same f2
  · simp at e1

theorem public_G_zTests1 (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) (t1 : OnBytes.DgP.tailTest hp.tl = true) :
    ZTests hp.tl hp.tl hp.Fp :=
  public_G_zTests h g hp hg (placed3_of (public_G_from h g hp hg) t1)

theorem public_A_zTests1 (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a)
    (t1 : OnBytes.DgP.tailTest a.seam.tl = true) : ZTests a.seam.tl a.seam.tl a.seam.Fp :=
  public_A_zTests h g a hg (placed3_of (public_A_from h g a hg) t1)

theorem public_H_zTests1 (h : Verify.publicOf pol KL layout = .ok X)
    (t1 : OnBytes.DgP.tailTest X.H.tl = true) : ZTests X.H.tl X.H.tl X.H.Fp :=
  public_H_zTests h (placed3_of (public_H_from h) t1)

end

end Fo.ZPlan

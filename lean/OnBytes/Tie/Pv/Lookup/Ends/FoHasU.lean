-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean.
Every link that the verifier lists for its own public part has one of the vectors U1 to U4; so the
frame's links have three moments or more each.

OnBytes/Tie/Pv/Lookup/Ends/FoMomentsLaw.lean shows the test momentsB of the frame's links of a run
of shapesOf under one premise, HasU X: every link of linksOf X default has one of the vectors U1 to
U4. This file shows HasU X of every X that Verify.publicOf returns, from that equation alone. The
planners of the three kinds of sub-proof (Layer.planG, Attention.Seam.shape, Head.planH2) shape the
record of the smallness test with the list #[false, false, true, false]: the third vector alone.
What follows in the plans and in publicOf keeps the record's numbering of arrays (Fo.SameP,
OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsPlan.lean). A link has the record of the plan from which it
is listed. "Has a vector" is said of the numbering (tl.ix.U): nothing is said of a vector's length.

* TlU tl: the record tl has one of the four vectors. TlU.same: Fo.SameP keeps that.
* shapeF_u: what HTailF2.shapeF returns at the list #[false, false, true, false] has one.
* tlU_made; planG_u, seamShape_lit, planA_u, planH2_u: the three plans' records. In seamShape_lit
  the other arguments of shapeF stand under "there are": that one equation binds what is returned,
  and nothing binds the arguments.
* public_G_u, public_A_u, public_H_u: the records of the members of X.
* listLinksH_tl: each link of listLinksH has the record of one of the plans given to it.
* public_hasU: publicOf pol KL layout = .ok X gives HasU X.
* public_moments: with it, ShapesCut X lf links x rl lay gives momentsB rl = true. The walks of the
  three plans and of the members of X follow those of OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean,
  with TlU in the place of FromPieces; the two local tactics are those of
  OnBytes/Tie/Pv/Lookup/Ends/FoTailCore.lean.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that publicOf returns, or that a run of shapesOf does.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZPlaced1
import OnBytes.Tie.Pv.Lookup.Ends.FoMomentsLaw

set_option autoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo.Pub
open Fo.BatRows (bindE_ok ite_ok)

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

/-- The record of a smallness test has one of the vectors U1 to U4. -/
def TlU (tl : HTailF2) : Prop := ∃ u ∈ tl.ix.U.toList.take 4, u.isSome = true

theorem TlU.same {a b : HTailF2} (h : TlU a) (k : SameP a b) : TlU b := by
  have e : b.ix = a.ix := congrArg (·.ix) k.eq
  unfold TlU
  rw [e]
  exact h

/-- A record that is shaped with the third vector alone has it. -/
theorem shapeF_u {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {tau : Nat}
    (e : tl.shapeF m txOf f #[false, false, true, false] tau = .ok tl') : TlU tl' := by
  unfold HTailF2.shapeF at e
  dsimp only at e
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨r2, h2, e⟩ := bindE_ok e
  obtain rfl := Except.ok.inj h2
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  obtain ⟨_, _, _, hi, _⟩ := Fo.PiecesF.piecesF_pieceOK_walk e
  unfold TlU
  rw [hi]
  refine ⟨some 0, ?_, rfl⟩
  show some 0 ∈ List.take 4 (#[none, none, some 0, none] : Array (Option Nat)).toList
  decide

theorem tlU_made {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {tau : Nat}
    (hs : tl₀.shapeF m txOf f #[false, false, true, false] tau = .ok tl) {F G : Fork}
    {T T' : Tail2} {nU aTX : Array Nat} {hb hbLine : Nat}
    (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) {tlc : HTailF2}
    (hr : SameP tl' tlc) : TlU tlc :=
  (shapeF_u hs).same ((addTreesF_sameP ha).trans hr)

/-! ### the three plans -/

theorem planG_u (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : TlU hp.tl := by
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
    exact tlU_made hS hA (ownerIs_sameP tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact tlU_made hS hA ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- A run of Seam.shape, cut, with the list of vectors as the routine writes it. -/
theorem seamShape_lit {g : Settings} {m : Array TMat} {tau col0F ktO aO : Nat}
    {s : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s) :
    ∃ (tl₀ : HTailF2) (m1 : Array TMat) (txOf : Array (Option Nat)) (f : Array T2Foreign),
      tl₀.shapeF m1 txOf f #[false, false, true, false] tau = .ok s.tl := by
  unfold Attention.Seam.shape at e
  dsimp only at e
  alive
  alive
  obtain ⟨tl, hS, e⟩ := bindE_ok e
  cases e
  exact ⟨_, _, _, _, hS⟩

theorem planA_u (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) : TlU P.seam.tl := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  obtain ⟨tl₀, m1, txOf, f, hS⟩ := seamShape_lit h0
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  exact tlU_made hS hA (SameP.refl _)

theorem planH2_u (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : TlU hp.tl := by
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
    exact tlU_made hS hA (ownerHeld_sameP hO)
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ### the members of X -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_u (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : TlU hp.tl :=
  planG_u X.layers g _ hp (public_G h g hp hg)

theorem public_H_u (h : Verify.publicOf pol KL layout = .ok X) : TlU X.H.tl := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_u _ _ _ _ _ _ _ H0 h0

theorem public_A_u (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : TlU a.seam.tl := by
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
    show TlU s.tl
    rw [f3] at f2
    exact (planA_u _ _ _ a0 m2).same f2
  · simp at e1

end

/-! ### the links -/

open OnBytes.Model.Stages in
/-- Each link of the chain has the record of one of the plans that it is listed from. -/
theorem listLinksH_tl {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {links : Array LinkH} (h : listLinksH NGr p4 G A H = .ok links) :
    ∀ Y ∈ links.toList, (∃ s ∈ G.toList, Y.tl = s.tl) ∨ (∃ a ∈ A.toList, Y.tl = a.tl) ∨
      Y.tl = H.tl := by
  unfold listLinksH at h
  dsimp only at h
  replace h := OnBytes.Params.exc_guard h
  obtain ⟨r, hr, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  have push1 : ∀ (q : Array LinkH) (Z : LinkH) (P : LinkH → Prop), (∀ Y ∈ q.toList, P Y) → P Z →
      ∀ Y ∈ (q.push Z).toList, P Y := by
    intro q Z P hq hZ Y hY
    rw [Array.toList_push] at hY
    rcases List.mem_append.1 hY with hY | hY
    · exact hq Y hY
    · obtain rfl : Y = Z := by simpa using hY
      exact hZ
  have I : ∀ Y ∈ r.toList, (∃ s ∈ G.toList, Y.tl = s.tl) ∨ (∃ a ∈ A.toList, Y.tl = a.tl) ∨
      Y.tl = H.tl := by
    refine Fo.ReqF.forIn_mem _
      (fun (q : Array LinkH) => ∀ Y ∈ q.toList, (∃ s ∈ G.toList, Y.tl = s.tl) ∨
        (∃ a ∈ A.toList, Y.tl = a.tl) ∨ Y.tl = H.tl)
      G.toList.zipIdx (fun x hx q q' Iq e => ?_) _ _ _ (fun _ ha => ha)
      (fun Y hY => by cases hY) hr
    have hG : x.1 ∈ G.toList :=
      List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.1
        (show (x.1, x.2) ∈ G.toList.zipIdx from hx))
    have h1 := push1 q (x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true) _ Iq
      (.inl ⟨x.1, hG, rfl⟩)
    split at e
    · split at e
      · rename_i a ha
        obtain ⟨_, _, e⟩ := bindE_ok e
        refine ⟨_, (Except.ok.inj e).symm, push1 _ _ _ h1 (.inr (.inl ⟨a, ?_, rfl⟩))⟩
        exact List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact ha)
      · obtain ⟨_, _, e⟩ := bindE_ok e
        exact ⟨_, (Except.ok.inj e).symm, h1⟩
    · obtain ⟨_, _, e⟩ := bindE_ok e
      exact ⟨_, (Except.ok.inj e).symm, h1⟩
  exact push1 r _ _ I (.inr (.inr rfl))

/-- **Every link that the verifier lists for its own public part has a vector U.** -/
theorem public_hasU {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : Fo.ReqF.HasU X := by
  intro links0 hl Y hY
  unfold Verify.linksOf at hl
  rcases listLinksH_tl hl Y hY with ⟨s, hs, e⟩ | ⟨a, ha, e⟩ | e
  · rw [e]
    obtain ⟨g, hg, rfl⟩ := List.getElem_of_mem hs
    have hg' : g < X.G.size := by simpa using hg
    have es : ((X.G.mapIdx fun g hp =>
        Verify.layersPlanOf X (default : Head.Covered).tokv g hp).toList[g]).tl = (X.G[g]).tl := by
      simp [Verify.layersPlanOf]
    rw [es]
    exact public_G_u h g _ (Array.getElem?_eq_getElem hg')
  · rw [e]
    rw [Array.toList_map] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
    obtain ⟨g, hg, rfl⟩ := List.getElem_of_mem ha0
    have hg' : g < X.A.size := by simpa using hg
    exact public_A_u h g _ (by rw [← Array.getElem?_toList]; exact List.getElem?_eq_getElem hg)
  · rw [e]
    exact public_H_u h

/-- **The frame's links of a run of shapesOf at the verifier's own public part have three moments or
more each.** -/
theorem public_moments {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) {lf : Option ByteArray}
    {links : Array Stages.LinkH} {x : Params.Shapes} {rl : List Params.ReqLink}
    {lay : Params.ReqLayout} (hs : Fo.ShapesCut X lf links x rl lay) :
    TwLaw.momentsB rl = true :=
  Fo.ReqF.shapesCut_moments hs (public_hasU h)

end Fo.ZPlan

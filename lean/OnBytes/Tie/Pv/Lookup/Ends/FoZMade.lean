-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean.
The tests on public numbers of the lookup on the digits: seven of the ten clauses of Fo.ZTests from
the success of the three plans' own routines.

A plan makes the record of its smallness test by HTailF2.shapeF (whose last step is
HTailF2.piecesF), lays the arrays by HTailF2.addTreesF, and then writes into the records of the
arrays' places alone (ownerIs, borderMeans). None of these later steps turns a field that Fo.ZTests
reads of the record (Fo.SameP).

Main names:
  `shapeF_pieces`: what shapeF returns is what piecesF returns at some record.
  `addTreesF_sameP`, `ownerIs_sameP`, `borderMeans_sameP`: Fo.SameP of the later steps.
  `addTreesF_zz`: where addTreesF returns the state G: (G.trees.getD tl.ix.ZZ {}).R = tl.tau.
  `coefTest_of_ok`: Fo.CoefOK as the Bool.
  `ZMine tl Fp`: the clauses t4 to t10 of Fo.ZTests tl tl Fp.
  `zMine_made`: shapeF's and addTreesF's success give ZMine at every record with SameP and every
    state with Frame.
  `zTests_of`: ZMine with the three clauses tailTest, pieceTest, apartTest gives Fo.ZTests.
  `planG_zMine`, `planA_zMine`, `planH2_zMine`: ZMine at the plans' own records and states.
Not here: the three clauses t1, t2, t3 (tailTest, pieceTest, apartTest).
The walk of addTreesF follows OnBytes/Tie/Pv/Lookup/Ends/FoAddTrees.lean's.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZRows
import OnBytes.Tie.Pv.Lookup.Ends.FoLookDigitsPlan
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanSize

set_option autoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Tie.Pv.Tail.Port
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

/-! ### the plans' steps -/

theorem shapeF_pieces {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (e : tl.shapeF m txOf f hasU tau = .ok tl') : ∃ tl0 : HTailF2, tl0.piecesF = .ok tl' := by
  unfold HTailF2.shapeF at e
  dsimp only at e
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  exact ⟨_, e⟩

theorem addTreesF_sameP {tl tl' : HTailF2} {F F' : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    SameP tl tl' := by
  obtain ⟨-, -, e⟩ := addTreesF_fits tl tl' F F' T T' nU aTX hb hbLine h
  rw [e]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem ownerIs_sameP (tl : HTailF2) (no : Nat) : SameP tl (tl.ownerIs no) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem borderMeans_sameP {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') : SameP tl tl' := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem forInX {α σ : Type} (f : α → σ → Except String (ForInStep σ)) (I : σ → Prop)
    (step : ∀ a s s', I s → f a s = .ok s' → ∃ t, s' = .yield t ∧ I t) :
    ∀ (l : List α) (s r : σ), I s → forIn l s f = .ok r → I r
  | [], s, r, hI, h => by
    rw [List.forIn_nil] at h
    have hr : s = r := Except.ok.inj h
    rw [← hr]
    exact hI
  | a :: l, s, r, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := bindX h
    obtain ⟨t, rfl, hI'⟩ := step a s s' hI hs
    exact forInX f I step l t r hI' h

/-- The array ZZ has as many rows as the smallness test has combinations. -/
theorem addTreesF_zz {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    (G.trees.getD tl.ix.ZZ {}).R = tl.tau := by
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
  subst gZ'
  have lZ : tl.ix.ZZ < FZ.trees.size := by omega
  have tZ : F4.trees.getD tl.ix.ZZ {} = FZ.trees.getD tl.ix.ZZ {} :=
    (K4.2 _ (Nat.lt_of_lt_of_le lZ b2.1)).trans (b2.2 _ lZ)
  rw [tZ, z4]

/-! ### the seven clauses -/

theorem coefTest_of_ok {tl : HTailF2} {Fc : Fork} (T : CoefOK tl Fc) : coefTest tl Fc = true := by
  simp only [coefTest, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨T.bz, T.bzR⟩, T.mats⟩, T.apart⟩, T.piece⟩

/-- The clauses t4 to t10 of Fo.ZTests tl tl Fp. -/
structure ZMine (tl : HTailF2) (Fp : Fork) : Prop where
  onRec : ZRec tl
  t9 : coefTest tl Fp = true
  t10 : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fp.trees.getD a.2.tree {}).R

theorem zMine_made {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (hs : tl₀.shapeF m txOf f hasU tau = .ok tl) {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    (tlc : HTailF2) (hr : SameP tl' tlc) (Fc : Fork) (hF : Frame G Fc) : ZMine tlc Fc := by
  obtain ⟨tl0, hp⟩ := shapeF_pieces hs
  have hP : SameP tl tlc := (addTreesF_sameP ha).trans hr
  refine ⟨(zRec_pieces hp).same hP.same.z1 hP.same.z2 hP.f9 hP.lidb,
    coefTest_of_ok (coefOK_behind hs ha tlc hr.same Fc hF), fun a ha' => ?_⟩
  have hall : allPieces tlc = allPieces tl := by
    unfold allPieces HTailF2.zOf
    rw [hP.same.z1, hP.same.z2]
  rw [hall] at ha'
  rw [(pieces_low hp a ha').1, (hF.2 _).1, addTreesF_zz ha]
  exact piecesF_rows hp a ha'

/-- With the three clauses on the pieces' places: all ten. -/
theorem zTests_of {tl : HTailF2} {Fp : Fork} (M : ZMine tl Fp) (t1 : OnBytes.DgP.tailTest tl = true)
    (t2 : ∀ q < 2, pieceTest tl q = true) (t3 : ∀ q < 2, apartTest tl q = true) :
    ZTests tl tl Fp :=
  ⟨t1, t2, t3, M.onRec.t4, M.onRec.t5, M.onRec.t6, M.onRec.t7, M.onRec.t8, M.t9, M.t10⟩

/-! ### the three plans -/

theorem frame_trimL (F : Fork) : Frame F F.trimL :=
  frame_map F _ fun X => ⟨rfl, by simp⟩

theorem frame_refl (F : Fork) : Frame F F := frame_same rfl

theorem planG_zMine (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : ZMine hp.tl hp.Fp := by
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
    exact zMine_made hS hA _ (ownerIs_sameP tl1 g) _ (frame_trimL Fp)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact zMine_made hS hA _ ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB)) _
        (frame_trimL Fp)
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- What Attention.Seam.shape runs. -/
theorem seamShape_cut {g : Settings} {m : Array TMat} {tau col0F ktO aO : Nat}
    {s : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s) :
    ∃ (tl₀ : HTailF2) (m1 : Array TMat) (txOf : Array (Option Nat)) (f : Array T2Foreign)
      (hasU : Array Bool), tl₀.shapeF m1 txOf f hasU tau = .ok s.tl := by
  unfold Attention.Seam.shape at e
  dsimp only at e
  alive
  alive
  obtain ⟨tl, hS, e⟩ := bindE_ok e
  cases e
  exact ⟨_, _, _, _, _, hS⟩

/-- What Attention.Seam.plan runs. -/
theorem seamPlan_cut {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') :
    ∃ T, s.tl.addTreesF {} {} #[0, 0, nU3] #[] hb hbLine = .ok (s'.tl, s'.Fp, T) := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl1, Fp, T⟩, hA, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact ⟨T, hA⟩

theorem seam_zMine {g : Settings} {m : Array TMat} {tau col0F ktO aO nU3 hb hbLine : Nat}
    {s s' : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s)
    (e' : s.plan nU3 hb hbLine = .ok s') (tlc : HTailF2) (hr : SameP s'.tl tlc) :
    ZMine tlc s'.Fp := by
  obtain ⟨tl₀, m1, txOf, f, hasU, hS⟩ := seamShape_cut e
  obtain ⟨T, hA⟩ := seamPlan_cut e'
  exact zMine_made hS hA tlc hr s'.Fp (frame_refl _)

theorem planA_zMine (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameP P.seam.tl tlc) : ZMine tlc P.seam.Fp := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  exact seam_zMine h0 h1 tlc hr

theorem ownerHeld_sameP {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : SameP tl tl' := by
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
    exact borderMeans_sameP hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

theorem planH2_zMine (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) (Fc : Fork) (hF : Frame hp.Fp Fc) :
    ZMine hp.tl Fc := by
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
    exact zMine_made hS hA _ (ownerHeld_sameP hO) Fc hF
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

end Fo.ZPlan

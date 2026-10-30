-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/UnitsAtPlan.lean: THE SMALLNESS TEST: THE PUBLIC TEST `unitsLaid`
(Johnson/Desc/K8/Honest/FallCount.lean) SAYS YES AT THE PLAN OF EVERY FEED-FORWARD SUB-PROOF, AT THE
PLAN's OWN LENGTHS OF THE VECTORS OF READS. A lemma; none of the library's goals. On the routines
that make a plan alone: no state, no prover.

Why. The routine that plans a feed-forward sub-proof (OnBytes/Model/LayerPlan.lean: Layer.planG)
hands the routine of shapes the literal list "the third vector alone", then lays the arrays at its
own list nU, and keeps that list as the plan's field nU; the two routines behind write two lists of
places alone.
  `addTreesF_tabs`   the parts of the vectors that the routine which lays the arrays gives to tables
  `units_made`     behind the two routines, at whatever agrees in the fields that the test reads
  **`planG_units`**   Layer.planG P g O = .ok hp gives unitsLaid hp.nU hp.tl 0 = true
  **`public_G_units`**   so at every member G[g] of the public parameters that Verify.publicOf
      returns
By: shapeF_U (Johnson/Road/K4/Rec/U3Tree.lean) · static_at
(Johnson/Desc/First/Link/Law/StaticOfMade.lean) · addTreesF_record
(OnBytes/Tie/Pv/Tail/EndRuns.lean), whose cut of the routine's text `addTreesF_tabs` repeats for two
more fields. The cut of planG's text is that of planG_two (StaticOfMade.lean).
Limits. Feed-forward sub-proofs alone. Nothing on a value that a later routine of a run has turned.

-/
import Johnson.Desc.K8.Honest.FallCount
import Johnson.Desc.First.Link.Law.StaticOfMade
import OnBytes.Tie.Pv.Tail.EndRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.K8.Honest (unitsLaid)
open VerifiableInference.Desc.LinkJoin (static_at)
open _root_.Fo (SameP SameRec pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan
open OnBytes.Tie.Pv.Tail.Port (ite_throw_ok excBind_ok)

variable {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
  {f : Array T2Foreign} {tau : Nat} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
  {hb hbLine : Nat}

/-- The parts that the routine which lays the arrays gives to tables: none of the first vector; the
whole of the third, if it is there. -/
theorem addTreesF_tabs (tl tl' : HTailF2) (F F' : Fork) (T T' : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat) (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    tl'.tabFirst = #[0, 0] ∧
      tl'.tabLen = #[0, if (tl.ix.U.getD 2 none).isSome then nU.getD 2 0 else 0] := by
  unfold HTailF2.addTreesF at h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨r1, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨r2, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨r3, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨gz, Fz, Tz⟩, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨⟨gb, Fb, Tb⟩, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨r4, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  have e := Except.ok.inj h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, _, _⟩ := e
  exact ⟨rfl, rfl⟩

/-- Behind the routine of shapes at "the third vector alone" and the routine that lays the arrays at
nU: the test says yes at nU, at array 0, at whatever agrees in the fields that it reads. -/
theorem units_made (hs : tl₀.shapeF m txOf f #[false, false, true, false] tau = .ok tl)
    (ha : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) (tlc : HTailF2)
    (hr : SameP tl' tlc) (h1 : tlc.tabFirst = tl'.tabFirst) (h2 : tlc.tabLen = tl'.tabLen)
    (h3 : tlc.nUF = tl'.nUF) : unitsLaid nU tlc 0 = true := by
  have hP : SameRec tl tlc := ((addTreesF_sameP ha).trans hr).same
  have hU := OnBytes.Road.K4.Rec.shapeF_U hs
  obtain ⟨⟨n0, -, -, aZ, -, aG, -⟩, -⟩ := static_at hs ha
  obtain ⟨t1, t2⟩ := addTreesF_tabs tl tl' {} G {} T' nU aTX hb hbLine ha
  obtain ⟨r1, -, -⟩ := OnBytes.Tie.Pv.Tail.addTreesF_record tl tl' {} G {} T' nU aTX hb hbLine ha
  have e2 : (tl.ix.U.getD 2 none).isSome = true := by
    rw [hU]
    rfl
  rw [if_pos e2] at t2
  simp only [unitsLaid, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    Option.isNone_iff_eq_none, List.all_eq_true, List.mem_range]
  rw [hP.ix, hP.NM, hP.gtTree, h1, h2, h3, t1, t2, r1, hU]
  exact ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, aZ⟩, aG⟩

theorem borderMeans_tabs {a b : HTailF2} {iF ownerNo index : Nat}
    (e : a.borderMeans iF ownerNo index = .ok b) :
    b.tabFirst = a.tabFirst ∧ b.tabLen = a.tabLen ∧ b.nUF = a.nUF := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact ⟨rfl, rfl, rfl⟩

/-- **At the plan of a feed-forward sub-proof.** -/
theorem planG_units (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : unitsLaid hp.nU hp.tl 0 = true := by
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
    exact units_made hS hA _ (ownerIs_sameP tl1 g) rfl rfl rfl
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      obtain ⟨b1, b2, b3⟩ := borderMeans_tabs hB
      exact units_made hS hA _ ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB)) b1 b2 b3
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- **At every feed-forward member of the public parameters.** -/
theorem public_G_units {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : unitsLaid hp.nU hp.tl 0 = true :=
  planG_units X.layers g _ hp (public_G h g hp hg)

end P1K8

#print axioms P1K8.addTreesF_tabs
#print axioms P1K8.units_made
#print axioms P1K8.planG_units
#print axioms P1K8.public_G_units

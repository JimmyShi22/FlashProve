-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TermsAtOf.lean: CONDITIONAL.

Not shown here. That the hypotheses hold anywhere: no example is known. THAT THE HONEST SIDE's TWO
MAKERS, Sides.of AND jobTermsOn, RETURN (hS, hJ); the public facts on the layout (K4Ground): THEY
HOLD AT SHAPES WITH ROUTED EXPERTS AND THE LIBRARY's ELEVEN SWITCHES ALONE (K4Ground.sw), so at
every other shape the statement says nothing; that the plan's layout, group and list of matrices
are the verifier's (hy, hg, hmats); that the honest structure of the forms has the verifier's four
fields (EnvKeys); that the verifier has heard the second token sumcheck (htT); THAT THE JOB's POINT
IS THE VERIFIER's END POINT OF THAT SUMCHECK (hrt) AND THAT THE TWO SIDES HOLD ONE POINT OF THE
LOOKUP (hzx); CellsAre; that the world's entries are the true ones (hW). No property is claimed.

TermsAt (TermsField.lean), BUILT: its fourteen fields from what a hearing's return and the plan
give, with G the test «is not the matrix of the lookup's planes». With it rt_read stands on the
hypotheses named above alone (its own hH and hE are paid from hS, by sides_ends, TermsField.lean);
sc_read and sel_read ask besides that the shape has routed experts, which K4Ground.sw gives.

  sides_fields   what Sides.of lays into the structure that the two jobs share: seven of its twelve
                 fields (not ce, lfc, opens, hh, ends).
  lastOf_size    the last k coordinates of a point are k in number.
  tok_part       the two points at the end point stand in the verifier's list of points.
  termsAt_of     TermsAt.
-/
import Johnson.Road.K4.C.TermsField
import Johnson.Road.K4.C.Below
import Johnson.Road.K4.C.TokAsksOf
import Johnson.Road.K4.W.Ground
import Johnson.Road.FormsKeysAddr
import Johnson.Desc.First.K4.Returns.Pub.PanelsKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Heard Own TableAsk TableAt layTables tableAsks funsOf matIx pointsOf
  callsTS)
open OnBytes.Road.K4 (entryOf entryTrue)
open OnBytes.Road.K4.W (K4Ground)
open OnBytes.Desc.First.K4.RtPub (EnvKeys)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts Sides Job matsOf envOf ztOf jobTermsOn)
open Inst.Model.FFSeg (Dim)

/-- **What Sides.of lays into the structure that the two jobs share.** -/
theorem sides_fields {Q : K4Pub} {w : K4In} {p : Pts} {S : Sides} (h : Sides.of Q w p = some S) :
    S.Q = Q ∧ S.w = w ∧ S.fo = p.fo ∧ envOf Q p = some S.v ∧
      (∃ Z, (lastOf p.fo.zx Q.P.y.h.la).toOption = some Z ∧ S.zlow = Z.extract 0 Q.P.y.ls) ∧
      callsTS Q.P = some S.TS ∧ S.zt = ztOf Q p := by
  unfold Sides.of at h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨TS, hTS, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Z, hZ, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cls, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hw, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨opens, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨gt, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ends, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  exact ⟨rfl, rfl, rfl, hv, ⟨Z, hZ, rfl⟩, hTS, rfl⟩

/-- The last k coordinates of a point are k in number. -/
theorem lastOf_size {z Z : Array E} {k : ℕ} (h : (lastOf z k).toOption = some Z) : Z.size = k := by
  obtain ⟨hk, rfl⟩ := lastOf_ok (ok_of_toOption h)
  rw [Array.size_extract]
  omega

/-- **The two points at the end point stand in the verifier's list of points.** -/
theorem tok_part {y : Layer.Lay} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf y H hd hd2 = some pts) {tT : Tsc}
    (hT : H.tT = some tT) {Z : Array E} (hZ : (lastOf H.fo.zx y.h.la).toOption = some Z) :
    PtsPart (tokPts (Z.extract 0 y.ls) tT.r) pts := by
  unfold pointsOf at h
  dsimp only at h
  obtain ⟨Z', hZ1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : Z = Z' := Option.some.inj (hZ.symm.trans hZ1)
  rw [hT] at h
  have key : ∃ zv za routed, pts = ([("Z", Z), ("zt", H.ztF), ("Z_V", zv), ("P_V", H.PV),
      ("Z_E", H.ZE), ("r_tV", H.tV.r), ("Z_a", za)] ++
      [("Y", longPoint (Z.extract 0 y.ls) tT.r), ("rt", tT.r)]) ++ routed := by
    cases hd2 with
    | none =>
      obtain ⟨routed, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨zv, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨za, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨zv, za, routed, (Option.some.inj h).symm⟩
    | some o2 =>
      obtain ⟨routed, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨zv, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨za, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨zv, za, routed, (Option.some.inj h).symm⟩
  obtain ⟨zv, za, routed, rfl⟩ := key
  intro n p hp
  by_cases c1 : n = "rt"
  · subst c1
    obtain rfl : ("rt", tT.r) = p := Option.some.inj ((find_rt _ _).symm.trans hp)
    rfl
  · by_cases c2 : n = "Y"
    · subst c2
      obtain rfl : ("Y", longPoint (Z.extract 0 y.ls) tT.r) = p :=
        Option.some.inj ((find_Y _ _).symm.trans hp)
      rfl
    · rw [find_none _ _ c1 c2] at hp
      cases hp

/-- **TermsAt, built.** -/
theorem termsAt_of {hsh : Layer.Shape} {pc : List (List String)}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {o : Own}
    {pts : List (String × Array E)} {D : Dim} {Q : K4Pub} {w : K4In} {p : Pts} {S : Sides}
    {J : Job} {rs : List E} {Mm : Mats Cb.Gl.E} {Wd : World Cb.Gl.E}
    (Gd : K4Ground hsh pc o.v Q.P.rd r tl o.H o.hd o.hd2 pts o.funs D)
    (hS : Sides.of Q w p = some S) (hJ : jobTermsOn S = some J) (hy : Q.P.y = o.v.y)
    (hg : Q.g = o.v.g) (hmats : matsOf Q = matsR o.v.y o.v.g) (K : EnvKeys S.v o.v)
    {tT : Tsc} (htT : o.H.tT = some tT) (hrt : J.cube.pointOf rs = tT.r) (hzx : p.fo.zx = o.H.fo.zx)
    (C : CellsAre Q w Mm) (hW : Wd.entry = entryTrue tl o Mm) :
    TermsAt S J rs Wd r o.H.fo pts tl Mm (· ≠ (matIx Q.P.y).iB) o.funs := by
  obtain ⟨rfl, rfl, -, -, ⟨Z, hZ, hlow⟩, -, -⟩ := sides_fields hS
  have A0 := admitted_of_layout Gd.lay Gd.sw.p3
  have hT : o.v.y.T = 2 ^ o.v.y.h.lt := (laid2_of_layout Gd.lay).T
  have hla : o.v.y.h.la = o.v.y.ls + o.v.y.h.lt := by
    rw [A0.shape]
    exact A0.la
  obtain ⟨H0, tT0, -, hE⟩ := sides_ends hS
  have hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r := by
    rw [hmats, hy, hg]
    exact Gd.tables
  have hf : funsOf S.Q.P.y o.H.fo pts r.2.1 = some o.funs := by
    rw [hy]
    exact Gd.funs
  have hv : S.v.tab = r.1 := K.tab.trans Gd.tab
  have hl' : layTables (matsOf S.Q) (Fo.preAsks S.Q.P.y S.Q.P.rd S.Q.g ++
      Fo.planeAsk S.Q.P.y "b-bits-0" ::
        [Fo.planeAsk S.Q.P.y "b-bits-1", Fo.planeAsk S.Q.P.y "b-pin"]) 0 =
      some (r.1, r.2.1, r.2.2) := hl
  obtain ⟨tB0, hB0, -⟩ := Fo.lay_find (matsOf S.Q) (Fo.planeAsk S.Q.P.y "b-bits-0") rfl _ _ 0 _ _ _
    (fun b hb => Fo.ask_ne hb "b-bits-0" (by decide)) hl'
  have hB : S.v.tabAt "b-bits-0" = some tB0 := by
    unfold Env.tabAt
    rw [hv]
    exact hB0
  have hZ' : (lastOf o.H.fo.zx o.v.y.h.la).toOption = some Z := by
    rw [← hzx, ← hy]
    exact hZ
  exact
    { job := hJ
      laid := hl
      asks := tokAsks_of_readsOf (by rw [hy]; exact Gd.reads)
      y := K.y.trans hy.symm
      T := by rw [K.y]; exact hT
      low := by
        rw [hlow, Array.size_extract, lastOf_size hZ, K.y, hy]
        omega
      tables := hf
      part := by
        rw [hlow, hrt, hy]
        exact tok_part Gd.points htT hZ'
      looks := Or.inl fun _ h => h
      mats := Gd.mats.trans hmats.symm
      NM := Gd.NM
      cells := C
      entry := by
        have e : entryTrue tl o Mm = entryOf Reading.gl tl o.funs o.v.iU3 o.v.K3 Mm := rfl
        rw [hW, e, K.iU3, K.K3]
      off := terms_off hl hf hv hB hE }

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sides_fields
#print axioms OnBytes.Road.K4.C.lastOf_size
#print axioms OnBytes.Road.K4.C.tok_part
#print axioms OnBytes.Road.K4.C.termsAt_of

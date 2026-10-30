-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PointsFields.lean: CONDITIONAL: the named premise `PointsSame`
(Johnson/Desc/K5/Honest/Law/U3Law.lean: two lists of points give every table of an attention
segment the same matrix, run of rows, weights and number of entries) follows from equations
between the fields of the two lists that the tables' weights read.

Main names:
  `unitView k`: of a unit of the scores: the five fields that the tables read: the tile rows'
    weights, the two inner points, the mark "below the diagonal", the sumcheck's point.
  `TableFields p0 p`: the units' views are the same, in order; and eleven fields of the division's
    and the maximum's points are the same: four points and the tile columns' weights, and the
    points of six sumchecks.
  `pointsSame_of_fields`: `TableFields p0 p` gives `PointsSame g lk p0 p`, at every shape's
    numbers g and whatever the lookup hands in.

What is not asked: the planes' inner points (the tables' weights do not read them; the test that
holds them against the lookup's point does, inside the verifier's text); every number of a hidden
value; every form that a sumcheck leaves; the pieces' weights.
Limits. All equations are word for word, not as read in a field: between the honest side's points
and the verifier's they can hold only where the key points are the same words and every one of the
segment's own rounds has been heard. That any two lists of points meet `TableFields` is not shown
here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.U3Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ScoreP)
open K5Law (Table)

/-- Of a unit of the scores, what the tables' weights read: the tile rows' weights, the two inner
points, the mark "below the diagonal", the sumcheck's point. -/
def unitView (k : ScoreP) : Array E × Array E × Array E × Bool × Array E :=
  (k.wI, k.zi, k.zj, k.below, k.sc.r)

/-- The fields of two lists of points that the tables' weights read are the same, word for word.
Whoever shows that the honest side's laying of the challenges yields the verifier's points pays
each clause. -/
structure TableFields (p₀ p : P.Pts) : Prop where
  /-- the units of the scores, in order -/
  scores : p₀.scores.toList.map unitView = p.scores.toList.map unitView
  /-- the division's points -/
  ziW : p₀.d.ziW = p.d.ziW
  zcW : p₀.d.zcW = p.d.zcW
  ziX : p₀.d.ziX = p.d.ziX
  /-- the tile columns' weights of the values' product -/
  wJv : p₀.d.wJv = p.d.wJv
  /-- the points of the division's three sumchecks -/
  scE : p₀.d.scE.r = p.d.scE.r
  vpm : p₀.d.vpm.r = p.d.vpm.r
  vpd : p₀.d.vpd.r = p.d.vpd.r
  /-- the maximum's point and the points of its three sumchecks -/
  ti : p₀.x.ti = p.x.ti
  scF : p₀.x.scF.r = p.x.scF.r
  scd : p₀.x.scd.r = p.x.scd.r
  scH : p₀.x.scH.r = p.x.scH.r

namespace PointsFields

/-- The tile weights of a unit, from its view. -/
def tilesV (g : P.Geo) (below : Bool) (r : Array E) : Array E × Array E :=
  if below then
    P.tileSums g (P.eqTab (r.extract g.lgk (g.lgk + g.lnT - 1)))
      (P.eqTab (r.extract (g.lgk + g.lnT - 1) (g.lgk + 2 * g.lnT - 1)))
  else
    let e := P.eqTab (r.extract g.lgk (g.lgk + g.lnT))
    (e, e)

/-- A unit's two lists of tile weights read the view alone. -/
theorem tiles_view (g : P.Geo) (k : ScoreP) : P.scoreTiles g k = tilesV g k.below k.sc.r := rfl

/-- Lists laid once a unit, where what is laid reads the view alone. -/
theorem flat_view {l₀ l : List ScoreP} (h : l₀.map unitView = l.map unitView)
    (f : Array E × Array E × Array E × Bool × Array E → List Table) :
    (l₀.flatMap fun k => f (unitView k)) = l.flatMap fun k => f (unitView k) := by
  have e : ∀ l : List ScoreP, (l.flatMap fun k => f (unitView k)) = (l.map unitView).flatMap f :=
    fun l => by rw [List.flatMap_map]
  rw [e l₀, e l, h]

end PointsFields

open PointsFields

/-- **Equations between the fields that the tables read give `PointsSame`.** Conditional on
`TableFields`; g and lk are free. -/
theorem pointsSame_of_fields (g : P.Geo) (lk : P.LookIn) {p₀ p : P.Pts} (h : TableFields p₀ p) :
    PointsSame g lk p₀ p := by
  have hM : P.pointM g p₀.d = P.pointM g p.d := by
    unfold P.pointM P.DivP.zilo
    rw [h.vpm, h.ziW]
  have hD : P.pointD g p₀.d = P.pointD g p.d := by
    unfold P.pointD P.DivP.zilo
    rw [h.vpd, h.ziW]
  have hpi : p₀.x.pi g = p.x.pi g := by
    unfold P.MaxP.pi
    rw [h.scd]
  have hpj : p₀.x.pj g = p.x.pj g := by
    unfold P.MaxP.pj
    rw [h.scd]
  have hri2 : p₀.x.ri2 g = p.x.ri2 g := by
    unfold P.MaxP.ri2
    rw [h.scH]
  have hri : p₀.x.ri g = p.x.ri g := by
    unfold P.MaxP.ri
    rw [h.scF]
  have hrc : p₀.x.rc g = p.x.rc g := by
    unfold P.MaxP.rc
    rw [h.scF]
  have hs1 : (p₀.scores.toList.flatMap fun k : ScoreP =>
        [(⟨g.NAs, g.T, P.tok g k.wI k.zi, g.fillH⟩ : Table)]) =
      p.scores.toList.flatMap fun k : ScoreP =>
        [(⟨g.NAs, g.T, P.tok g k.wI k.zi, g.fillH⟩ : Table)] :=
    flat_view h.scores fun v => [⟨g.NAs, g.T, P.tok g v.1 v.2.1, g.fillH⟩]
  have hs2 : (p₀.scores.toList.flatMap fun k : ScoreP =>
        [(⟨g.NAs + 3, 2 ^ g.la,
          P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls))
            (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table)] ++
        ([⟨g.NAs + 3, 2 ^ g.la,
          P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls))
            (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩] ++ [])) =
      p.scores.toList.flatMap fun k : ScoreP =>
        [(⟨g.NAs + 3, 2 ^ g.la,
          P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls))
            (P.tok g (P.scoreTiles g k).1 k.zi), g.fillQ * g.T / 2 ^ g.la⟩ : Table)] ++
        ([⟨g.NAs + 3, 2 ^ g.la,
          P.blockRows (P.eqTab (P.lastCoords (P.lastCoords k.sc.r g.ldh) g.ls))
            (P.tok g (P.scoreTiles g k).2 k.zj), g.fillQ * g.T / 2 ^ g.la⟩] ++ []) :=
    flat_view h.scores fun v =>
      [⟨g.NAs + 3, 2 ^ g.la,
        P.blockRows (P.eqTab (P.lastCoords (P.lastCoords v.2.2.2.2 g.ldh) g.ls))
          (P.tok g (tilesV g v.2.2.2.1 v.2.2.2.2).1 v.2.1), g.fillQ * g.T / 2 ^ g.la⟩] ++
      ([⟨g.NAs + 3, 2 ^ g.la,
        P.blockRows (P.eqTab (P.lastCoords (P.lastCoords v.2.2.2.2 g.ldh) g.ls))
          (P.tok g (tilesV g v.2.2.2.1 v.2.2.2.2).2 v.2.2.1), g.fillQ * g.T / 2 ^ g.la⟩] ++ [])
  unfold PointsSame K5Law.laidBy
  rw [hs1, hs2, hM, hD, hpi, hpj, hri2, hri, hrc, h.ziW, h.zcW, h.ziX, h.wJv, h.scE, h.vpm, h.vpd,
    h.ti]

end H2K5.Honest

#print axioms H2K5.Honest.PointsFields.tiles_view
#print axioms H2K5.Honest.PointsFields.flat_view
#print axioms H2K5.Honest.pointsSame_of_fields

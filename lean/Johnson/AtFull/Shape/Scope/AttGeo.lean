-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttGeo.lean: WHAT THE ATTENTION's GEOMETRY HOLDS BESIDE THE CALLS' SHIFTS AND
TABLES, AND THAT THE TEST ON THE TABLES' SHAPES (H2K5.Honest.tabsG) AND THE TABLES' SHAPES
(H2K5.Honest.attFuns) READ NOTHING ELSE: at two plans equal but for what moves.

* stripCG, stripG; geo_strip: the geometry of a stripped shape.
* units_strip, scores_strip, lastHolding_strip, single_strip.
* ptsB_strip, nScores_strip, **tabsG_same**, **attFuns_same**.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Rel
import Johnson.Desc.K5.Honest.Law.TabsChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo CallG geoOf callOf parCOf)
open VerifiableInference.Desc.First.Shape (HeardAll Heard5Sh LedSh)
open H2K5.Honest (tabsG ptsB placeB attFuns longB tabsFitB)
open OnBytes.Tie.Pv.Tail.Closed (attShapes nScores attAsks)

/-- A call of the geometry with no shift and no table. -/
def stripCG (c : CallG) : CallG := { c with sh := 0, tau := none }

/-- The geometry, its calls with no shift and no table. -/
def stripG (g : Geo) : Geo := { g with calls := g.calls.map stripCG }

theorem geo_strip (S : Attention.Shape) : geoOf (stripS S) = stripG (geoOf S) := by
  unfold geoOf stripS stripG
  simp only [Array.map_map]
  rfl

theorem units_strip (g : Geo) (t : P.Tab) (ks : List P.Keys) :
    (stripG g).units t ks = (g.units t ks).map fun u => (u.1, stripCG u.2.1, u.2.2) := by
  unfold Geo.units stripG
  simp only [Array.toList_map, List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  congr 1
  funext x
  show (if x.1.tab == t then (ks.filter fun k => x.1.holds k).map fun k => (x.2, stripCG x.1, k)
      else []) = _
  split
  · simp [List.map_map, Function.comp_def]
  · rfl

theorem scores_strip (g : Geo) : (stripG g).scores = g.scores := by
  unfold Geo.scores
  rw [units_strip, List.map_map]
  rfl

theorem lastHolding_strip (g : Geo) (k : P.Keys) : (stripG g).lastHolding k = g.lastHolding k := by
  unfold Geo.lastHolding stripG
  simp only [Array.toList_map, List.zipIdx_map, List.filter_map, List.getLast?_map,
    Option.map_map]
  rfl

theorem single_strip (g : Geo) (k : P.Keys) : (stripG g).single k = g.single k := by
  unfold Geo.single
  rw [lastHolding_strip]
  cases g.lastHolding k with
  | none => rfl
  | some q =>
    show (do let c ← (stripG g).calls[q]?; pure ((stripG g).unitAt q c k)) =
      (do let c ← g.calls[q]?; pure (g.unitAt q c k))
    have e : (stripG g).calls[q]? = g.calls[q]?.map stripCG := by
      show (g.calls.map stripCG)[q]? = _
      rw [Array.getElem?_map]
    rw [e]
    cases g.calls[q]? with
    | none => rfl
    | some c => rfl

theorem ptsB_strip (g : Geo) (zk : List Nat) (H : Heard5Sh) (L : LedSh) :
    ptsB (stripG g) zk H L = ptsB g zk H L := by
  unfold ptsB
  rw [units_strip, scores_strip, single_strip, single_strip, single_strip, List.length_map]
  rfl

theorem nScores_strip (S : Attention.Shape) : nScores (stripS S) = nScores S := by
  unfold nScores Attention.unitsOf stripS
  simp only [Array.toList_map, List.zipIdx_map, List.flatMap_map, List.length_flatMap]
  congr 2
  funext a
  show (if (a.1.kind == Attention.Table.kfd) = true then
      List.map (fun s => (a.2, stripA a.1, s))
        (List.filter (fun s => a.1.holds s) [Attention.Seg.fm, Attention.Seg.fd]) else []).length = _
  split <;> simp

theorem attAsks_strip (S : Attention.Shape) (k : Nat) : attAsks (stripS S) k = attAsks S k := rfl

theorem attFuns_strip (A : Attention.Plan) : attFuns (stripPlan A) = attFuns A := by
  unfold attFuns attShapes
  show ((OnBytes.Tie.Pv.Tail.Closed.place (attAsks (stripS A.S) (nScores (stripS A.S))) 0).map _) = _
  rw [nScores_strip]
  rfl

theorem attFuns_same {A B : Attention.Plan} (e : stripPlan A = stripPlan B) :
    attFuns A = attFuns B := by
  rw [← attFuns_strip A, e, attFuns_strip]

theorem tabsG_strip (A : Attention.Plan) (H : Heard5Sh) (K : HeardAll) (L : LedSh) :
    tabsG (stripPlan A) H (stripH K) L = tabsG A H K L := by
  unfold tabsG placeB
  have eg : (parCOf (stripPlan A)).geo = stripG (parCOf A).geo := geo_strip A.S
  rw [eg, ptsB_strip]
  show _ = _
  have e1 : nScores (stripPlan A).S = nScores A.S := nScores_strip A.S
  rw [e1]
  rfl

/-- **The test on the tables' shapes at two plans equal but for what moves, and two hearings equal
but for the calls' tables.** -/
theorem tabsG_same {A B : Attention.Plan} (e : stripPlan A = stripPlan B) (H : Heard5Sh)
    {K K' : HeardAll} (eK : stripH K = stripH K') (L : LedSh) :
    tabsG A H K L = tabsG B H K' L := by
  rw [← tabsG_strip A, e, eK, tabsG_strip]

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.tabsG_same
#print axioms Johnson.AtFull.Shape.Scope.attFuns_same

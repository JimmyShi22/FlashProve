-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5FunsSkel.lean: kind K5: THE SKELETON OF THE LIST OF TABLES THAT AN ATTENTION SEGMENT's QUIET STEP LAYS (of each table its matrix, the rows in a block and the first entry in the vector of reads; NOT its weights) IS A TERM OF THE PLAN's SHAPE ALONE: the library's own
attShapes S (nScores S) (OnBytes/Tie/Pv/Tail/ShapesAtt.lean).

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Why. The library has that sentence of its routine in a context (tables_shapes, at the heard number of units). The IOP as written in Lean makes the tables by the kind's own pure text tablesP (Johnson/Desc/First/Att/TablesP.lean), from the points that pointsOf
(Att/Points.lean) makes of what was heard. Here: the same term, at tablesP, with the heard number of units pinned to the plan by pointsOf's own guard; and at the state behind the step.

Main names:
  `lay_place`: tables laid one behind the other (K5Law.layFrom) have the shapes of the library's place.
  `flat_rep`: a list laid once a member is the library's rep.
  `asks_laid`: the placing's list in the text's own order (K5Law.laidBy), weights dropped, IS the library's attAsks S at the number of units.
  `funs_laid`: tablesP g mats nW lk p = some t → t.funs.toList = layFrom 0 (laidBy g lk p) (K5Law.lq_placeAll · fq_placeAll).
  `units_plan`: pointsOf (geoOf S) zk h L = some p → p.scores.size = nScores S (K5Law.points_counts · points_are's field nH · units_old): THE HEARD NUMBER OF UNITS IS THE PLAN's.
  `tablesP_shapes`: **pointsOf … = some p → tablesP (geoOf S) mats nW lk p = some t → shapesOf (tabsBack t).funs = attShapes S (nScores S).**
  `funsSkel_reads`: **readsAtSO A s = .ok s' → ∃ funs, s'.funs? = some funs ∧ shapesOf funs = attShapes A.S (nScores A.S) ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2.**
Is it empty here? Where pointsOf, tablesP or the step refuses nothing is said. No premise but the returns.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsOfIs
import Johnson.Desc.First.Att.Claims.Place
import Johnson.Desc.First.Att.Claims.PtsBridge
import Johnson.Desc.First.Att.Claims.ReadsNextO
import Johnson.Desc.First.Att.Claims.TablesTree
import OnBytes.Tie.Pv.Tail.ShapesAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo LookIn Pts TablesP Heard Left Fun1 geoOf)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf attShapes attAsks asPart nScores place rep)

/-- Tables laid one behind the other have the shapes of the library's `place`. -/
theorem lay_place : ∀ (L : List K5Law.Table) (m : ℕ),
    (K5Law.layFrom m L).map (fun f : Fun1 => (⟨f.mat, f.len, f.start⟩ : Cb.Pv.Tail.Tab)) =
      place (L.map fun t => (t.mat, t.len, t.entries)) m
  | [], _ => rfl
  | t :: L, m => by
    show _ :: (K5Law.layFrom (m + t.entries) L).map _ = _ :: place _ (m + t.entries)
    rw [lay_place L]

/-- A list laid once a member is the library's `rep`. -/
theorem flat_rep {α : Type} (c : List (ℕ × ℕ × ℕ)) : ∀ l : List α, (l.flatMap fun _ => c) = rep l.length c
  | [] => rfl
  | _ :: l => by
    rw [List.flatMap_cons, flat_rep c l]
    rfl

/-- **The placing's list, weights dropped, is the library's list of asks.** -/
theorem asks_laid (S : Attention.Shape) (lk : LookIn) (p : Pts) :
    (K5Law.laidBy (geoOf S) lk p).map (fun t => (t.mat, t.len, t.entries)) = attAsks S p.scores.size := by
  have hA : ∀ w : Array E, ((List.range (geoOf S).NAs).map fun q =>
      (⟨q, 2 ^ (geoOf S).lmS, w, (geoOf S).kAs / (geoOf S).NAs⟩ : K5Law.Table)).map
        (fun t => (t.mat, t.len, t.entries)) = asPart S := by
    intro w
    unfold asPart
    rw [List.map_map, List.map_eq_flatMap]
    rfl
  unfold K5Law.laidBy attAsks
  simp only [List.map_append, hA, List.map_flatMap, List.map_cons, List.map_nil, List.append_nil]
  rw [← Array.length_toList (xs := p.scores), ← flat_rep, ← flat_rep]
  rfl

/-- What tablesP lays, as the placing's list from entry 0 on. -/
theorem funs_laid {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) : t.funs.toList = K5Law.layFrom 0 (K5Law.laidBy g lk p) := by
  unfold P.tablesP at h
  have a : (P.placeAll g mats nW lk p {}).bind (fun y => some y.1) = some t := h
  obtain ⟨y, hy, e⟩ := Option.bind_eq_some_iff.1 a
  obtain rfl := Option.some.inj e
  obtain ⟨_, f, _⟩ := K5Law.lq_placeAll g mats nW lk p {} y.1 y.2 rfl hy
  rw [K5Law.fq_placeAll g mats nW lk p {} y.1 y.2 hy, f]
  rfl

/-- **The heard number of units is the plan's.** -/
theorem units_plan {S : Attention.Shape} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf (geoOf S) zk h L = some p) : p.scores.size = nScores S := by
  rw [(K5Law.points_counts hp).2.2, ← (K5Law.points_are hp).nH]
  unfold P.Geo.scores nScores
  rw [List.length_map]
  have e := congrArg List.length (K5Law.units_old S Attention.Table.kfd [Attention.Seg.fm, Attention.Seg.fd])
  rw [List.length_map] at e
  exact e

/-- **The skeleton of tablesP's list is a term of the plan's shape alone.** -/
theorem tablesP_shapes {S : Attention.Shape} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {t : TablesP} (hp : P.pointsOf (geoOf S) zk h L = some p)
    (ht : P.tablesP (geoOf S) mats nW lk p = some t) :
    shapesOf (tabsBack t).funs = attShapes S (nScores S) := by
  unfold shapesOf attShapes
  rw [show (tabsBack t).funs = t.funs.map funBack from rfl, Array.toList_map, List.map_map, funs_laid ht,
    ← units_plan hp, ← asks_laid S lk p, ← lay_place]
  rfl

/-- **Behind the quiet step: the skeleton of the list that the state bears.** -/
theorem funsSkel_reads (A : Attention.Plan) {s s' : First.S} (h : readsAtSO A s = .ok s') :
    ∃ funs, s'.funs? = some funs ∧ shapesOf funs = attShapes A.S (nScores A.S) ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨a, hh, g, p, t, c, ha, _, _, hp, ht, _, rfl⟩ := K5Law.reads_next_o A s s' h
  unfold P.ptsFrom at hp
  obtain ⟨L, _, hp'⟩ := Option.bind_eq_some_iff.1 hp
  exact ⟨(tabsBack t).funs, rfl, tablesP_shapes hp' ht, K5Law.tabs_tree ht⟩

end H2K5.Door

#print axioms H2K5.Door.lay_place
#print axioms H2K5.Door.flat_rep
#print axioms H2K5.Door.asks_laid
#print axioms H2K5.Door.funs_laid
#print axioms H2K5.Door.units_plan
#print axioms H2K5.Door.tablesP_shapes
#print axioms H2K5.Door.funsSkel_reads

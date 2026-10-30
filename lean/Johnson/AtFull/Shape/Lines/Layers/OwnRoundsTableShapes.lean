-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/OwnRoundsTableShapes.lean: the shapes of the tables that the
hearing of the layers' own rounds leaves, in closed form: a function of the layout, of the lookup's
record's shape and of the plan's placing of the tables. General; nothing is evaluated.

Why. Each family's number of weights comes by the size laws (eqTab_size,
Johnson/Road/FormsKeysEq.lean; blockRows_size, Johnson/Desc/Reads/FoldAll.lean) and not by making
the weights, so no weight need be evaluated. From a return, the last clause of the library's
hear_public says funsOf P.y fo pts laid = some o.funs.

  lookupBitsTableSize, tableFamilySize   the number of weights of a table of the lookup's bits and
                          of a family of tables.
  bitsTable_size, tableFamily_size   these are the sizes of what phiB and phiOf return.
  tableShapesClosedForm   the tables' shapes. laid: the plan's placing of the tables.
  funsOf_shapes           where funsOf returns, the shapes of what it returns are the closed form.
  **hearing_tableShapes** so from a return of the hearing.

Limits. From a return alone: that the hearing returns is not said here. What any of this costs
Lean's kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FunsRel
import OnBytes.Desc.First.K4.HearPublic
import Johnson.Desc.First.K4.Returns.Pub.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Lay Pub HPlan2 Own TableAsk TableAt phiOf funsOf)
open OnBytes.Road (eqTab_size)
open VerifiableInference.Reads (blockRows_size)
open VerifiableInference.Desc.First.Shape

/-- The number of weights of a table of the lookup's bits: z: the size of the point. -/
def lookupBitsTableSize (h : HeardAll) (lm z : Nat) : Nat :=
  2 ^ ((min h.shape.kT z - (h.shape.kT + 5 - lm)) + (min z z - (h.shape.kT + h.shape.cK)))

/-- The number of weights of a family of tables. -/
def tableFamilySize (y : Lay) (h : HeardAll) (a : TableAsk) : Nat :=
  if a.name == "b-bits-0" then lookupBitsTableSize h y.h.lmb h.zb0
  else if a.name == "b-bits-1" then lookupBitsTableSize h y.h.lmb h.zb1
  else if a.name == "b-pin" then 2 ^ y.h.lmb
  else if a.lng then 2 ^ (min y.ls y.h.la - 0) * 2 ^ (min (y.ls + y.h.lt) y.h.la - y.ls)
  else 2 ^ y.h.lt

/-- Where phiB returns, what it returns has the size lookupBitsTableSize. -/
theorem bitsTable_size {fo : Forest.Heard} {lm e : Nat} {phi : Array E}
    (h : Forest.phiB fo lm e = some phi) : phi.size = lookupBitsTableSize (heardAll fo) lm (fo.zb
        e).size := by
  unfold Forest.phiB at h
  dsimp only at h
  split at h
  · obtain rfl := Option.some.inj h
    rw [eqTab_size, Array.size_append, Array.size_extract, Array.size_extract]
    rfl
  · cases h

/-- Where phiOf returns, what it returns has the size tableFamilySize. -/
theorem tableFamily_size {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)} {a : TableAsk}
    {phi : Array E} (h : phiOf y fo pt a = some phi) : phi.size =
        tableFamilySize y (heardAll fo) a := by
  unfold phiOf at h
  unfold tableFamilySize
  by_cases c0 : (a.name == "b-bits-0") = true
  · rw [if_pos c0] at h ⊢
    exact bitsTable_size h
  rw [if_neg c0] at h ⊢
  by_cases c1 : (a.name == "b-bits-1") = true
  · rw [if_pos c1] at h ⊢
    exact bitsTable_size h
  rw [if_neg c1] at h ⊢
  by_cases c2 : (a.name == "b-pin") = true
  · rw [if_pos c2] at h ⊢
    obtain rfl := Option.some.inj h
    unfold Forest.phiP
    rw [Array.size_map, Array.size_range]
  rw [if_neg c2] at h ⊢
  split at h
  · cases h
  · rename_i p _
    by_cases hl : a.lng = true
    · rw [if_pos hl]
      simp only [hl, ↓reduceIte] at h
      by_cases hs : (p.2.size != y.h.la) = true
      · rw [if_pos hs] at h
        cases h
      · rw [if_neg hs] at h
        obtain rfl := Option.some.inj h
        have hs' : p.2.size = y.h.la := by simpa using hs
        unfold longPhi
        rw [blockRows_size, eqTab_size, eqTab_size, Array.size_extract, Array.size_extract, hs']
    · rw [if_neg hl]
      have hl' : a.lng = false := by simpa using hl
      simp only [hl', Bool.false_eq_true, ↓reduceIte] at h
      by_cases hs : (p.2.size != y.h.lt) = true
      · rw [if_pos hs] at h
        cases h
      · rw [if_neg hs] at h
        obtain rfl := Option.some.inj h
        have hs' : p.2.size = y.h.lt := by simpa using hs
        rw [eqTab_size, hs']

/-- **The tables' shapes, in closed form.** laid: the plan's placing of the tables. -/
def tableShapesClosedForm (y : Lay) (h : HeardAll) (laid : List (TableAsk × List (Nat × Nat))) :
    List FunSh :=
  laid.flatMap fun x => x.2.map fun m => FunSh.mk m.1 x.1.L (tableFamilySize y h x.1) 2 m.2

/-- The families one by one: the shapes of what they return are the closed form. -/
theorem tableFamilies_shapes (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E)) :
    ∀ (laid : List (TableAsk × List (Nat × Nat))) (l : List (List HFun)),
    (laid.mapM fun x => (phiOf y fo pt x.1).bind fun phi =>
      some (x.2.map fun m => ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))) =
        some l → l.flatten.map funSh = tableShapesClosedForm y (heardAll fo) laid
  | [], l, h => by
    obtain rfl : [] = l := Option.some.inj h
    rfl
  | x :: laid, l, h => by
    rw [List.mapM_cons] at h
    cases hp : phiOf y fo pt x.1 with
    | none =>
      rw [hp] at h
      cases h
    | some phi =>
      rw [hp] at h
      cases hr : (laid.mapM fun x => (phiOf y fo pt x.1).bind fun phi =>
        some (x.2.map fun m =>
          ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))) with
      | none =>
        have h' := h
        simp only [Option.bind_some, hr] at h'
        cases h'
      | some r =>
        have h' := h
        simp only [Option.bind_some, hr] at h'
        obtain rfl := Option.some.inj h'
        rw [List.flatten_cons, List.map_append, tableFamilies_shapes y fo pt laid r hr,
            List.map_map]
        unfold tableShapesClosedForm
        rw [List.flatMap_cons, ← tableFamily_size hp]
        rfl

/-- Where funsOf returns, the shapes of the tables are the closed form. -/
theorem funsOf_shapes {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {laid : List (TableAsk × List (Nat × Nat))} {fs : Array HFun}
    (h : funsOf y fo pt laid = some fs) : fs.toList.map funSh =
        tableShapesClosedForm y (heardAll fo) laid := by
  unfold funsOf at h
  obtain ⟨l, hl, e⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl : l.flatten.toArray = fs := Option.some.inj e
  exact tableFamilies_shapes y fo pt laid l hl

/-- **From a return of the hearing**, the tables' shapes in closed form. -/
theorem hearing_tableShapes {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape}
    {o : Own} (hh : hearFl P hp g fo F t = some (o, G, u)) :
    ∃ tab laid n, RtPub.tablesAt P g = some (tab, laid, n) ∧
      o.funs.toList.map funSh = tableShapesClosedForm P.y (heardAll fo) laid := by
  obtain ⟨-, -, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, -, -, hl, -, -, -, -, -, -, hf⟩ :=
    hear_public hh
  exact ⟨tab, laid, nU3, hl, funsOf_shapes hf⟩

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.lookupBitsTableSize
#print axioms OnBytes.Desc.First.K4.Rt.tableFamilySize
#print axioms OnBytes.Desc.First.K4.Rt.bitsTable_size
#print axioms OnBytes.Desc.First.K4.Rt.tableFamily_size
#print axioms OnBytes.Desc.First.K4.Rt.tableShapesClosedForm
#print axioms OnBytes.Desc.First.K4.Rt.tableFamilies_shapes
#print axioms OnBytes.Desc.First.K4.Rt.funsOf_shapes
#print axioms OnBytes.Desc.First.K4.Rt.hearing_tableShapes

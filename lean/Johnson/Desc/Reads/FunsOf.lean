-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/FunsOf.lean: the list of tables to which a list of declarations unfolds, made as
a list of the smallness test's own records; and that the equation of Reads/DeclRow.lean holds of it.

All of this file is a tool: it holds for all sizes and declarations, and names no description of the
protocol. It serves toys: letters whose list of tables is as declared, by make.

What is here.
  `funOf x`: the record of one laid table with its weights. Its array holds the weights below the
    run's length, in order.
  `funsOf t ds`: the list of these records for the tables to which ds unfolds at the sizes t.
  `funsAre_funsOf`: `FunsAre t' (funsOf t ds) ds`, at all sizes t' with the rows and columns of t.
  `laid_funsOf`: at a record tl: `TablesAre` at the row's sizes and weights, and the test on
    lengths.
  `funsOf_tree`: every record of the list lies in the third vector.
  `laidOf_funOf`, `funOf_size`, `funOf_weight`: steps.

Of OnBytes/Model/ this file names the records `HTailF2` and `HFun`.

Limits. A list that is made from the declarations has a join that is true by its make: see the
limits of Reads/DeclRow.lean. Nothing is said of a list that a verifier lays. Nothing on soundness.


-/
import Johnson.Desc.Reads.DeclRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 HFun)

/-- The smallness test's record of one laid table with its weights. -/
def funOf (x : Laid × (ℕ → E)) : HFun :=
  { mat := x.1.mat, len := x.1.len, phi := ((List.range x.1.len).map x.2).toArray,
    tree := x.1.tree, start := x.1.start }

/-- The records of the tables to which the declarations unfold, in order. -/
def funsOf (t : TSize) (ds : List (ReadDecl E)) : Array HFun := ((tablesOf t ds).map funOf).toArray

theorem laidOf_funOf (x : Laid × (ℕ → E)) : laidOf (funOf x) = x.1 := rfl

theorem funOf_size (x : Laid × (ℕ → E)) : (funOf x).phi.size = (funOf x).len := by
  show ((List.range x.1.len).map x.2).toArray.size = x.1.len
  simp

theorem funOf_weight (x : Laid × (ℕ → E)) (j : ℕ) (hj : j < x.1.len) :
    (funOf x).phi.getD j zeroE = x.2 j := by
  show (((List.range x.1.len).map x.2).toArray).getD j zeroE = x.2 j
  simp [Array.getD_eq_getD_getElem?, hj]

/-- **The equation on the list holds of the list that is made from the declarations.** -/
theorem funsAre_funsOf (t t' : TSize) (hm : t'.m = t.m) (hk : t'.k = t.k)
    (ds : List (ReadDecl E)) : FunsAre t' (funsOf t ds) ds := by
  have e : tablesOf t' ds = tablesOf t ds := by
    unfold tablesOf
    rw [hm, hk]
  unfold FunsAre
  rw [e]
  refine ⟨?_, fun n Fn x hFn hx => ?_⟩
  · show ((tablesOf t ds).map funOf).map laidOf = _
    rw [List.map_map]
    exact List.map_congr_left fun x _ => laidOf_funOf x
  · have hFn' : ((tablesOf t ds).map funOf)[n]? = some Fn := hFn
    rw [List.getElem?_map, hx, Option.map_some] at hFn'
    obtain rfl := Option.some.inj hFn'
    exact ⟨funOf_size x, fun j hj => funOf_weight x j hj⟩

/-- Every record of the list lies in the third vector. -/
theorem funsOf_tree (t : TSize) (ds : List (ReadDecl E)) :
    ∀ Fn ∈ (funsOf t ds).toList, Fn.tree = 2 := by
  intro Fn h
  have h' : Fn ∈ (tablesOf t ds).map funOf := h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h'
  exact tree_of_tablesOf hx

/-- At a record: the equation at the row's sizes and weights, and the test on lengths. -/
theorem laid_funsOf {K : Type} (tl : HTailF2) (val : E → K) (ds : List (ReadDecl E)) :
    TablesAre (sizeU3 tl (funsOf (OnBytes.Tie.Pv.Tail.sizeOf tl) ds))
        (phiU3 val (funsOf (OnBytes.Tie.Pv.Tail.sizeOf tl) ds)) val ds ∧
      lensB (funsOf (OnBytes.Tie.Pv.Tail.sizeOf tl) ds) = true :=
  tables_of_funs val (funsAre_funsOf _ _ rfl rfl ds)

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.laidOf_funOf
#print axioms VerifiableInference.Reads.funOf_size
#print axioms VerifiableInference.Reads.funOf_weight
#print axioms VerifiableInference.Reads.funsAre_funsOf
#print axioms VerifiableInference.Reads.funsOf_tree
#print axioms VerifiableInference.Reads.laid_funsOf

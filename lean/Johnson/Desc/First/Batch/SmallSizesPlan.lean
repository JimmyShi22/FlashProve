-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/SmallSizesPlan.lean: THE HALF ON SIZES OF THE NAMED TEST ON THE SMALLNESS
TEST's SINGLE EQUATIONS (`smallFits (sizeBox L)`, Johnson/Desc/First/Batch/SmallBehindDraw.lean)
FROM A TEST ON THE PLAN ALONE. Definitions with code, and theorems.

Why. The test a tree reads, of the smallness test's part of the verifier's state, seven fields
(`Ready.seven`, Johnson/Desc/First/K8/Cond.lean) and the number of combinations; of the caller's
tables it reads each one's matrix, rows to an entry, first entry and vector, not its weights. The
seven are the plan's at a state in front of the draw; the number of combinations and the tables'
shapes the draw's own tests hold against the place's numbers.
  `smallFits_seven`: two parts with the same seven fields and number of combinations: one answer.
  `shape4 Fn`: a table's matrix, rows to an entry, first entry, vector. `readsP_all`: a test on all
    reads, as loops. `smallFits_shapes`: two lists of tables with the same shapes: one answer.
  `tablesOf p`: the place's tables (`K8.tabs`), each on the third vector of reads, without weights.
  `sizeBoxOf arrayOf layout`: `sizeBox` off a list of arrays and a layout.
  `smallSizesB arrayOf layout tlP p`: **THE NAMED TEST ON THE PLAN**: the test a tree, at the boxes
    on sizes, at the planned part tlP with the place's number of combinations, at the place's
    tables. It reads no state.
  `sizes_of_plan`: **at a state s from which the draw says yes**: the seven fields are tlP's; the
    closed list is what the claims take (`K8.FunsAre`); every table lies on the third vector; the
    test on the plan says yes at the link's own list of arrays and layout: THEN the half on sizes
    holds at s.
Limits: (1) `smallSizesB` HAS BEEN EVALUATED AT NO PLAN. (2) That the link's list of arrays and its
layout at a reached state are the plan's is not shown here: the test is stated at the state's own
two values. (3) `K8.FunsAre` and the seven fields are premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.SmallBehindDraw
import Johnson.Desc.First.K8.Cond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (readsP)
open VerifiableInference.Desc.First.K8.Ready (seven)

section
variable (B : Nat → Nat → Nat → Bool)

/-- **The test a tree reads seven fields and the number of combinations.** -/
theorem smallFits_seven (tl tlP : HTailF2) (funs : Array HFun) (h7 : seven tl = seven tlP)
    (hτ : tl.tau = tlP.tau) : smallFits B tl funs = smallFits B tlP funs := by
  simp only [seven, Prod.mk.injEq] at h7
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h7
  simp only [smallFits, tieFits, readFits, readsP, HTailF2.zzCol, HTailF2.tabAt, a1, a2, a3, a4,
    a5, a6, a7, hτ]

/-- A table's matrix, rows to an entry, first entry, vector. -/
def shape4 (Fn : HFun) : Nat × Nat × Nat × Nat := (Fn.mat, Fn.len, Fn.start, Fn.tree)

/-- The table of a shape, without weights. -/
def ofShape (x : Nat × Nat × Nat × Nat) : HFun :=
  { mat := x.1, len := x.2.1, start := x.2.2.1, tree := x.2.2.2 }

omit B in
/-- A test on all reads, as loops. -/
theorem readsP_all (g : HFun × Nat → Bool) (tl : HTailF2) (funs : Array HFun) :
    (readsP tl funs).all g =
      (List.range tl.NM).all fun mu => [0, 2].all fun un => funs.toList.all fun Fn =>
        if (Fn.mat == mu && Fn.tree == un) = true then
          (List.range ((tl.mats.getD mu {}).m / Fn.len)).all fun sg => g (Fn, sg)
        else true := by
  unfold readsP
  simp only [List.all_flatMap, apply_ite (fun l : List (HFun × Nat) => l.all g), List.all_map,
    List.all_nil, Function.comp_def]

/-- The reads' half of the test a tree, off the tables' shapes. -/
def readsFitL (tl : HTailF2) (sh : List (Nat × Nat × Nat × Nat)) : Bool :=
  (List.range tl.NM).all fun mu => [0, 2].all fun un => sh.all fun x =>
    if (x.1 == mu && x.2.2.2 == un) = true then
      (List.range ((tl.mats.getD mu {}).m / x.2.1)).all fun sg => readFits B tl (ofShape x, sg)
    else true

theorem reads_by_shapes (tl : HTailF2) (funs : Array HFun) :
    ((readsP tl funs).all fun x => readFits B tl x) = readsFitL B tl (funs.toList.map shape4) := by
  rw [readsP_all]
  unfold readsFitL
  simp only [List.all_map, Function.comp_def]
  rfl

/-- **Two lists of tables with the same shapes: one answer.** -/
theorem smallFits_shapes (tl : HTailF2) (funs funs' : Array HFun)
    (h : funs.toList.map shape4 = funs'.toList.map shape4) :
    smallFits B tl funs = smallFits B tl funs' := by
  unfold smallFits
  rw [reads_by_shapes, reads_by_shapes, h]

end

/-- The place's tables, each on the third vector of reads, without weights. -/
def tablesOf (p : First.K8.Par) : Array HFun :=
  ((First.K8.tabs p).map fun x => ofShape (x.1, x.2.1, x.2.2, 2)).toArray

/-- The closed list has the place's shapes, on the third vector: so it has the shapes of
`tablesOf`. -/
theorem shapes_of_tabs (p : First.K8.Par) (funs : Array HFun)
    (h : (funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)) = First.K8.tabs p)
    (h3 : ∀ Fn ∈ funs.toList, Fn.tree = 2) :
    funs.toList.map shape4 = (tablesOf p).toList.map shape4 := by
  unfold tablesOf
  rw [← h]
  simp only [List.map_map, Function.comp_def]
  refine List.map_congr_left fun Fn hFn => ?_
  show (Fn.mat, Fn.len, Fn.start, Fn.tree) = (Fn.mat, Fn.len, Fn.start, 2)
  rw [h3 Fn hFn]

/-- `sizeBox` off a list of arrays and a layout. -/
def sizeBoxOf (arrayOf : Array (Nat × String)) (layout : Params.ReqLayout) (t R C : Nat) : Bool :=
  match (arrayOf[t]?).bind fun b => reqArray layout b.1 b.2 with
  | some A => decide (R ≤ A.sizeI) && decide (C ≤ A.sizeC)
  | none => false

theorem sizeBox_eq (L : LinkCtx) : sizeBox L = sizeBoxOf L.arrayOf L.check.rows.layout := rfl

/-- **THE NAMED TEST ON THE PLAN.** -/
def smallSizesB (arrayOf : Array (Nat × String)) (layout : Params.ReqLayout) (tlP : HTailF2)
    (p : First.K8.Par) : Bool :=
  smallFits (sizeBoxOf arrayOf layout) { tlP with tau := p.tau } (tablesOf p)

/-- **The half on sizes, at a state from which the draw says yes, from the test on the plan.** -/
theorem sizes_of_plan {Cl : Type} (p : First.K8.Par) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).decide s rs gs = .ok t)
    (L : LinkCtx) (tl tlP : HTailF2) (funs : Array HFun) (ht : s.tl? = some tl)
    (hf : s.funs? = some funs) (hFA : First.K8.FunsAre s) (h3 : ∀ Fn ∈ funs.toList, Fn.tree = 2)
    (h7 : seven tl = seven tlP)
    (hP : smallSizesB L.arrayOf L.check.rows.layout tlP p = true) :
    smallFits (sizeBox L) tl funs = true := by
  obtain ⟨r, rfl⟩ := First.K8.decide_one First.K8.atS p s t rs gs h
  obtain ⟨tl', ht', hc, _, _, _, _, _, hτ, hsh, _⟩ := (First.K8.decide_atS_iff p s t r gs).1 h
  obtain rfl : tl' = tl := Option.some.inj (ht'.symm.trans ht)
  obtain rfl : tl'.funs = funs := Option.some.inj ((hFA tl' ht' hc).symm.trans hf)
  rw [sizeBox_eq, smallFits_shapes _ tl' tl'.funs (tablesOf p) (shapes_of_tabs p tl'.funs hsh h3),
    smallFits_seven _ tl' { tlP with tau := p.tau } (tablesOf p) h7 hτ]
  exact hP

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.smallFits_seven
#print axioms VerifiableInference.Desc.K9.readsP_all
#print axioms VerifiableInference.Desc.K9.reads_by_shapes
#print axioms VerifiableInference.Desc.K9.smallFits_shapes
#print axioms VerifiableInference.Desc.K9.shapes_of_tabs
#print axioms VerifiableInference.Desc.K9.sizeBox_eq
#print axioms VerifiableInference.Desc.K9.sizes_of_plan

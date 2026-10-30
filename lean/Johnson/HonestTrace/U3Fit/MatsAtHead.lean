-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/MatsAtHead.lean

Under the head (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean) the five clauses of "fitsSeg"
(Johnson/HonestTrace/U3Rows.lean) on the public X and a plan's list of matrices ("fitsMats",
Johnson/HonestTrace/U3Fit/ValsGeneral.lean) hold at each of the 25 segments, at the list that stands
in X's own plan of the segment's smallness test. Definitions and theorems. Public data alone.

How. "fitsMats" reads of X the step between the layers' links and six fields of each matrix: name,
kind, aId, ttOff, m, k. In the goals' scope the first four are written values by "PlanMarks"
(Johnson/HonestTrace/PlanMarks.lean), which "planMarks_in_scope"
(Johnson/Goal/HonestTrace/PlanMarksInScope.lean) gives, and aId, m, k by the written shape part
"xShapeFull" (Johnson/G/XShapeLit.lean), which "xShape_in_scope"
(Johnson/Goal/Numbers/MadeInScope.lean) gives.

Main definitions: "matView", "viewsOf": the six fields, of the 25 lists. "ownerBy", "entryBy",
"fitsMatsBy": the clauses typed a second time, over such views. "viewsW": the written views.

Main theorems:
* "fitsMats_of_by" (no head; one way alone): a yes of "fitsMatsBy" at X's own views gives "fitsMats"
  at X's own list. An owner beyond segment 24 has no view: there "fitsMatsBy" says no.
* "views_of_marks" (no head): from "PlanMarks X" and "xShapeOf X = xShapeFull", X's views are
  "viewsW".
* "fitsMats_at_head": "fitsMats G.W seg (tlOf G.W seg).mats = true" at seg below 25.

Limits. The head is a premise: the full size and the format's second hash function alone. Two closed facts,
"fitsMatsW" and its control "fitsMatsW_can_fail", are shown by "decide +kernel", each under
"set_option maxRecDepth 1000000", which raises the elaborator's depth of recursion. Two of the five
clauses compare a list with X's own, in length and in sizes; here the list is X's own, so these two
are idle and the other three carry the statement. An empty list of views passes "fitsMatsBy", and
the zip in "viewsW" stops at the shorter list: so that none of the 25 written lists is empty is not
what "fitsMatsW" states.
Not claimed: anything on the lookup's two clauses ("fitsLook") or on n != 0. That the list which a
maker hands "fitsSeg" is X's own is the caller's to show: Johnson/HonestTrace/U3Fit/HeadAtHead.lean
shows it at segment 24, Johnson/HonestTrace/U3Fit/LayersAtHead.lean at the even segments; at the odd
ones, where attention's maker hands "A.mats", no file of this folder shows it. No property of a
release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.ValsGeneral
import Johnson.Goal.HonestTrace.PlanMarksInScope
import Johnson.HB.LLHARD.PlanInScope
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground)
open ProofFile.Honest.K3 (matsOwn tlOf linkG linkH stepOf ownerOf nameAt matsOwn_length ownerOf_own)
open VerifiableInference.PlanWritten (xShapeOf tailView)
open Johnson.G (xShapeFull)
open P5J (AtMgA TS)

/-! ## 1 The clauses over views -/

/-- Six fields of a matrix of a plan's list: name, kind, aId, ttOff; aId, m, k. -/
abbrev MatView : Type := (String × Nat × Nat × Nat) × (Nat × Nat × Nat)

def matView (M : TMat) : MatView := ((M.name, M.kind, M.aId, M.ttOff), (M.aId, M.m, M.k))

/-- The views of the 25 lists. -/
def viewsOf (X : Verify.Public) : List (List MatView) :=
  (List.range 25).map fun k => (tlOf X k).mats.toList.map matView

/-- "ownerOf" (Johnson/Desc/ProofFile/Honest/K3/WitOwner.lean) over views. step: 2 where attention's
links stand between the layers'. -/
def ownerBy (step : Nat) (vs : List (List MatView)) (seg : Nat) (v : MatView) : Nat × String :=
  if v.1.2.1 == 1 then
    (step * (v.1.2.2.1 / 256 - 1),
      (((vs.getD (step * (v.1.2.2.1 / 256 - 1)) [])[v.1.2.2.1 % 256]?).map (·.1.1)).getD "")
  else (seg, v.1.1)

/-- The clauses at one matrix: its owner's name is not empty; its owner is no later segment; a
borrowed one lies inside its owner's. -/
def entryBy (step : Nat) (vs : List (List MatView)) (seg : Nat) (v : MatView) : Bool :=
  (ownerBy step vs seg v).2 != "" && decide ((ownerBy step vs seg v).1 ≤ seg) &&
    (v.1.2.1 != 1 || (decide (256 ≤ v.1.2.2.1) &&
      match (vs.getD (step * (v.1.2.2.1 / 256 - 1)) [])[v.1.2.2.1 % 256]? with
      | some O => v.2.2.1 == O.2.2.1 && decide (v.1.2.2.2 + v.2.2.2 ≤ O.2.2.2)
      | none => false))

/-- At every matrix of a segment's list. -/
def fitsMatsBy (step : Nat) (vs : List (List MatView)) (seg : Nat) : Bool :=
  (vs.getD seg []).all (entryBy step vs seg)

/-- The views of a segment below 25. -/
theorem views_getD (X : Verify.Public) {k : Nat} (hk : k < 25) :
    (viewsOf X).getD k [] = (tlOf X k).mats.toList.map matView := by
  unfold viewsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- A view that is found is the view of an entry of X's own list. -/
theorem views_get {X : Verify.Public} {k i : Nat} {v : MatView}
    (h : ((viewsOf X).getD k [])[i]? = some v) :
    ∃ O, (tlOf X k).mats[i]? = some O ∧ matView O = v := by
  by_cases hk : k < 25
  · rw [views_getD X hk, List.getElem?_map] at h
    obtain ⟨O, hO, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨O, by rw [← Array.getElem?_toList]; exact hO, e⟩
  · have e : (viewsOf X).getD k [] = [] := by
      unfold viewsOf
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hk)]
      rfl
    rw [e] at h
    cases h

/-- **GENERAL, at one matrix.** -/
theorem entry_of_by (X : Verify.Public) (seg : Nat) (M : TMat)
    (h : entryBy (stepOf X) (viewsOf X) seg (matView M) = true) :
    ((ownerOf X seg M).2 != "") = true ∧ decide ((ownerOf X seg M).1 ≤ seg) = true ∧
      (M.kind != 1 || (decide (256 ≤ M.aId) &&
        match (tlOf X (linkG X (M.aId / 256 - 1))).mats[M.aId % 256]? with
        | some O => M.m == O.m && decide (M.ttOff + M.k ≤ O.k)
        | none => false)) = true := by
  unfold entryBy at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  by_cases hk : M.kind = 1
  · have hb : (M.kind == 1) = true := by rw [hk]; rfl
    have hn : (M.kind != 1) = false := by rw [hk]; rfl
    change (M.kind != 1 || (decide (256 ≤ M.aId) &&
      match ((viewsOf X).getD (stepOf X * (M.aId / 256 - 1)) [])[M.aId % 256]? with
      | some O => M.m == O.2.2.1 && decide (M.ttOff + M.k ≤ O.2.2.2)
      | none => false)) = true at h3
    rw [hn, Bool.false_or, Bool.and_eq_true] at h3
    obtain ⟨h4, h5⟩ := h3
    cases hm : ((viewsOf X).getD (stepOf X * (M.aId / 256 - 1)) [])[M.aId % 256]? with
    | none =>
      rw [hm] at h5
      cases h5
    | some O' =>
      obtain ⟨O, hO, rfl⟩ := views_get hm
      rw [hm] at h5
      have eo : ownerOf X seg M = ownerBy (stepOf X) (viewsOf X) seg (matView M) := by
        unfold ownerOf ownerBy
        change (if (M.kind == 1) = true then _ else _) = (if (M.kind == 1) = true then _ else _)
        rw [if_pos hb, if_pos hb]
        change (_, (nameAt (tlOf X (stepOf X * (M.aId / 256 - 1))).mats (M.aId % 256)).getD "") =
          (_, ((((viewsOf X).getD (stepOf X * (M.aId / 256 - 1)) [])[M.aId % 256]?).map
            (·.1.1)).getD "")
        unfold nameAt
        rw [hm, hO]
        rfl
      rw [eo]
      refine ⟨h1, h2, ?_⟩
      rw [hn, Bool.false_or, Bool.and_eq_true]
      refine ⟨h4, ?_⟩
      change (match (tlOf X (stepOf X * (M.aId / 256 - 1))).mats[M.aId % 256]? with
        | some O => M.m == O.m && decide (M.ttOff + M.k ≤ O.k)
        | none => false) = true
      rw [hO]
      exact h5
  · have hb : (M.kind == 1) = false := by simpa using hk
    have eo : ownerOf X seg M = ownerBy (stepOf X) (viewsOf X) seg (matView M) := by
      rw [ownerOf_own X seg M hk]
      unfold ownerBy
      change _ = (if (M.kind == 1) = true then _ else _)
      rw [hb]
      rfl
    rw [eo]
    refine ⟨h1, h2, ?_⟩
    have hn : (M.kind != 1) = true := by simpa using hk
    rw [hn]
    rfl

/-- **GENERAL, ONE WAY: a yes over X's own views gives "fitsMats" at X's own list.** -/
theorem fitsMats_of_by {X : Verify.Public} {seg : Nat} (hseg : seg < 25)
    (h : fitsMatsBy (stepOf X) (viewsOf X) seg = true) :
    fitsMats X seg (tlOf X seg).mats = true := by
  unfold fitsMatsBy at h
  rw [views_getD X hseg, List.all_map] at h
  have H := fun M hM => entry_of_by X seg M (List.all_eq_true.1 h M hM)
  have c2 : ((matsOwn X seg).all fun m => m.2.1 != "") = true := by
    unfold matsOwn
    rw [List.all_map]
    exact List.all_eq_true.2 fun M hM => (H M hM).1
  have c3 : ((matsOwn X seg).all fun m => decide (m.1 ≤ seg)) = true := by
    unfold matsOwn
    rw [List.all_map]
    exact List.all_eq_true.2 fun M hM => (H M hM).2.1
  have c5 : borrowedFit X seg = true := by
    unfold borrowedFit
    rw [← Array.all_toList]
    exact List.all_eq_true.2 fun M hM => (H M hM).2.2
  unfold fitsMats
  rw [matsOwn_length, c2, c3, c5, beq_self_eq_true, beq_self_eq_true]
  rfl

/-! ## 2 The written views -/

/-- name, kind, aId, ttOff, list by list, as "PlanMarks" has them. -/
def marksW (k : Nat) : List (String × Nat × Nat × Nat) :=
  match Seg.ofNo 12 k with
  | some σ => (MatName.all 3 1 1 4 σ).map (markOf σ)
  | none => []

/-- aId, m, k, list by list, off the written shape part. -/
def sizesW (k : Nat) : List (Nat × Nat × Nat) := ((xShapeFull.1.getD k none).map (·.2.1)).getD []

def viewsW : List (List MatView) := (List.range 25).map fun k => (marksW k).zip (sizesW k)

/-- GENERAL: the two texts of "the structure of a link's smallness test" agree. -/
theorem tlOf_tlAt (X : Verify.Public) (k : Nat) :
    tlOf X k = (VerifiableInference.Desc.First.Look.tlAt X k).getD {} := by
  unfold tlOf VerifiableInference.Desc.First.Look.tlAt linkH stepOf
  dsimp only
  split_ifs <;> rfl

/-- Under the marks the list is the trace's files' "planMats". -/
theorem tlOf_planMats {X : Verify.Public} (M : PlanMarks X) {k : Nat} (hk : k < 25) :
    (tlOf X k).mats = planMats X k := by
  have e1 : stepOf X = 2 := by
    unfold stepOf
    rw [M.p4]
    rfl
  have e2 : linkH X = 24 := by
    unfold linkH
    rw [e1, M.groups]
  unfold tlOf planMats
  rw [e1, e2]
  by_cases h24 : k = 24
  · subst h24
    rfl
  · have a : (k == 24) = false := by simpa using h24
    rw [a, if_neg (by omega : ¬ 24 < k), if_neg h24]
    by_cases h2 : k % 2 = 0
    · have b : (k % 2 == 0) = true := by simpa using h2
      rw [b, if_pos h2]
      rfl
    · have b : (k % 2 == 0) = false := by simpa using h2
      rw [b, if_neg h2]
      rfl

/-- **GENERAL: from the marks and the shape part: X's views are the written ones.** -/
theorem views_of_marks {X : Verify.Public} (M : PlanMarks X) (S : xShapeOf X = xShapeFull) :
    viewsOf X = viewsW := by
  unfold viewsOf viewsW
  refine List.map_congr_left fun k hk => ?_
  have hk : k < 25 := List.mem_range.1 hk
  obtain ⟨σ, hσ⟩ := seg_of_lt hk
  have m1 : (tlOf X k).mats.toList.map (fun M => (M.name, M.kind, M.aId, M.ttOff)) = marksW k := by
    unfold marksW
    rw [hσ, tlOf_planMats M hk]
    exact M.marks k σ hσ
  have m2 : (tlOf X k).mats.toList.map (fun M => (M.aId, M.m, M.k)) = sizesW k := by
    unfold sizesW
    rw [← S, tlOf_tlAt]
    unfold xShapeOf
    dsimp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    show _ = (Option.map (fun x => x.2.1)
      (Option.map tailView (VerifiableInference.Desc.First.Look.tlAt X k))).getD []
    cases VerifiableInference.Desc.First.Look.tlAt X k <;> rfl
  rw [← m1, ← m2, List.zip_map']
  rfl

set_option maxRecDepth 1000000 in
/-- The clauses at the written views, at each of the 25 segments. -/
theorem fitsMatsW : (List.range 25).all (fitsMatsBy 2 viewsW) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Two controls: at the step 1 (the owners' links are then others) · with the views of segment 22, the
owner of the output head's borrowed matrix, struck. (Beside them, evaluated nowhere in this file: at a
segment beyond the 25 the test is empty; so it is asked below 25 alone.) -/
theorem fitsMatsW_can_fail :
    ((List.range 25).all (fitsMatsBy 1 viewsW) || fitsMatsBy 2 (viewsW.set 22 []) 24) = false := by
  decide +kernel

/-! ## 3 Under the head -/

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the marks hold of a blank ground's public X. -/
theorem marks_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : PlanMarks G.W :=
  planMarks_in_scope h.scope h.reads (IM.ground_publicK h.laid.pub hG)

/-- Its views are the written ones. -/
theorem views_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : viewsOf G.W = viewsW := by
  obtain ⟨ls, -, eW, -, -⟩ := IM.blank_ground hG
  refine views_of_marks (marks_at_head h hG) ?_
  rw [eW]
  exact VerifiableInference.PlanWritten.Joined.xShape_in_scope h.scope h.laid.pub
    (VerifiableInference.Desc.K1.pin1_atAll h)

/-- The step is 2. -/
theorem step_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : stepOf G.W = 2 := by
  unfold stepOf
  rw [(marks_at_head h hG).p4]
  rfl

/-- **UNDER THE HEAD: THE FIVE CLAUSES ON X AT EACH OF THE 25 SEGMENTS, at X's own list.** -/
theorem fitsMats_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {seg : Nat} (hseg : seg < 25) :
    fitsMats G.W seg (tlOf G.W seg).mats = true := by
  refine fitsMats_of_by hseg ?_
  rw [step_at_head h hG, views_at_head h hG]
  exact List.all_eq_true.1 fitsMatsW seg (List.mem_range.2 hseg)

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.views_getD
#check @OnBytes.HonestTrace.U3.Fit.views_get
#check @OnBytes.HonestTrace.U3.Fit.entry_of_by
#check @OnBytes.HonestTrace.U3.Fit.fitsMats_of_by
#check @OnBytes.HonestTrace.U3.Fit.tlOf_tlAt
#check @OnBytes.HonestTrace.U3.Fit.tlOf_planMats
#check @OnBytes.HonestTrace.U3.Fit.views_of_marks
#check @OnBytes.HonestTrace.U3.Fit.fitsMatsW
#check @OnBytes.HonestTrace.U3.Fit.fitsMatsW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.marks_at_head
#check @OnBytes.HonestTrace.U3.Fit.views_at_head
#check @OnBytes.HonestTrace.U3.Fit.step_at_head
#check @OnBytes.HonestTrace.U3.Fit.fitsMats_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.views_getD
#print axioms OnBytes.HonestTrace.U3.Fit.views_get
#print axioms OnBytes.HonestTrace.U3.Fit.entry_of_by
#print axioms OnBytes.HonestTrace.U3.Fit.fitsMats_of_by
#print axioms OnBytes.HonestTrace.U3.Fit.tlOf_tlAt
#print axioms OnBytes.HonestTrace.U3.Fit.tlOf_planMats
#print axioms OnBytes.HonestTrace.U3.Fit.views_of_marks
#print axioms OnBytes.HonestTrace.U3.Fit.fitsMatsW
#print axioms OnBytes.HonestTrace.U3.Fit.fitsMatsW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.marks_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.views_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.step_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.fitsMats_at_head

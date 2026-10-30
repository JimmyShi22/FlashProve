-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/PlanMarksInScope.lean

PlanMarks (Johnson/HonestTrace/PlanMarks.lean) for public files in scope, and two comparisons of
idOf and markOf with terms of the library.
This file states no goal.

Main theorems:
* "planMarks_in_scope": if VerifierAndGoals.InScope Z = true, VerifierAndGoals.readFiles Z = .ok pp and publicOf Z.pol
  Z.KL lay = .ok X: PlanMarks X.
* "linkOf_idOf": for a segment σ of a proof with 12 groups: Meaning.linkOf (idOf σ) = σ.no 12
  (linkOf: Johnson/Goal/Meaning/HidOwner.lean).
* "aIdsOk_written": by evaluation in Lean's kernel: aIdsOk xShapeFull = true. aIdsOk V is a test
  with code on a written shape V: at each of the 25 sub-proofs the written identifiers of the
  matrices are, in order, the third parts of markOf at the names of the segment's list. xShapeFull:
  Johnson/G/XShapeLit.lean.
* "aIdsOk_rejects": two negative tests, by evaluation in Lean's kernel: aIdsOk is false at
  xShapeFull with entry 0 taken out, and at xShapeFull with entry 0 replaced by a copy of entry 2.
On the way: "mk4" (the four fields of an entry), "bordersOf_marks", "plan_marks" (the routines
bordersOf and plansG keep the four fields, where every ttOff is 0), "mk4_own", "mk4_xbI" (the four
fields of the entries that tailsOf makes).

Limits. planMarks_in_scope goes by the texts of the routines that make the lists, through the
library's theorems on what publicOf returns (Hd.public_plans, matsAt_att_gid, labAtt_eq, lab_head,
Hd.planH2_label and others). The written shape holds identifiers, rows and columns: name, kind and
ttOff are compared with no written value. xShapeFull is a written value; that xShapeOf X is
xShapeFull is not used here and not shown here. That some public files meet the three premises
together is not shown in this file: at the stored full-size example's files the first two are shown
(premises_met_of_public, Johnson/Goal/HonestTrace/FullInScope.lean, where publicOf's return is a
premise); the check that publicOf returns there which this file knows of is an evaluation (#guard,
Johnson/Goal/Meaning/ScopeRun.lean).

Not claimed: anything on a prover or on what a verifier accepts.

-/
import Johnson.HonestTrace.PlanMarks
import Johnson.Goal.HonestTrace.FromCellsInScope
import Johnson.Goal.Meaning.HidOwner
import Johnson.Goal.Meaning.PlanShapes
import Johnson.HB.LLHARD.TailAtView
import Johnson.G.XShapeLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open Meaning
open VerifiableInference.PlanWritten (XShape)
open Johnson.G (xShapeFull)

/-! ## Two comparisons of idOf and markOf with the library's terms -/

/-- For a segment of a proof with 12 groups the library's linkOf, at idOf of the segment, is the
segment's number. -/
theorem linkOf_idOf {σ : Seg} (hσ : σ.Below 12) : Meaning.linkOf (idOf σ) = σ.no 12 := by
  cases σ with
  | ff g =>
    have hg : g < 12 := hσ
    show Meaning.linkOf (1 + g) = 2 * g
    unfold Meaning.linkOf
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  | att g =>
    show Meaning.linkOf (14 + g) = 2 * g + 1
    unfold Meaning.linkOf
    rw [if_neg (by omega), if_neg (by omega)]
    omega
  | head => rfl

/-- The test: in a written shape V, at each of the 25 sub-proofs, the written identifiers of the
matrices are, in order, markOf's third parts at the names of the segment's list. -/
def aIdsOk (V : XShape) : Bool :=
  (List.range 25).all fun k =>
    match Seg.ofNo 12 k with
    | some σ =>
      (viewTail V k).2.1.map (·.1) == (MatName.all 3 1 1 4 σ).map fun μ => (markOf σ μ).2.2.1
    | none => false

/-- The test accepts the written shape of the full-size example. By evaluation in the kernel. -/
theorem aIdsOk_written : aIdsOk xShapeFull = true := by decide +kernel

/-- Two negative tests: the test rejects the written shape with entry 0 taken out, and the written
shape with entry 0 replaced by a copy of entry 2. By evaluation in the kernel. -/
theorem aIdsOk_rejects : aIdsOk (xShapeFull.1.set 0 none, xShapeFull.2) = false ∧
    aIdsOk (xShapeFull.1.set 0 (xShapeFull.1.getD 2 none), xShapeFull.2) = false := by
  decide +kernel

/-! ## The marks in the plans of the layer sub-proofs -/

section PlanMarksG
open OnBytes.Model (TMat T2Foreign Settings)
open OnBytes.Model.Layer (Pub HPlan2 Scales bordersOf planG plansFrom plansG tailsOf)

/-- The four marks of an entry. -/
def mk4 (M : TMat) : String × ℕ × ℕ × ℕ := (M.name, M.kind, M.aId, M.ttOff)

/-- bordersOf keeps the matrices' order, number and four marks, where every first column is 0. -/
theorem bordersOf_marks {y : Lay} {ms : Array TMat}
    {r : Array TMat × Array (Option ℕ) × Array T2Foreign} (h : bordersOf y ms = .ok r)
    (h0 : ∀ M ∈ ms.toList, M.ttOff = 0) : r.1.toList.map mk4 = ms.toList.map mk4 := by
  unfold bordersOf at h
  obtain ⟨-, h⟩ := ok_of_refuse h
  have e := (Except.ok.inj h).symm
  subst e
  have H : ∀ (l : List (TMat × ℕ)), (∀ x ∈ l, x.1.ttOff = 0) →
      ∀ (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ),
      ((l.foldl (fun (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ) x =>
        if (x.1.kind == 0 && (x.2 == (Model.Layer.matIx y).iXO ||
            (y.h.p4 && x.2 == (Model.Layer.matIx y).iQA))) = true then
          (s.1.push x.1, s.2.1.push (some s.2.2.2), s.2.2.1, s.2.2.2 + 1)
        else if (x.1.kind == 1) = true then
          (s.1.push { x.1 with foreign := some s.2.2.1.size, ttOff := 0 }, s.2.1.push none,
           s.2.2.1.push { name := "PXf" ++ toString s.2.2.1.size, K := x.1.k, a := 2, m := x.1.m,
                          wp := x.1.wp }, s.2.2.2)
        else (s.1.push x.1, s.2.1.push none, s.2.2.1, s.2.2.2)) s).1.toList.map mk4) =
        s.1.toList.map mk4 ++ l.map fun x => mk4 x.1 := by
    intro l
    induction l with
    | nil =>
      intro _ s
      simp
    | cons x l ih =>
      intro hl s
      have hx : x.1.ttOff = 0 := hl x (List.mem_cons_self ..)
      rw [List.foldl_cons, ih fun z hz => hl z (List.mem_cons_of_mem _ hz)]
      split_ifs <;> simp [mk4, hx]
  have h1 := H ms.toList.zipIdx (fun x hx => h0 x.1 (by
    have := List.mem_map_of_mem (f := Prod.fst) hx
    rwa [List.zipIdx_map_fst] at this)) (#[], #[], #[], 0)
  refine Eq.trans h1 ?_
  have h2 : (ms.toList.zipIdx.map fun x => mk4 x.1) = (ms.toList.zipIdx.map (·.1)).map mk4 := by
    rw [List.map_map]
    rfl
  rw [h2, List.zipIdx_map_fst]
  simp

/-- In the plans that plansG returns for the layout y, the list in the plan of group g has the four
marks of the list of tailsOf, in order, where every first column there is 0. -/
theorem plan_marks {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : Model.WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub} (hP : Pub.of y sc rope wsLay V tokv set = .ok P)
    {G : Array HPlan2} (hG : plansG P = .ok G) (g : ℕ) (hp : HPlan2) (hg : G[g]? = some hp)
    (h0 : ∀ M ∈ ((tailsOf y).getD g {}).mats.toList, M.ttOff = 0) :
    hp.tl.mats.toList.map mk4 = ((tailsOf y).getD g {}).mats.toList.map mk4 := by
  unfold Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, -, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  unfold plansG at hG
  obtain ⟨l, hl, hG⟩ := ok_of_bind hG
  have e := (Except.ok.inj hG).symm
  subst e
  have hg' : l[g]? = some hp := by simpa using hg
  obtain ⟨O', hO⟩ := plansFrom_at _ _ 0 none l hl g hp hg'
  rw [Nat.zero_add] at hO
  obtain ⟨b, hb, e⟩ := Hd.planG_mats hO
  rw [e]
  exact bordersOf_marks hb h0

/-- The marks of the matrix that tailsOf makes at a number other than xbI's. -/
theorem mk4_own (y : Lay) (g : ℕ) (x : String × ℕ × ℕ) {n : ℕ} (hn : n ≠ (matIx y).iXI) :
    mk4 (tmatTab y g (x, n)) = (x.1, 0, (1 + g) * 256 + n, 0) := by
  unfold tmatTab mk4
  simp [hn]

/-- The marks of the matrix that tailsOf makes at xbI's number. -/
theorem mk4_xbI (y : Lay) (g : ℕ) (x : String × ℕ × ℕ) :
    mk4 (tmatTab y g (x, (matIx y).iXI)) =
      if g = 0 then (x.1, 0, (1 + g) * 256 + (matIx y).iXI, 0)
      else (x.1, 1, g * 256 + (matIx y).iXO, 0) := by
  unfold tmatTab mk4
  by_cases h0 : g = 0 <;> simp [h0]

end PlanMarksG

/-! ## In scope -/

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- If Z is in the goals' scope, the goals' reader returns pp at Z, and publicOf returns X at Z's
parameter file and scale file: PlanMarks X. -/
theorem planMarks_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : PlanMarks X := by
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨i6, i7, i8⟩ := ix_of_core h C
  have hN : X.hS.NHf = 4 := B.full.NHf
  refine ⟨(Meaning.scope_plans hZ hR h).1, B.groups, fun k σ hσ => ?_⟩
  obtain ⟨hb, hn⟩ := Seg.of_ofNo hσ
  subst hn
  show (planMats X (σ.no 12)).toList.map mk4 = _
  cases σ with
  | ff g =>
    have hg : g < 12 := hb
    show (planMats X (2 * g)).toList.map mk4 = _
    obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
    obtain ⟨P, e⟩ := planG_there h C hg
    have hT : ((Model.Layer.tailsOf X.y).getD g {}).mats =
        ((asksTab X.y).zipIdx.map (tmatTab X.y g)).toArray := by
      rw [tailsOf_eq, getD_range_map _ _ _ _ (by rw [B.groups]; exact hg)]
    have h0 : ∀ M ∈ ((Model.Layer.tailsOf X.y).getD g {}).mats.toList, M.ttOff = 0 := by
      rw [hT]
      intro M hM
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hM
      unfold tmatTab
      dsimp only
      split <;> rfl
    rw [planMats_eq, matsAt_even hg e, plan_marks hP hG g P e h0, hT, marks_ff]
    have L : asksTab X.y = [("af0", X.y.mrow.getD 0 0, X.y.kcol.getD 0 0),
        ("af1", X.y.mrow.getD 0 0, X.y.kcol.getD 0 0),
        ("af2", X.y.mrow.getD 0 0, X.y.kcol.getD 0 0),
        ("ad0", X.y.mrow.getD 1 0, X.y.kcol.getD 1 0),
        ("ar", X.y.mrow.getD 2 0, X.y.kcol.getD 2 0), ("b", 2 ^ X.y.h.lmb, X.y.kbm),
        ("qa", X.y.mrow.getD 3 0, X.y.kcol.getD 3 0), ("xbO", X.y.mxb, X.y.kxb),
        ("xbI", X.y.mxb, X.y.kxb)] := by
      unfold asksTab
      rw [p0, p1]
      rfl
    rw [L]
    have x8 := mk4_xbI X.y g ("xbI", X.y.mxb, X.y.kxb)
    rw [i8, i7] at x8
    show [mk4 (tmatTab X.y g (_, 0)), mk4 (tmatTab X.y g (_, 1)), mk4 (tmatTab X.y g (_, 2)),
      mk4 (tmatTab X.y g (_, 3)), mk4 (tmatTab X.y g (_, 4)), mk4 (tmatTab X.y g (_, 5)),
      mk4 (tmatTab X.y g (_, 6)), mk4 (tmatTab X.y g (_, 7)), mk4 (tmatTab X.y g (_, 8))] = _
    rw [mk4_own X.y g _ (by rw [i8]; decide), mk4_own X.y g _ (by rw [i8]; decide),
      mk4_own X.y g _ (by rw [i8]; decide), mk4_own X.y g _ (by rw [i8]; decide),
      mk4_own X.y g _ (by rw [i8]; decide), mk4_own X.y g _ (by rw [i8]; decide),
      mk4_own X.y g _ (by rw [i8]; decide), mk4_own X.y g _ (by rw [i8]; decide), x8]
  | att g =>
    have hg : g < 12 := hb
    show (planMats X (2 * g + 1)).toList.map mk4 = _
    obtain ⟨i, gi, n1, e⟩ := matsAt_att_gid h C hg
    have hq : i.midQ = (1 + g) * 256 + 6 := by
      have L := labAtt_eq h C hg
      unfold labAtt at L
      obtain ⟨P, hP, L⟩ := Option.bind_eq_some_iff.1 L
      rw [← matsAt_odd hg hP, e, n1] at L
      have e4 : (((Attention.matrices (Hd.shapeA X g) i).map fixed)[1 + 3]?).map
          (fun M => M.aId) = some i.midQ := by
        unfold Attention.matrices
        dsimp only
        rw [n1]
        simp [List.range_succ, fixed]
      rw [e4] at L
      rw [Option.some.inj L]
      unfold labA
      rw [i6, i8, if_neg (by omega)]
    rw [planMats_eq, e, marks_att]
    unfold Attention.matrices
    dsimp only
    rw [n1]
    simp [List.range_succ, mk4, fixed, Attention.ownMatrix, gi, hq]
    decide
  | head =>
    show (planMats X 24).toList.map mk4 = _
    obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
    obtain ⟨stream, -, hm⟩ := Hd.planH2_label hH
    have em : matsAt X 24 =
        Model.Head.matsH X.hS X.HLy (borderOf X.y) (1 + X.y.NGr) stream.aId := by
      rw [matsAt_head, e]
      exact hm
    have hs : stream.aId = 12 * 256 + 7 := by
      have L := lab_head h C (a := 7) (by decide)
      unfold labAt at L
      rw [em] at L
      have e7 : ((Model.Head.matsH X.hS X.HLy (borderOf X.y) (1 + X.y.NGr) stream.aId).getD 7
          {}).aId = stream.aId := by
        unfold Model.Head.matsH
        rw [hN]
        rfl
      rw [e7] at L
      rw [L]
      unfold Hd.labH labA
      rw [hN, if_pos rfl, B.groups, i7, i8, if_neg (by omega)]
    rw [planMats_eq, em, marks_head, hs, B.groups]
    unfold Model.Head.matsH
    rw [hN]
    rfl

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.linkOf_idOf
#print axioms OnBytes.HonestTrace.aIdsOk_written
#print axioms OnBytes.HonestTrace.aIdsOk_rejects
#print axioms OnBytes.HonestTrace.bordersOf_marks
#print axioms OnBytes.HonestTrace.plan_marks
#print axioms OnBytes.HonestTrace.mk4_own
#print axioms OnBytes.HonestTrace.mk4_xbI
#print axioms OnBytes.HonestTrace.planMarks_in_scope

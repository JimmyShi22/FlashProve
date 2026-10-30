-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/XShapeLaws.lean: what a yes and a no of the test on the shape part say
(`xShapeIs`, Johnson/Desc/Ok/PlanWritten/XShapeTest.lean), part by part, so that a user can rewrite
the arguments of its own test and restate nothing.

Statements and proofs.
  `callView_inj`, `forestView_inj`: equal views give equal structures: the views take every field.
  `sameCallV_iff`, `sameCallVs_iff`, `sameForestV_iff`, `sameHeadV_iff`, `sameTailV_iff`,
    `sameTailO_iff`, `sameTails_iff`, `sameXShape_iff`: each comparison says yes just where its two
    arguments are one: no place is left out.
  `xShape_of_is`, `xShapeIs_of`, `xShape_no`: the test says yes just where the projection is the
    written value.
  `tail_of_is`: under a yes, at a segment k < 25: `tailView` of the structure that stands there is
    the written list's entry number k.
  `head_of_is`: under a yes: the seven parts of the head's plan, one equation each: nU, ns,
    funClosed and lidb outright; the two calls and f9 as equations of views.
  `callOfView`, `forestOfView`: the structure of a view. `z1_of_is`, `z2_of_is`, `f9_of_is`: so the
    two calls and f9 are the structures of the written views, whole.   `no_table`: NO PUBLIC TABLE
    STANDS IN THE WRITTEN VALUE: in the two calls and in all calls of f9 the place tau is none. A
    call's table can be made of the parameter file's free numbers; were one in the view, honest
    files with other free numbers would be rejected. By the kernel.
Negative tests, by Lean's kernel (`decide +kernel`): `no_tail`: with one more row in the first
matrix of segment 0 the comparison says no. `no_head`: with one more in ns it says no. `xShape_self`:
the written value passes its own test.

Limits. That the reader's value at any public files passes the test is no theorem. At the full-size
example's three files, as Johnson/G/KitFull.lean holds them, a test by evaluation holds it at every
build (Johnson/G/XShapeLitGuard.lean); at other files it is the reference run's to show.
Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.XShapeTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Model Johnson.G

/-- **Equal views, equal calls.** -/
theorem callView_inj {a b : Call} (h : callView a = callView b) : a = b := by
  cases a
  cases b
  simp only [callView, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have k8 := Option.map_injective (fun _ _ e => Array.toList_inj.1 e) h8
  have k9 := Array.toList_inj.1 h9
  subst h1 h2 h3 h4 h5 h6 h7 k8 k9 h10
  rfl

/-! ## The comparison leaves no place out -/

theorem sameCallV_iff (a b : CallView) : sameCallV a b = true ↔ a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := b
  simp only [sameCallV, Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq, and_assoc]

theorem sameCallVs_iff : ∀ (a b : List CallView), sameCallVs a b = true ↔ a = b
  | [], [] => by simp [sameCallVs]
  | [], _ :: _ => by simp [sameCallVs]
  | _ :: _, [] => by simp [sameCallVs]
  | a :: as, b :: bs => by
    simp only [sameCallVs, Bool.and_eq_true, sameCallV_iff, sameCallVs_iff as bs,
      List.cons.injEq]

theorem sameForestV_iff (a b : ForestView) : sameForestV a b = true ↔ a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := b
  simp only [sameForestV, Bool.and_eq_true, decide_eq_true_eq, sameCallVs_iff, Prod.mk.injEq,
    and_assoc]

theorem sameHeadV_iff (a b : HeadView) : sameHeadV a b = true ↔ a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp only [sameHeadV, Bool.and_eq_true, decide_eq_true_eq, sameCallV_iff, sameForestV_iff,
    Prod.mk.injEq, and_assoc]

theorem sameTailV_iff (a b : TailView) : sameTailV a b = true ↔ a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [sameTailV, Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq, and_assoc]

theorem sameTailO_iff : ∀ (a b : Option TailView), sameTailO a b = true ↔ a = b
  | none, none => by simp [sameTailO]
  | none, some _ => by simp [sameTailO]
  | some _, none => by simp [sameTailO]
  | some a, some b => by simp only [sameTailO, sameTailV_iff, Option.some.injEq]

theorem sameTails_iff : ∀ (a b : List (Option TailView)), sameTails a b = true ↔ a = b
  | [], [] => by simp [sameTails]
  | [], _ :: _ => by simp [sameTails]
  | _ :: _, [] => by simp [sameTails]
  | a :: as, b :: bs => by
    simp only [sameTails, Bool.and_eq_true, sameTailO_iff, sameTails_iff as bs, List.cons.injEq]

/-- **A yes just where the two projections are one.** -/
theorem sameXShape_iff (a b : XShape) : sameXShape a b = true ↔ a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [sameXShape, Bool.and_eq_true, sameTails_iff, sameHeadV_iff, Prod.mk.injEq]

theorem xShape_of_is {X : Verify.Public} (h : xShapeIs X = true) : xShapeOf X = xShapeFull :=
  (sameXShape_iff _ _).1 h

theorem xShapeIs_of {X : Verify.Public} (h : xShapeOf X = xShapeFull) : xShapeIs X = true :=
  (sameXShape_iff _ _).2 h

/-- What a no says. -/
theorem xShape_no {X : Verify.Public} (h : xShapeIs X = false) : xShapeOf X ≠ xShapeFull := by
  intro e
  rw [xShapeIs_of e] at h
  cases h

/-- **At a segment.** -/
theorem tail_of_is {X : Verify.Public} (h : xShapeIs X = true) {k : Nat} (hk : k < 25) :
    xShapeFull.1[k]? = some ((Desc.First.Look.tlAt X k).map tailView) := by
  rw [← xShape_of_is h]
  show ((List.range 25).map fun k => (Desc.First.Look.tlAt X k).map tailView)[k]? = _
  rw [List.getElem?_map, List.getElem?_range hk]
  rfl

/-- **The head's seven parts.** -/
theorem head_of_is {X : Verify.Public} (h : xShapeIs X = true) :
    X.H.nU.toList = xShapeFull.2.1 ∧ X.H.ns = xShapeFull.2.2.1 ∧
      X.H.tl.funClosed = xShapeFull.2.2.2.1 ∧ X.H.tl.lidb = xShapeFull.2.2.2.2.1 ∧
      callView X.H.tl.z1.call = xShapeFull.2.2.2.2.2.1 ∧
      callView X.H.tl.z2.call = xShapeFull.2.2.2.2.2.2.1 ∧
      forestView X.H.tl.f9 = xShapeFull.2.2.2.2.2.2.2 := by
  have e : headView X = xShapeFull.2 := congrArg Prod.snd (xShape_of_is h)
  rw [← e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The call of a view. -/
def callOfView (v : CallView) : Call :=
  { name := v.1, n := v.2.1, iota := v.2.2.1, k := v.2.2.2.1, kappa := v.2.2.2.2.1,
    fn := v.2.2.2.2.2.1, t0 := v.2.2.2.2.2.2.1, tau := v.2.2.2.2.2.2.2.1.map (·.toArray),
    pub := v.2.2.2.2.2.2.2.2.1.toArray, heavy := v.2.2.2.2.2.2.2.2.2 }

theorem callOfView_view (c : Call) : callOfView (callView c) = c := by
  cases c with
  | mk name n iota k kappa fn t0 tau pub heavy =>
    cases tau <;> rfl

/-- The public numbers of a view. -/
def forestOfView (v : ForestView) : Forest.Shape :=
  { calls := (v.1.map callOfView).toArray, dT := v.2.1, kT := v.2.2.1, NT := v.2.2.2.1,
    rK := v.2.2.2.2.1, NC := v.2.2.2.2.2.1, cK := v.2.2.2.2.2.2.1,
    iota := v.2.2.2.2.2.2.2.1.toArray, first := v.2.2.2.2.2.2.2.2.1.toArray,
    callOf := v.2.2.2.2.2.2.2.2.2.1.toArray, pub := v.2.2.2.2.2.2.2.2.2.2.toArray }

theorem forestOfView_view (s : Forest.Shape) : forestOfView (forestView s) = s := by
  cases s with
  | mk calls dT kT NT rK NC cK iota first callOf pub =>
    simp only [forestOfView, forestView, List.map_map]
    congr 1
    have e : (callOfView ∘ callView) = id := funext callOfView_view
    rw [e, List.map_id]

/-- **Equal views, equal public numbers of a lookup.** -/
theorem forestView_inj {a b : Forest.Shape} (h : forestView a = forestView b) : a = b := by
  rw [← forestOfView_view a, h, forestOfView_view]

/-- **The two calls and f9, whole.** -/
theorem z1_of_is {X : Verify.Public} (h : xShapeIs X = true) :
    X.H.tl.z1.call = callOfView xShapeFull.2.2.2.2.2.1 := by
  rw [← (head_of_is h).2.2.2.2.1, callOfView_view]

theorem z2_of_is {X : Verify.Public} (h : xShapeIs X = true) :
    X.H.tl.z2.call = callOfView xShapeFull.2.2.2.2.2.2.1 := by
  rw [← (head_of_is h).2.2.2.2.2.1, callOfView_view]

theorem f9_of_is {X : Verify.Public} (h : xShapeIs X = true) :
    X.H.tl.f9 = forestOfView xShapeFull.2.2.2.2.2.2.2 := by
  rw [← (head_of_is h).2.2.2.2.2.2, forestOfView_view]

/-! ## Negative tests -/

/-- With one more row in the first matrix of segment 0 the comparison says no. -/
theorem no_tail : sameXShape ((xShapeFull.1.modifyHead fun t => t.map fun v =>
    (v.1, v.2.1.modifyHead fun x => (x.1, x.2.1 + 1, x.2.2), v.2.2)), xShapeFull.2)
      xShapeFull = false := by decide +kernel

/-- With one more in ns the comparison says no. -/
theorem no_head : sameXShape
    (xShapeFull.1, xShapeFull.2.1, xShapeFull.2.2.1 + 1, xShapeFull.2.2.2) xShapeFull = false := by
  decide +kernel

/-- **No public table stands in the written value**: in the two calls and in all calls of f9 the
place tau is none: row t has the value t. So nothing made of the free numbers is compared there. -/
theorem no_table : (([xShapeFull.2.2.2.2.2.1, xShapeFull.2.2.2.2.2.2.1] ++
    xShapeFull.2.2.2.2.2.2.2.1).all fun v => v.2.2.2.2.2.2.2.1.isNone) = true := by decide +kernel

/-- The written value passes its own test. -/
theorem xShape_self : sameXShape xShapeFull xShapeFull = true := (sameXShape_iff _ _).2 rfl

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.callView_inj
#print axioms VerifiableInference.PlanWritten.sameCallV_iff
#print axioms VerifiableInference.PlanWritten.sameCallVs_iff
#print axioms VerifiableInference.PlanWritten.sameForestV_iff
#print axioms VerifiableInference.PlanWritten.sameHeadV_iff
#print axioms VerifiableInference.PlanWritten.sameTailV_iff
#print axioms VerifiableInference.PlanWritten.sameTailO_iff
#print axioms VerifiableInference.PlanWritten.sameTails_iff
#print axioms VerifiableInference.PlanWritten.sameXShape_iff
#print axioms VerifiableInference.PlanWritten.xShape_of_is
#print axioms VerifiableInference.PlanWritten.xShapeIs_of
#print axioms VerifiableInference.PlanWritten.xShape_no
#print axioms VerifiableInference.PlanWritten.tail_of_is
#print axioms VerifiableInference.PlanWritten.head_of_is
#print axioms VerifiableInference.PlanWritten.callOfView_view
#print axioms VerifiableInference.PlanWritten.forestOfView_view
#print axioms VerifiableInference.PlanWritten.forestView_inj
#print axioms VerifiableInference.PlanWritten.z1_of_is
#print axioms VerifiableInference.PlanWritten.z2_of_is
#print axioms VerifiableInference.PlanWritten.f9_of_is
#print axioms VerifiableInference.PlanWritten.no_tail
#print axioms VerifiableInference.PlanWritten.no_head
#print axioms VerifiableInference.PlanWritten.no_table
#print axioms VerifiableInference.PlanWritten.xShape_self

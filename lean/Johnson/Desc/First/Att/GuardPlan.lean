-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardPlan.lean: kind K5: FIVE PUBLIC PREMISES OF THE KIND's LAW THAT ARE
THEOREMS where the stored attention plans are the planner's (PlanIs, Att/GuardPublic.lean) and the
proof covers attention: so no test need ask them.

Main names:
  `matsFit_of_plan`: Attention.plan s j cf = .ok X → MatsFit X.S X.seam.tl: the smallness test's
    list of a plan that the planner returns fits the plan's shape. By plan_mats
    (Johnson/Road/Lane5AttLabel.lean), plan_nm (Att/Claims/PlanU3.lean) and the text of
    Attention.matrices.
  `place_att`: where W.p4 holds, the place that lookAt makes at link 2 g + 1 holds the lookup's
    record, packing, calls, padding numbers and cap of the plan W.A[g]:
    lookAt_att (Johnson/Desc/First/Look/K3CallerAtPlan.lean) at that link.
  `p4_of_public`: Verify.publicOf … = .ok X → X.A[g]? = some a → X.p4 = true.
  `guard_theorems`: **PlanIs W, W.p4, W.A[g]? = some a, lookAt W (2 g + 1) false = some x ⊢
    K5Public's "att": shape and planes · "fs" · "mats" · "planes"**, at a and x. By the library's
    lookPubA_plan (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubA.lean), a lemma at the planner's return, and
    the lookups' shape_of_made.
A premise that a theorem gives is none.
Limits. One direction. That W.p4 holds and that PlanIs holds are premises.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GuardPublic
import Johnson.Desc.First.Att.Claims.PlanU3
import Johnson.Desc.First.Att.GeoOf
import Johnson.Desc.First.Look.K3CallerAtPlan
import Johnson.Desc.First.Look.ShapeOwn
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubA
import Johnson.Road.Lane5AttLabel
import Johnson.Road.Rows.AttRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open OnBytes.Road (L5.plan_mats L5.append_at)
open VerifiableInference.Desc.First.Look (lookAt lookAt_att shape_of_made)

/-- A part of as in the planner's list. -/
theorem matrices_as (S : Attention.Shape) (i : Attention.In) {q : ℕ} (hq : q < S.cf.NAs) :
    (Attention.matrices S i)[q]? =
      some (Attention.ownMatrix i ("as" ++ toString q) (2 ^ S.cf.lmS) (S.kAs / S.cf.NAs) q
        i.wpS) := by
  unfold Attention.matrices
  dsimp only
  rw [Array.getElem?_append_left (by simpa using hq)]
  simp [hq]

/-- **The smallness test's list of a plan that the planner returns fits the plan's shape.** -/
theorem matsFit_of_plan {settings : Model.Settings} {j : Attention.In} {cf : Attention.Cfg}
    {X : Attention.Plan} (h : Attention.plan settings j cf = Except.ok X) :
    OnBytes.Road.Rows.MatsFit X.S X.seam.tl := by
  have hm := OnBytes.Road.L5.plan_mats h
  have tailAt : ∀ k : ℕ, (Attention.matrices X.S X.inp)[X.S.cf.NAs + k]? =
      (#[Attention.ownMatrix X.inp "ah" (X.S.cf.wcH * X.S.T) (X.S.fillH / X.S.cf.wcH) X.S.cf.NAs
          X.inp.wph,
        Attention.ownMatrix X.inp "ao" (X.S.cf.wcO * X.S.T) (X.S.fillO / X.S.cf.wcO)
          (X.S.cf.NAs + 1) X.inp.wpo,
        Attention.ownMatrix X.inp "bA" (2 ^ X.S.cf.lmb) X.S.kbA (X.S.cf.NAs + 2) X.inp.wpbA,
        { name := "qa", m := X.S.cf.wcQ * X.S.T, k := X.S.fillQ / X.S.cf.wcQ, kind := 1,
          foreign := some 0, aId := X.inp.midQ, wp := X.inp.wpq }] : Array Model.TMat)[k]? := by
    intro k
    unfold Attention.matrices
    exact OnBytes.Road.L5.append_at _ _ k (by simp)
  refine ⟨K5Law.plan_nm h, fun q hq => ?_, ?_, ?_, ?_⟩
  · rw [hm, Array.getD_eq_getD_getElem?, Array.getElem?_map, matrices_as X.S X.inp hq]
    exact ⟨rfl, rfl⟩
  · rw [hm, Array.getD_eq_getD_getElem?, Array.getElem?_map, show X.S.cf.NAs = X.S.cf.NAs + 0 from rfl,
      tailAt 0]
    rfl
  · rw [hm, Array.getD_eq_getD_getElem?, Array.getElem?_map, tailAt 1]
    rfl
  · rw [hm, Array.getD_eq_getD_getElem?, Array.getElem?_map, tailAt 3]
    rfl

/-- **The place of an attention link's lookup holds the plan's own.** -/
theorem place_att {W : Verify.Public} {g : ℕ} {a : Attention.Plan}
    {x : VerifiableInference.Desc.First.Look.Place} (h4 : W.p4 = true) (ha : W.A[g]? = some a)
    (hx : lookAt W (2 * g + 1) false = some x) :
    x.fs = a.fs ∧ x.lm = a.S.cf.lmb ∧ x.calls = a.S.calls.map (·.call) ∧ x.pub = a.fs.pub ∧
      x.lid = a.lid := by
  have hn : 2 * g + 1 ≠ (if W.p4 then 2 else 1) * W.NGr := by
    rw [h4]
    simp only [if_true]
    omega
  have h0 : (2 * g + 1) % (if W.p4 then 2 else 1) ≠ 0 := by
    rw [h4]
    simp only [if_true]
    omega
  obtain ⟨a', ha', _, e1, e2, e3, e4, e5⟩ := lookAt_att hx hn h0
  have eg : (2 * g + 1) / (if W.p4 then 2 else 1) = g := by
    rw [h4]
    simp only [if_true]
    omega
  rw [eg] at ha'
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  exact ⟨e1, e2, e3, e4, e5⟩

/-- **A return of publicOf with a stored attention plan covers attention**: below profile 4 publicOf
makes no plan (publicOf_cut, OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean). -/
theorem p4_of_public {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) {g : ℕ} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : X.p4 = true := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, _, k3, _, k7⟩ := Fo.Pub.publicOf_cut pol KL layout X h
  rcases k3 with ⟨h4, _⟩ | ⟨_, rfl⟩
  · exact h4
  · rw [k7] at hg
    simp at hg

/-- **Five public premises of the kind's law, as theorems.** -/
theorem guard_theorems {W : Verify.Public} (hP : PlanIs W) (h4 : W.p4 = true) {g : ℕ}
    {a : Attention.Plan} (ha : W.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt W (2 * g + 1) false = some x)
    (set : Params.Setting) :
    (VerifiableInference.Desc.First.Look.P.ofPlace set false x).shape = some x.fs ∧
      (Forest.planeCols x.fs x.lm).toBool = true ∧ x.fs = a.fs ∧
      OnBytes.Road.Rows.MatsFit a.S a.seam.tl ∧ Look.planesOk x.fs (geoOf a.S).lmb = true := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := place_att h4 ha hx
  obtain ⟨A0, pf, hA, e⟩ := hP g a ha
  have k := Fo.Pub2.lookPubA_plan (M₀ := Unit) (fun _ _ => 0) _ _ _ A0 hA 0 0 Unit
  have hM := matsFit_of_plan hA
  subst e
  have h5 : 5 ≤ A0.S.cf.lmb := k.lm5
  have hT : A0.S.cf.lmb ≤ A0.fs.kT + 5 := k.lmT
  refine ⟨shape_of_made (p := VerifiableInference.Desc.First.Look.P.ofPlace set false x) ?_, ?_, e1,
    ⟨hM.nm, hM.asM, hM.ahM, hM.aoM, hM.qaM⟩, ?_⟩
  · show _root_.Fo.ShapeOf x.calls x.pub x.lid x.fs
    rw [e1, e3, e4, e5]
    exact k.shape
  · rw [e1, e2]
    show (Forest.planeCols A0.fs A0.S.cf.lmb).toBool = true
    unfold Forest.planeCols
    rw [if_neg (by simp; omega)]
    rfl
  · rw [e1]
    show Look.planesOk A0.fs A0.S.cf.lmb = true
    unfold Look.planesOk
    rw [decide_eq_true h5, decide_eq_true hT]
    rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.matrices_as
#print axioms VerifiableInference.Desc.First.Att.P.matsFit_of_plan
#print axioms VerifiableInference.Desc.First.Att.P.place_att
#print axioms VerifiableInference.Desc.First.Att.P.p4_of_public
#print axioms VerifiableInference.Desc.First.Att.P.guard_theorems

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05GeoAtPlan.lean: kind K5: GeoFits (Johnson/Desc/First/Att/K05PtsSlots.lean:
five tests on public data) IS A THEOREM AT THE PLANNER's RETURN UNDER THE KIND's ONE TEST ON THE
PLAN (planOkAll), AND SO AT EVERY STORED PLAN OF A PUBLIC RECORD WITH PlanIs
(Johnson/Desc/First/Att/GuardPublic.lean).

Main names:
  `geoFits_of_planOk`: **Attention.plan … = .ok A and planOkAll cf A.S A.fs = true give
    GeoFits (geoOf A.S) A.own.** lt, NP = pairs, Lam: by plan's text (plan_rec). Each softmax unit
    has as many pieces as there are pairs: UnitsAll (Johnson/Desc/First/Att/K05UnitsOk.lean). Each
    entry of the record's score counts the pairs: counts_place, npOf_unit
    (Johnson/Desc/First/Att/K05Record.lean).
  `geoFits_at_seat`: the same at a stored plan a of a public record with PlanIs (a is the planner's
    return at a's own letters, but for one field that GeoFits does not read): GeoFits (parCOf a).geo
    a.own: THE LETTERS AT WHICH THE KIND's SEATED BLOCK HEARS (k5AtN: own := a.own) AND ITS RUNS
    READ (parCOf a).
Premises: the planner's return; planOkAll; (at the seat) PlanIs and the plan's place in the record.
Limits. EMPTY AT: a configuration that the planner refuses or planOkAll fails. By Lean's evaluator
geoFitsB is true at the library's two example geometries (a harness's print; no kernel proof).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05PtsSlots
import Johnson.Desc.First.Att.K05Record
import Johnson.Desc.First.Att.K05PlanAll
import Johnson.Desc.First.Att.GuardPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Attention
open OnBytes.Road.L5 (dimOf)

/-- GeoFits at the planner's return, from the place's four calls and the units. -/
theorem geoFits_of_place {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (h : Attention.plan settings i cf = Except.ok A) {c0 c1 c2 c3 : ACall}
    (Pl : K5Law.PlaceIs A.S c0 c1 c2 c3) {fs : Model.Forest.Shape} {r1 r2 u1 u2 wl ix wh : UnitG}
    (U : UnitsAll A.S fs r1 r2 u1 u2 wl ix wh) : GeoFits (geoOf A.S) A.own := by
  obtain ⟨_, k2⟩ := counts_place Pl
  have e := (K5Law.place_scores Pl).symm.trans U.sco
  simp only [List.cons.injEq, and_true] at e
  have nb : (dimOf A.S).nb = A.S.NP := rfl
  have p1 : u1.pcs.length = A.S.NP := by rw [← nb, ← U.m2.nPw #[], weights_size]
  have p2 : u2.pcs.length = A.S.NP := by rw [← nb, ← U.d2.nPw #[], weights_size]
  have n1 : c1.npOf .fm = A.S.NP := by
    rw [npOf_unit (geoOf A.S) 1 c1 .fm, ← p1, ← e.1]
    rfl
  have n2 : c1.npOf .fd = A.S.NP := by
    rw [npOf_unit (geoOf A.S) 1 c1 .fd, ← p2, ← e.2]
    rfl
  rw [plan_rec h]
  refine ⟨rfl, rfl, rfl, fun u hu => ?_, fun t ht => ?_⟩
  · rw [U.sco] at hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl
    · exact Nat.le_of_eq p1
    · exact Nat.le_of_eq p2
  · have ht' : t ∈ (Counts.of A.S).score.toList := ht
    rw [k2] at ht'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht'
    rcases ht' with rfl | rfl
    · exact n1
    · exact n2

/-- **GeoFits at the planner's return, under the kind's one test on the plan.** -/
theorem geoFits_of_planOk {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (h : Attention.plan settings i cf = Except.ok A)
    (hok : planOkAll cf A.S A.fs = true) : GeoFits (geoOf A.S) A.own := by
  have PA := plan_all (OnBytes.Road.L5.plan_shape h).1 hok
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U⟩ := PA.units
  exact geoFits_of_place h PA.law.place U

/-- **GeoFits at a stored plan of a public record with PlanIs.** -/
theorem geoFits_at_seat {Wv : Verify.Public} (hP : PlanIs Wv) {g : ℕ} {a : Attention.Plan}
    (ha : Wv.A[g]? = some a) (hok : planOkAll a.S.cf a.S a.fs = true) :
    GeoFits (parCOf a).geo a.own := by
  obtain ⟨A0, pf, h0, e⟩ := hP g a ha
  have e1 : a.S = A0.S := by rw [e]
  have e2 : a.own = A0.own := by rw [e]
  have e3 : a.fs = A0.fs := by rw [e]
  show GeoFits (geoOf a.S) a.own
  rw [e1, e2]
  refine geoFits_of_planOk h0 ?_
  rw [← e1, ← e3]
  exact hok

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.geoFits_of_planOk
#print axioms VerifiableInference.Desc.First.Att.P.geoFits_at_seat

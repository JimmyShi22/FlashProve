-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/PlacesAtScope.lean: at every three public files in the scope of the
goals, the stages, the work and the radii of the four places of the kind K12 that are made off the
planner's return are those of the four closed places at the full size.

`placesOfMade` (Johnson/Desc/K12/Plan/PlaceOfPlan.lean) makes the four places off what
Johnson.G.OfPlan.madeOf returns. PlacesFull.lean types four closed places and four functions of
radii. Here the two are joined, in three fields, over all of the scope: by StageSizesAtScope.lean
and LastAtScope.lean (the planner's sized stages and settings are typed values in scope), by
PlacesNums.lean (what placesOfMade lays as stages and as work), and by closed statements that Lean's
kernel evaluates.
Main names, X one of U, O, W, L:
  `radBy_XFull`: at each stage of the closed place, the radius that `radBy` (CondAtMade.lean) looks
    up in the typed list is `rXFull` there. Closed.
  `place_X_of_full`: THE STATEMENT, from `AtFull m.p.chains.made` (StageSizesAtScope.lean) and
    placesOfMade's yes: no planner's name occurs in it. `place_X_at_scope`: from `madeOf`. They say:
    the made place's stages and work are the closed place's, and `radBy` at the planner's own
    setting and stages is `rXFull` at each of these stages.
Limits: `place_L_at_scope` stands under the closed premise `LayoutGroupsAre` (LastAtScope.lean),
which is proved in AtFullSide/LayoutRead/GroupsPaid.lean. One direction: from a madeOf and a
placesOfMade that return; that they return at any file in scope is not shown. THREE THINGS OF A
PLACE ARE JOINED, NOT THE PLACE: its rows, its first and free trees, its index, its answers, its
oracle messages and what stands before it are not spoken of; so no equation of whole places follows.
Nothing on soundness. Nothing on hiding.
-/
import Johnson.Desc.K12.Law.Sizes.LastAtScope
import Johnson.Desc.K12.Law.Sizes.OneRadAtPlaces
import Johnson.Desc.K12.Law.PlacesNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Params Johnson.G.OfPlan
open H2K.Member Lk6.AtPlan
open H2K.Pub (radBy sgOf)
open H2U (placesOfMade laterOfProof stageNums Places4 PlaceNums)
open H2K.Made (places_nums workShared workOwn)

/-! ## 1. Closed: the radius that is looked up in the typed list -/

theorem radByB_UFull : (piUFull.nums.stages.all fun a =>
    radBy setAt szUFull (sgOf a) == rUFull a) = true := by decide +kernel

/-- At each stage of the closed place of the folded row's test. -/
theorem radBy_UFull : ∀ a ∈ piUFull.nums.stages, radBy setAt szUFull (sgOf a) = rUFull a :=
  fun a ha => eq_of_beq (List.all_eq_true.1 radByB_UFull a ha)

theorem radByB_OFull : (piOFull.nums.stages.all fun a =>
    radBy setAt szOFull (sgOf a) == rOFull a) = true := by decide +kernel

/-- At each stage of the closed place of Omega's test. -/
theorem radBy_OFull : ∀ a ∈ piOFull.nums.stages, radBy setAt szOFull (sgOf a) = rOFull a :=
  fun a ha => eq_of_beq (List.all_eq_true.1 radByB_OFull a ha)

theorem radByB_WFull : (piWFull.nums.stages.all fun a =>
    radBy setAt szWFull (sgOf a) == rWFull a) = true := by decide +kernel

/-- At each stage of the closed place of the request's own test. -/
theorem radBy_WFull : ∀ a ∈ piWFull.nums.stages, radBy setAt szWFull (sgOf a) = rWFull a :=
  fun a ha => eq_of_beq (List.all_eq_true.1 radByB_WFull a ha)

theorem radByB_LFull : (piLFull.nums.stages.all fun a =>
    radBy setAt szLFull (sgOf a) == rLFull a) = true := by decide +kernel

/-- At each stage of the closed place of the first chain's last test. -/
theorem radBy_LFull : ∀ a ∈ piLFull.nums.stages, radBy setAt szLFull (sgOf a) = rLFull a :=
  fun a ha => eq_of_beq (List.all_eq_true.1 radByB_LFull a ha)

/-! ## 2. From what the planner has made -/

/-- The work that placesOfMade lays, where the test on the table is no one-time test. -/
theorem works_of_later (m : Made) (X : Places4) (h : placesOfMade m = .ok X)
    (hot : m.p.chains.made.sized.proof.batch.lines.oneTime = false) :
    X.L.nums.work = m.p.chains.made.sized.set.workOf .query .request ∧
      X.U.nums.work = m.p.chains.made.sized.set.workOf .query .shared ∧
      (∀ o, X.O = some o → o.nums.work = m.p.chains.made.sized.set.workOf .query .shared) ∧
      X.W.nums.work = m.p.chains.made.sized.set.workOf .query .request := by
  obtain ⟨⟨_, wL⟩, g, ⟨_, wU⟩, hO, ⟨_, wW⟩⟩ := places_nums m X h
  have sh : workShared (laterOfProof m g) =
      m.p.chains.made.sized.set.workOf .query .shared := by
    show m.p.chains.made.sized.set.workOf .query
      (if m.p.chains.made.sized.proof.batch.lines.oneTime then .once else .shared) = _
    rw [hot]
    rfl
  have ow : workOwn (laterOfProof m g) =
      m.p.chains.made.sized.set.workOf .query .request := by
    show m.p.chains.made.sized.set.workOf .query
      (if m.p.chains.made.sized.proof.batch.lines.oneTime then .once else .request) = _
    rw [hot]
    rfl
  exact ⟨wL, wU.trans sh, fun o ho => (hO o ho).2.trans sh, wW.trans ow⟩

section
variable {m : Made} (A : AtFull m.p.chains.made) {X : Places4} (h : placesOfMade m = .ok X)
include A h

/-- **The folded row's place.** -/
theorem place_U_of_full :
    X.U.nums.stages = piUFull.nums.stages ∧ X.U.nums.work = piUFull.nums.work ∧
      ∀ a ∈ X.U.nums.stages, radBy m.p.chains.made.sized.proof.set
        m.p.chains.made.sized.proof.batch.folded.stages (sgOf a) = rUFull a := by
  obtain ⟨_, g, ⟨e, _⟩, _, _⟩ := places_nums m X h
  have w := (works_of_later m X h A.later).2.1
  rw [A.U] at e
  have e' : X.U.nums.stages = piUFull.nums.stages := e.trans stages_UFull.symm
  refine ⟨e', ?_, ?_⟩
  · rw [w, A.set]
    exact work_UFull.symm
  · rw [e', A.setP, A.U]
    exact radBy_UFull

/-- **Omega's place**, where there is one. -/
theorem place_O_of_full (o : PlaceNums) (ho : X.O = some o) :
    o.nums.stages = piOFull.nums.stages ∧ o.nums.work = piOFull.nums.work ∧
      ∀ a ∈ o.nums.stages, radBy m.p.chains.made.sized.proof.set
        m.p.chains.made.sized.proof.batch.omega.stages (sgOf a) = rOFull a := by
  obtain ⟨_, g, _, hO, _⟩ := places_nums m X h
  have e := (hO o ho).1
  have w := (works_of_later m X h A.later).2.2.1 o ho
  rw [A.O] at e
  have e' : o.nums.stages = piOFull.nums.stages := e.trans stages_OFull.symm
  refine ⟨e', ?_, ?_⟩
  · rw [w, A.set]
    exact work_OFull.symm
  · rw [e', A.setP, A.O]
    exact radBy_OFull

/-- **The place of the request's own test.** -/
theorem place_W_of_full :
    X.W.nums.stages = piWFull.nums.stages ∧ X.W.nums.work = piWFull.nums.work ∧
      ∀ a ∈ X.W.nums.stages, radBy m.p.chains.made.sized.proof.set
        m.p.chains.made.sized.proof.batch.own.stages (sgOf a) = rWFull a := by
  obtain ⟨_, g, _, _, ⟨e, _⟩⟩ := places_nums m X h
  have w := (works_of_later m X h A.later).2.2.2
  rw [A.W] at e
  have e' : X.W.nums.stages = piWFull.nums.stages := e.trans stages_WFull.symm
  refine ⟨e', ?_, ?_⟩
  · rw [w, A.set]
    exact work_WFull.symm
  · rw [e', A.setP, A.W]
    exact radBy_WFull

/-- **The place of the first chain's last test**, where that test's stages are the typed list. -/
theorem place_L_of_full (hL : m.p.chains.made.sized.proof.last.stages = szLFull) :
    X.L.nums.stages = piLFull.nums.stages ∧ X.L.nums.work = piLFull.nums.work ∧
      ∀ a ∈ X.L.nums.stages, radBy m.p.chains.made.sized.proof.set
        m.p.chains.made.sized.proof.last.stages (sgOf a) = rLFull a := by
  obtain ⟨⟨e, _⟩, _⟩ := places_nums m X h
  have w := (works_of_later m X h A.later).1
  rw [hL] at e
  have e' : X.L.nums.stages = piLFull.nums.stages := e.trans stages_LFull.symm
  refine ⟨e', ?_, ?_⟩
  · rw [w, A.set]
    exact work_LFull.symm
  · rw [e', A.setP, hL]
    exact radBy_LFull

end

/-! ## 3. At the scope, from Johnson.G.OfPlan.madeOf -/

section
variable {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {m : Made}
  (hm : madeOf Z.pol Z.lay Z.KL = .ok m) {X : Places4} (h : placesOfMade m = .ok X)
include hZ hm h

theorem place_U_at_scope :
    X.U.nums.stages = piUFull.nums.stages ∧ X.U.nums.work = piUFull.nums.work ∧
      ∀ a ∈ X.U.nums.stages, radBy m.p.chains.made.sized.proof.set
        m.p.chains.made.sized.proof.batch.folded.stages (sgOf a) = rUFull a :=
  place_U_of_full (atFull_at_made hZ hm) h

theorem place_O_at_scope (o : PlaceNums) (ho : X.O = some o) :
    o.nums.stages = piOFull.nums.stages ∧ o.nums.work = piOFull.nums.work ∧
      ∀ a ∈ o.nums.stages, radBy m.p.chains.made.sized.proof.set
        m.p.chains.made.sized.proof.batch.omega.stages (sgOf a) = rOFull a :=
  place_O_of_full (atFull_at_made hZ hm) h o ho

theorem place_W_at_scope :
    X.W.nums.stages = piWFull.nums.stages ∧ X.W.nums.work = piWFull.nums.work ∧
      ∀ a ∈ X.W.nums.stages, radBy m.p.chains.made.sized.proof.set
        m.p.chains.made.sized.proof.batch.own.stages (sgOf a) = rWFull a :=
  place_W_of_full (atFull_at_made hZ hm) h

/-- Under the closed premise on the layout file. -/
theorem place_L_at_scope (hG : LayoutGroupsAre) :
    X.L.nums.stages = piLFull.nums.stages ∧ X.L.nums.work = piLFull.nums.work ∧
      ∀ a ∈ X.L.nums.stages, radBy m.p.chains.made.sized.proof.set
        m.p.chains.made.sized.proof.last.stages (sgOf a) = rLFull a :=
  place_L_of_full (atFull_at_made hZ hm) h (last_at_made hG hZ hm)

end

end H2K.Sizes

#print axioms H2K.Sizes.place_U_of_full
#print axioms H2K.Sizes.place_O_of_full
#print axioms H2K.Sizes.place_W_of_full
#print axioms H2K.Sizes.place_L_of_full
#print axioms H2K.Sizes.place_U_at_scope
#print axioms H2K.Sizes.place_O_at_scope
#print axioms H2K.Sizes.place_W_at_scope
#print axioms H2K.Sizes.place_L_at_scope

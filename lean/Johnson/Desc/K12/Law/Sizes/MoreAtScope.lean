-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/MoreAtScope.lean: at every three public files in the scope of the goals,
five further fields of three of the four places of the kind K12 that are made off the planner's
return are those of the closed places at the full size: the rows, the own mask, the answers, whether
the masks come early, and the chain.

`placesLater` (Johnson/Desc/K12/Plan/PlaceOfPlan.lean) lays these five fields from the setting's
number of samples and four fields of the shape of the test on the table. Params.linSized's closing
text fixes these four fields. By `AtFull` (StageSizesAtScope.lean) they are closed values at every
file in scope.
Main names:
  `later_more`, `places_more`: what placesLater and placesOfMade lay in the five fields. No scope.
  `firstTree_full`: the first tree's number at the four closed places.
  `more_U_of_full`, `more_O_of_full`, `more_W_of_full`: THE STATEMENTS, from
    `AtFull m.p.chains.made` (StageSizesAtScope.lean) and placesOfMade's yes: no planner's name
    occurs in them.
  `more_U_at_scope`, `more_O_at_scope`, `more_W_at_scope`: the same from `madeOf`.
The chain's equation is what makes `proximityTestParametersAt P x` (Johnson/Desc/K12/AtPlan.lean) the place's own record
at an address P on that chain: proximityTestParametersAt refuses where P.chain differs from x.chain.
Limits: one direction: from a madeOf and a placesOfMade that return; that they return at any file in
scope is not shown. Nothing on the place of the first chain's last test. With PlacesAtScope.lean
eight things of a place are joined, NOT THE PLACE: the first trees, the free trees, the first tree's
number, the index and the first group are not joined here; so no equation of whole places follows.
Nothing on soundness. Nothing on hiding.
-/
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.K12.Plan.PlaceOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Params Johnson.G.OfPlan
open H2K.Member Lk6.AtPlan
open H2U (placesOfMade placesLater laterOfProof mkPlace stageNums Places4 PlaceNums Later3
  LaterArgs)

/-! ## 1. Without a scope -/

/-- What mkPlace lays. -/
theorem later_more (A : LaterArgs) (X : Later3) (h : placesLater A = .ok X) :
    (X.U.nums.rows = A.batch.shape.fold.index.answers + A.batch.shape.fold.columns + 1 +
        2 * A.set.samples ∧ X.U.nums.ownMask = !A.batch.shape.masksAhead ∧
      X.U.answers = A.set.samples ∧ X.U.early = A.batch.shape.choice.masksRide ∧ X.U.chain = 2) ∧
    (∀ o, X.O = some o →
      o.nums.rows = 1 + 2 * A.set.samples ∧ o.nums.ownMask = true ∧ o.answers = A.set.samples ∧
        o.early = A.batch.shape.choice.masksRide ∧ o.chain = 2) ∧
    (X.W.nums.rows = 2 + 3 * A.set.samples ∧ X.W.nums.ownMask = !A.batch.shape.masksAhead ∧
      X.W.answers = A.set.samples ∧ X.W.early = A.batch.shape.choice.masksRide ∧
      X.W.chain = 3) := by
  unfold placesLater at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals
    first
    | (cases h
       refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
       intro o ho
       cases ho
       exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | (cases h
       refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
       intro o ho
       cases ho)
    | cases h

/-- The same of the proof file's places. -/
theorem places_more (m : Made) (X : Places4) (h : placesOfMade m = .ok X) :
    (X.U.nums.rows = m.p.chains.made.sized.proof.batch.shape.fold.index.answers +
        m.p.chains.made.sized.proof.batch.shape.fold.columns + 1 +
        2 * m.p.chains.made.sized.set.samples ∧
      X.U.nums.ownMask = !m.p.chains.made.sized.proof.batch.shape.masksAhead ∧
      X.U.answers = m.p.chains.made.sized.set.samples ∧
      X.U.early = m.p.chains.made.sized.proof.batch.shape.choice.masksRide ∧ X.U.chain = 2) ∧
    (∀ o, X.O = some o →
      o.nums.rows = 1 + 2 * m.p.chains.made.sized.set.samples ∧ o.nums.ownMask = true ∧
        o.answers = m.p.chains.made.sized.set.samples ∧
        o.early = m.p.chains.made.sized.proof.batch.shape.choice.masksRide ∧ o.chain = 2) ∧
    (X.W.nums.rows = 2 + 3 * m.p.chains.made.sized.set.samples ∧
      X.W.nums.ownMask = !m.p.chains.made.sized.proof.batch.shape.masksAhead ∧
      X.W.answers = m.p.chains.made.sized.set.samples ∧
      X.W.early = m.p.chains.made.sized.proof.batch.shape.choice.masksRide ∧ X.W.chain = 3) := by
  unfold placesOfMade at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i X3 hX3
        split at h
        · cases h
        · cases h
          exact later_more _ X3 hX3

/-- The first tree's number at the four closed places. What placesOfMade lays there is said in
FirstTreeOfMade.lean. -/
theorem firstTree_full : piUFull.nums.firstTree = 0 ∧ piOFull.nums.firstTree = 0 ∧
    piLFull.nums.firstTree = 0 ∧ piWFull.nums.firstTree = 84 := ⟨rfl, rfl, rfl, rfl⟩

/-! ## 2. From what the planner has made -/

/-- The rows that are batched on the folded row's group, at the typed lines. -/
theorem rowsU_full : (indexShapeOf recordSet recordTable).answers +
    linColumnsOf recordSet prLin recordTable + 1 + 2 * setAt.samples = 68 := by
  have h := congrArg LinGroups.foldedRows prGroups_eq
  rw [← set_eq]
  exact h

section
variable {m : Made} (A : AtFull m.p.chains.made) {X : Places4} (h : placesOfMade m = .ok X)
include A h

/-- **The folded row's place.** -/
theorem more_U_of_full :
    X.U.nums.rows = piUFull.nums.rows ∧ X.U.nums.ownMask = piUFull.nums.ownMask ∧
      X.U.answers = piUFull.answers ∧ X.U.early = piUFull.early ∧
      X.U.chain = piUFull.place.chain := by
  obtain ⟨⟨r1, r2, r3, r4, r5⟩, _, _⟩ := places_more m X h
  rw [A.index, A.columns, A.set] at r1
  rw [A.ahead] at r2
  rw [A.set] at r3
  rw [A.choice] at r4
  exact ⟨r1.trans rowsU_full, r2, r3, r4, r5⟩

/-- **Omega's place**, where there is one. -/
theorem more_O_of_full (o : PlaceNums) (ho : X.O = some o) :
    o.nums.rows = piOFull.nums.rows ∧ o.nums.ownMask = piOFull.nums.ownMask ∧
      o.answers = piOFull.answers ∧ o.early = piOFull.early ∧ o.chain = piOFull.place.chain := by
  obtain ⟨_, hO, _⟩ := places_more m X h
  obtain ⟨r1, r2, r3, r4, r5⟩ := hO o ho
  rw [A.set] at r1 r3
  rw [A.choice] at r4
  exact ⟨r1, r2, r3, r4, r5⟩

/-- **The place of the request's own test.** -/
theorem more_W_of_full :
    X.W.nums.rows = piWFull.nums.rows ∧ X.W.nums.ownMask = piWFull.nums.ownMask ∧
      X.W.answers = piWFull.answers ∧ X.W.early = piWFull.early ∧
      X.W.chain = piWFull.place.chain := by
  obtain ⟨_, _, ⟨r1, r2, r3, r4, r5⟩⟩ := places_more m X h
  rw [A.set] at r1 r3
  rw [A.ahead] at r2
  rw [A.choice] at r4
  exact ⟨r1, r2, r3, r4, r5⟩

end

/-! ## 3. At the scope, from Johnson.G.OfPlan.madeOf -/

section
variable {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {m : Made}
  (hm : madeOf Z.pol Z.lay Z.KL = .ok m) {X : Places4} (h : placesOfMade m = .ok X)
include hZ hm h

theorem more_U_at_scope :
    X.U.nums.rows = piUFull.nums.rows ∧ X.U.nums.ownMask = piUFull.nums.ownMask ∧
      X.U.answers = piUFull.answers ∧ X.U.early = piUFull.early ∧
      X.U.chain = piUFull.place.chain :=
  more_U_of_full (atFull_at_made hZ hm) h

theorem more_O_at_scope (o : PlaceNums) (ho : X.O = some o) :
    o.nums.rows = piOFull.nums.rows ∧ o.nums.ownMask = piOFull.nums.ownMask ∧
      o.answers = piOFull.answers ∧ o.early = piOFull.early ∧ o.chain = piOFull.place.chain :=
  more_O_of_full (atFull_at_made hZ hm) h o ho

theorem more_W_at_scope :
    X.W.nums.rows = piWFull.nums.rows ∧ X.W.nums.ownMask = piWFull.nums.ownMask ∧
      X.W.answers = piWFull.answers ∧ X.W.early = piWFull.early ∧
      X.W.chain = piWFull.place.chain :=
  more_W_of_full (atFull_at_made hZ hm) h

end

end H2K.Sizes

#print axioms H2K.Sizes.places_more
#print axioms H2K.Sizes.more_U_of_full
#print axioms H2K.Sizes.more_O_of_full
#print axioms H2K.Sizes.more_W_of_full
#print axioms H2K.Sizes.more_U_at_scope
#print axioms H2K.Sizes.more_O_at_scope
#print axioms H2K.Sizes.more_W_at_scope

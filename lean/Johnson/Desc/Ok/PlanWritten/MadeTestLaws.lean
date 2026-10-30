-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean: what a yes and a no of the tests on what the planner
configures say (`madeIs`, `firstIs`, Johnson/Desc/Ok/PlanWritten/MadeTest.lean); that the two
earlier tests follow from them; negative tests.

Definitions.
  `MadeWritten made`: two equations: the proof file's sizes are `proofSizedFull`; the first of its
    lists is the first written list (`proofThree.A.plan`,
    Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean). `FirstWritten f`: the six equations on the
    first chain's parameters as read back; the sixth: the layout of a request's arrays is
    `layoutFull` (Johnson/G/LayoutLit.lean).
  `madePinned k made f m`: at the full size's key (`fullKey`, Johnson/Desc/Ok/PlanWritten/Test.lean)
    `madeIs made`, `firstIs f`, `proofSendsIs m` (Johnson/Desc/Ok/PlanWritten/SendsTest.lean: the
    proof file's three lists of what is sent are the written ones) and `xShapeIs m.p.X`
    (Johnson/Desc/Ok/PlanWritten/XShapeTest.lean: the shape part of what `verify-on-bytes`'s reader
    makes of the public files is the written one); at every other key: yes. `madePinnedAt P made f
    m`: the key off the strict scan P of the parameter file. They are the form of which the laws
    speak; the verifier's list of tests writes the guard on the key itself.
Statements and proofs.
  `lit_three`: `proofLit` is `proofThree.A`.
  `made_of_is`, `madeIs_of`: `madeIs` says yes just where the two equations hold. A yes gives
    equations of whole values (`sameProof_eq`, Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean;
    `ride_eq`, Johnson/Desc/Ok/NumberPrices/ByRuns.lean): so no field and no round is left out. The
    converse wants that the written list passes the walk against itself (`ride_self`): the walk's
    completeness is not proved in general.
  `first_of_is`, `firstIs_of`: `firstIs` says yes just where the six hold.
  `made_of_pinned`: at the full size's key a yes gives all ten equations. `madePinned_other`: at
    every other key the test says yes.
  `made_no`: WHAT A NO REJECTS: the key is the full size's, (L, d, V) = (48, 5120, 202048), and one
    of the ten equations fails; its comment lists what can part.
  `pinnedAt_row`, `pinnedAt_of_row`: at a public part the law form is the row `madeRow`
    (MadeTest.lean) behind the guard on the key; a yes of the row as a verifier's list of tests
    writes it (not at the full size's key, or `madeRow`) gives a yes of the law form.
  `sized_of_made`, `first_of_made`: a yes of `madePinnedAt` gives a yes of `sizedPinnedAt` and of
    `firstPinnedAt` (SizedTest.lean): so what is stated over these two stands unturned. By an
    evaluation in Lean's kernel (`decide +kernel`): `ride_self`: a walk of 48293 rounds. Negative
    tests, by the kernel: `no_bound`: with one more in the exponent of the error bound of the list's
    first round the walk says no. `no_short`: with the list's first round left out it says no.
    `no_layout`: with one more in the first place of the layout's first rectangle (`layoutBent`) the
    comparison of the layouts says no. `layout_counts`: the written layout has 25 segments, 227
    arrays and 5419 rectangles. `no_list`: where the planner has no list, `madeIs` says no whatever
    the sizes are. Those on the sizes and on the first chain's parameters stand in
    SizedTestLaws.lean.

Limits. That the planner's values at any public files pass the tests is not said: that is the
reference run's to show. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.MadeTest
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import Johnson.Desc.Ok.PlanWritten.SendsTestLaws
import Johnson.Desc.Ok.PlanWritten.XShapeLaws
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Number.ByRuns (Lit rideB ride_eq proofThree)

/-- The written list of the test is the first of `proofThree`. -/
theorem lit_three : proofLit = proofThree.A := rfl

/-- The two equations. -/
def MadeWritten (made : Configured) : Prop :=
  made.sized.proof = proofSizedFull ∧ made.proof.head? = some proofThree.A.plan

/-- **A yes gives the two equations, of whole values.** -/
theorem made_of_is {made : Configured} (h : madeIs made = true) : MadeWritten made := by
  unfold madeIs at h
  rw [Bool.and_eq_true] at h
  refine ⟨sameProof_eq h.1, ?_⟩
  have h2 := h.2
  cases hp : made.proof with
  | nil =>
    rw [hp] at h2
    cases h2
  | cons a l =>
    rw [hp] at h2
    exact congrArg some (ride_eq h2)

set_option maxRecDepth 1000000 in
/-- The written list passes the walk against itself. -/
theorem ride_self : rideB 60000 proofThree.A.plan proofLit = true := by decide +kernel

/-- **The test says yes wherever the two equations hold.** -/
theorem madeIs_of {made : Configured} (h : MadeWritten made) : madeIs made = true := by
  obtain ⟨h1, h2⟩ := h
  unfold madeIs
  rw [h1, sameProof_self, Bool.true_and]
  cases hp : made.proof with
  | nil =>
    rw [hp] at h2
    cases h2
  | cons a l =>
    rw [hp] at h2
    obtain rfl : a = proofThree.A.plan := Option.some.inj h2
    exact ride_self

/-- The six equations on the first chain's parameters as read back. -/
def FirstWritten (f : First) : Prop :=
  f.codes = proofSizedFull.codes ∧ f.lin = proofSizedFull.batch.shape ∧
    f.shape = proofSizedFull.request ∧ f.pendingRows = 13 ∧ f.binding = ⟨6, 40⟩ ∧
    f.layout = layoutFull

theorem first_of_is {f : First} (h : firstIs f = true) : FirstWritten f := by
  simp only [firstIs, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem firstIs_of {f : First} (h : FirstWritten f) : firstIs f = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [firstIs, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

/-- **At the full size's key**: the four tests. At every other key: yes. Do not call this with a k
of your own: call `madePinnedAt`. The fourth test reads m.p.X. -/
def madePinned (k : ℕ × ℕ × ℕ) (made : Configured) (f : First) (m : OfPlan.Made) : Bool :=
  if k = fullKey then madeIs made && firstIs f && proofSendsIs m && xShapeIs m.p.X else true

/-- P: the strict scan of the parameter file; made: what the planner configured at the same public
files; f: what the reader made of the first chain's parameter bytes there; m: the structure that
holds the lists of what is sent and what `verify-on-bytes`'s reader made of the files. -/
def madePinnedAt (P : OnBytes.Model.PolScan) (made : Configured) (f : First) (m : OfPlan.Made) :
    Bool :=
  madePinned (keyOfScan P) made f m

/-- **At the full size's key a yes gives all ten equations.** -/
theorem made_of_pinned {made : Configured} {f : First} {m : OfPlan.Made}
    (h : madePinned fullKey made f m = true) :
    MadeWritten made ∧ FirstWritten f ∧ m.proof = proofSendsFull ∧
      xShapeOf m.p.X = xShapeFull := by
  unfold madePinned at h
  rw [if_pos rfl, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨made_of_is h.1.1.1, first_of_is h.1.1.2, proofSends_of_is h.1.2, xShape_of_is h.2⟩

/-- At every other key the test says yes. -/
theorem madePinned_other {k : ℕ × ℕ × ℕ} (made : Configured) (f : First) (m : OfPlan.Made)
    (hk : k ≠ fullKey) : madePinned k made f m = true := by
  unfold madePinned
  rw [if_neg hk]

/-- **What a no rejects.** The key is the full size's, and one of the ten equations fails: one of
these parts from its written value: the planner's sizes of a proof file, in some field; the first of
the proof file's lists of rounds, in that there is none, in its setting, in its length, or in one of
the seven fields of one of its rounds (the entry, the error bound, the group from which it was
priced, the kind of argument, the footing of a count, who pays for the proof of work, the mark of a
fault); one of six fields of the first chain's parameters as read back, the layout of a request's
arrays among them, in some array's name, message, size or rectangle; the proof file's three lists of
what is sent; the shape part of what `verify-on-bytes`'s reader makes of the public files. -/
theorem made_no {k : ℕ × ℕ × ℕ} {made : Configured} {f : First} {m : OfPlan.Made}
    (h : madePinned k made f m = false) :
    k = fullKey ∧ ¬ (MadeWritten made ∧ FirstWritten f ∧ m.proof = proofSendsFull ∧
      xShapeOf m.p.X = xShapeFull) := by
  by_cases hk : k = fullKey
  · refine ⟨hk, fun e => ?_⟩
    unfold madePinned at h
    rw [if_pos hk, madeIs_of e.1, firstIs_of e.2.1, proofSendsIs_of e.2.2.1,
      xShapeIs_of e.2.2.2] at h
    cases h
  · rw [madePinned_other made f m hk] at h
    cases h

/-- The law form at a public part is the row behind the guard on the key. -/
theorem pinnedAt_row (Z : ProofFile.Pub) :
    madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made =
      if keyOfScan Z.p.X.P = fullKey then madeRow Z else true := rfl

/-- **A yes of the row as a verifier's list of tests writes it gives a yes of the law form.** -/
theorem pinnedAt_of_row {Z : ProofFile.Pub}
    (h : (!decide (keyOfScan Z.p.X.P = fullKey) || madeRow Z) = true) :
    madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true := by
  rw [pinnedAt_row]
  by_cases hk : keyOfScan Z.p.X.P = fullKey
  · rw [if_pos hk]
    rw [decide_eq_true hk] at h
    exact h
  · rw [if_neg hk]

/-! ## The two earlier tests follow -/

theorem sized_of_made {P : OnBytes.Model.PolScan} {made : Configured} {f : First}
    {m : OfPlan.Made} (h : madePinnedAt P made f m = true) : sizedPinnedAt P made = true := by
  unfold madePinnedAt madePinned at h
  unfold sizedPinnedAt sizedPinned
  by_cases hk : keyOfScan P = fullKey
  · rw [if_pos hk] at h ⊢
    unfold madeIs at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1.1
  · rw [if_neg hk]

theorem first_of_made {P : OnBytes.Model.PolScan} {made : Configured} {f : First}
    {m : OfPlan.Made} (h : madePinnedAt P made f m = true) : firstPinnedAt P f = true := by
  unfold madePinnedAt madePinned at h
  unfold firstPinnedAt firstPinned
  by_cases hk : keyOfScan P = fullKey
  · rw [if_pos hk] at h ⊢
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    have h2 := h.1.1.2
    unfold firstIs at h2
    rw [Bool.and_eq_true] at h2
    exact h2.1
  · rw [if_neg hk]

/-! ## Negative tests -/

set_option maxRecDepth 1000000 in
/-- With one more in the exponent of the first round's error bound the walk says no. -/
theorem no_bound : rideB 60000 { proofThree.A.plan with
    rounds := proofThree.A.plan.rounds.modifyHead fun r =>
      { r with error := { r.error with e := r.error.e + 1 } } } proofLit = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the first round left out the walk says no. -/
theorem no_short : rideB 60000 { proofThree.A.plan with
    rounds := proofThree.A.plan.rounds.tail } proofLit = false := by decide +kernel

/-- The written layout with one more in the first place of its first rectangle. -/
def layoutBent : ReqLayout :=
  ⟨(layoutFirst.modifyHead fun a =>
      { a with
        blocks := a.blocks.modifyHead fun b => { b with firstPlace := b.firstPlace + 1 } }) ::
    layoutFull.link.tail⟩

set_option maxRecDepth 100000 in
/-- With one rectangle bent the comparison of the layouts says no. -/
theorem no_layout : decide (layoutBent = layoutFull) = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- 25 segments, 227 arrays, 5419 rectangles. -/
theorem layout_counts : layoutFull.link.length = 25 ∧
    (layoutFull.link.map (·.length)).sum = 227 ∧
    (layoutFull.link.map fun l => (l.map (·.blocks.length)).sum).sum = 5419 := by decide +kernel

/-- Where the planner has no list the test says no. -/
theorem no_list {made : Configured} (h : made.proof = []) : madeIs made = false := by
  unfold madeIs
  rw [h, Bool.and_false]

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.lit_three
#print axioms VerifiableInference.PlanWritten.made_of_is
#print axioms VerifiableInference.PlanWritten.ride_self
#print axioms VerifiableInference.PlanWritten.madeIs_of
#print axioms VerifiableInference.PlanWritten.first_of_is
#print axioms VerifiableInference.PlanWritten.firstIs_of
#print axioms VerifiableInference.PlanWritten.made_of_pinned
#print axioms VerifiableInference.PlanWritten.madePinned_other
#print axioms VerifiableInference.PlanWritten.made_no
#print axioms VerifiableInference.PlanWritten.pinnedAt_row
#print axioms VerifiableInference.PlanWritten.pinnedAt_of_row
#print axioms VerifiableInference.PlanWritten.sized_of_made
#print axioms VerifiableInference.PlanWritten.first_of_made
#print axioms VerifiableInference.PlanWritten.no_bound
#print axioms VerifiableInference.PlanWritten.no_short
#print axioms VerifiableInference.PlanWritten.no_layout
#print axioms VerifiableInference.PlanWritten.layout_counts
#print axioms VerifiableInference.PlanWritten.no_list

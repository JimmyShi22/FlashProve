-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontOne.lean: THE TWO EQUATIONS BY FIELD OF K5's ROW WHERE THE FRONT
HAS RETURNED, PAID OFF THE FRONT ALONE. Calls alone; nothing is evaluated here.
  `cuts_of_plans`: where `pubBy` returns Z and the plan's first list is the written one, Z's table
    of stretches is `cutWritten`: `pubBy_cuts` (Johnson/Goal/Numbers/WrittenOfPins.lean) and
    `cut_written` (Johnson/AtFull/Cut/CutAtWritten.lean).
  `entries_of_plans`: and the entries of Z's declared rounds are the written ones: `pubBy_entries`
    (Johnson/Goal/Numbers/PlanWrittenPlans.lean).
  `k5Before_of_plans`: so "before" at the twelve (`k5Before_written`, K5BeforeWritten.lean).
  **`hc_made` · `hD_made`**: the two premises hc and hD of `k5_row_front` (K5RowFront.lean), each in
    its own form there, from the public part's return (at any three files, as in the frame) and ONE
    EQUATION BY FIELD: the planner's three lists for the proof file are the three written ones; by
    `plans_made` (K5FrontE0.lean). `cuts_made`: the whole table, the like.
NO PIN, NO SCOPE, AND NO PREMISE UNDER THE HEAD.
Limits: those of the files that are called. An implication: none of its premises is shown at any
public files. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5BeforeWritten
import Johnson.Desc.First.Att.Row.K5FrontE0
import Johnson.AtFull.Cut.CutAtWritten
import Johnson.Goal.Numbers.WrittenOfPins
import Johnson.Goal.Numbers.PlanWrittenPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open VerifiableInference.PlanWritten (pubBy_entries)
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.AtFull.Cut (cutWritten cut_written)

section
variable {made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made}
  {st : ProofFile.Starts} {pol lay KL : ByteArray} {Z : ProofFile.Pub}

/-- The table of stretches, from the plan's first list. -/
theorem cuts_of_plans (hZ : ProofFile.pubBy made st pol lay KL = .ok Z)
    (h1 : Z.plans.1 = P5T.esFull.1) : Z.cuts = cutWritten := by
  have e := Desc.K14.Law.pubBy_cuts hZ
  rw [h1] at e
  exact Option.some.inj (e.symm.trans cut_written)

/-- The declared rounds' entries, from the plan's first list. -/
theorem entries_of_plans (hZ : ProofFile.pubBy made st pol lay KL = .ok Z)
    (h1 : Z.plans.1 = P5T.esFull.1) : Z.D.1.map (·.entry) = P5T.esFull.1 :=
  (pubBy_entries hZ).1.trans h1

/-- "before" at the twelve, from the plan's first list. -/
theorem k5Before_of_plans (hZ : ProofFile.pubBy made st pol lay KL = .ok Z)
    (h1 : Z.plans.1 = P5T.esFull.1) (g : ℕ) (hg : g < 12) :
    H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 * g)] :=
  k5Before_written (cuts_of_plans hZ h1) (entries_of_plans hZ h1) g hg

end

variable {Z : ProofFile.Pub}

/-- `pubPlain` is `pubBy` at its own two letters. -/
theorem asBy {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) :
    ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z := hZ

/-- **The premise hc of `k5_row_front`, off the front, by field.** -/
theorem hc_made {pol lay KL : ByteArray} (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    (Z.cuts.map fun c => (c.look, c.take)) = cutPairsW :=
  congrArg (List.map fun c => (c.look, c.take)) (cuts_of_plans (asBy hZ) (plans_made hZ hm))

/-- **The premise hD of `k5_row_front`, off the front, by field.** -/
theorem hD_made {pol lay KL : ByteArray} (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    Z.D.1.map (·.entry) = P5T.esFull.1 :=
  entries_of_plans (asBy hZ) (plans_made hZ hm)

/-- The whole table of stretches, the like (another kind's row asks it so). -/
theorem cuts_made {pol lay KL : ByteArray} (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    Z.cuts = cutWritten :=
  cuts_of_plans (asBy hZ) (plans_made hZ hm)

end H2K5.Row

#print axioms H2K5.Row.cuts_of_plans
#print axioms H2K5.Row.entries_of_plans
#print axioms H2K5.Row.k5Before_of_plans
#print axioms H2K5.Row.hc_made
#print axioms H2K5.Row.hD_made
#print axioms H2K5.Row.cuts_made

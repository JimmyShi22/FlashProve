-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtKeyRanges.lean: `test_accepts_all` (WholeAll.lean in this
folder), in the form `accepts_of_plan` (PlanB.lean in this folder), at the written-out place of the
key file's test on the ranges, at the full size, with the plan's half proved. A place (`P12`,
Johnson/Desc/K12/Frame.lean) is the structure of the numbers of one proximity test in a file, among
them its list of stages (`Fmt.M1.Stage`). The plan's half is the list of clauses `planL`
(PlanB.lean): they read only the place, a table of codes and the number of trees that the first
switch opens. The place is the closed term `piKRFull`
(Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean); the table of codes is the key file's, `codesKeyFull`
(Johnson/Desc/K12/Law/PlacesKeyFull.lean). The place has four stages, (k, h) = (4, 4), (4, 3),
(3, 3), (0, 0); by its numbers the first fold's fresh table has come earlier and the first switch
opens one tree. The main theorem is general in the job (`TestJob`, Test.lean in this folder: what a
caller supplies for its test) among those at that place, and in every other argument. Two theorems
with their proofs and three `#guard` lines; no definition. The other terms are explained in the head
of PlanB.lean.

  `accepts_at_key_ranges`: at a job at that place, if the library's plain data list one tree, and
    `ShapeAsks` at those codes, `FormAsks` and `DataAsks` hold, then the decision of the test's
    block accepts all that `testAll` shows: the block's `decide`, at the job's state on entry
    `J.rec₀ w fr`, the rounds of `testAll J w fr C D` without their digests and its groups of
    opened columns, returns `.ok t'` for some state t'
  `planB_KR`: all twenty-two clauses of the plan's half hold at that place, those codes and one
    tree: a theorem, by an evaluation in Lean's kernel (`decide +kernel`). It reads no state

By what. `planB_KR`: `decide +kernel` on closed terms. `accepts_at_key_ranges`: `accepts_of_plan`
(PlanB.lean) at `codesKeyFull`; its hypothesis that `planB J.p codesKeyFull Dp.ts.length` is true
is rewritten by hJ and hT and is then `planB_KR`.

Hypotheses. Of `accepts_at_key_ranges`. hJ: the job's place is `piKRFull`. hT: the plain data Dp
(`Plain`, Johnson/Desc/K12/Law/FirstOk.lean) list one tree. S: `ShapeAsks` at `codesKeyFull` and Dp:
clauses on the job's state on entry, on the state after the batching (`J.recB`) and on the state
after the first fold (`tFold`). F: `FormAsks`: clauses on the challenges D. Dt: `DataAsks`: clauses
on the prover's data. The three structures are defined in PlanB.lean; its head says what each clause
asks and what it reads.

Limits.
- No job is built here: J is a free parameter with `J.p = piKRFull`.
- The three structures are shown of no value at this place: whether the key file's own state meets
  `ShapeAsks` is not shown here.
- Values that meet `ShapeAsks` and `DataAsks`, at two small made-up places, each at one list of
  challenges: `sorts_one`, `sorts_came` (SortsMember.lean in this folder). Statements that conclude
  them, among others: from the same structure at other challenges (Sim/PlanCausal.lean in this
  folder); from the like on the state on entry (`shapeAsks_of_front`, `dataAsks_of_front`,
  ShapeAll.lean); from the test `coreB` and two equations on the codes (`sorts_of_coreB`,
  SortsMember.lean); under the library's head and `SaysAt`, at two trees (`asks_head`,
  AsksWhole.lean); each under further premises of its own: by reading the files that name them.
- What was known to fail there, "nothing is left untested" (the index masks' message is sampled and
  joins its group behind this test), is asked no more.
- Whether a row that this test takes in has a written-out factor is not shown here.
- hT is a hypothesis. It could be derived: the library's test on the plain data (`gpL`,
  FirstOk.lean, the clause "opens.n") compares the number of trees with the plan's, that is with the
  number of openings that the first switch's two rounds declare (`opensOf`). `ShapeAsks` gives that
  test only at a claim that the state after the batching passes.
- Some of the place's numbers rest on a print of a run of Lean's evaluator: which, and what they are
  compared with, is said in the limits of Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean.
- Of the twenty-two clauses the two negative tests show four to be false: "oS" at two trees;
  "switchPubB", "switchPlanB" and "planFromOk" at `answers := 2`. The eighteen others have no
  negative test here. The three `#guard` lines are evaluations by Lean's evaluator, outside the
  kernel: they leave no theorem.
- "Accepts" is `Block.decide ... = .ok`.
- The limits of `accepts_of_plan` (PlanB.lean) and of `test_accepts_all` (WholeAll.lean) hold here
  too.
- Nothing is said on what is left untested, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlanB
import Johnson.Desc.K12.Law.PlaceKeyRangesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (Plain)
open H2K.Member (piKRFull codesKeyFull)

variable {W X : Type}

set_option maxRecDepth 100000 in
/-- **All clauses of the plan's half (`planL`) hold at `piKRFull`, `codesKeyFull` and one tree.**
By an evaluation in Lean's kernel. -/
theorem planB_KR : planB piKRFull codesKeyFull 1 = true := by decide +kernel

/-- **What is left of `accepts_of_plan` at `piKRFull` with the plan's half proved (`planB_KR`).**
If the plain data list one tree (hT) and `ShapeAsks`, `FormAsks` and `DataAsks` hold, then the
decision of the test's block accepts all that `testAll` shows. -/
theorem accepts_at_key_ranges (J : TestJob W X) (hJ : J.p = piKRFull) (w : W) (fr : Front X)
    (C : TestCoins) (D : ℕ → Fmt.Drawn) (Dp : Plain) (hT : Dp.ts.length = 1)
    (c : ℕ → ℕ → List UInt64) (R : PlainRows) (S : ShapeAsks J w fr C D codesKeyFull Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp c R) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' :=
  accepts_of_plan J w fr C D codesKeyFull Dp c R (by rw [hJ, hT]; exact planB_KR) S F Dt

-- The same by Lean's evaluator: no clause is false, and there are twenty-two. Then two negative
-- tests: at two trees the clause "oS" is false and no other; at `answers := 2` three are false.
#guard planNo piKRFull codesKeyFull 1 == [] && (planL piKRFull codesKeyFull 1).length == 22
#guard planNo piKRFull codesKeyFull 2 == ["oS"]
#guard planNo { piKRFull with answers := 2 } codesKeyFull 1 ==
  ["switchPubB", "switchPlanB", "planFromOk"]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.planB_KR
#print axioms ProofFile.Honest.K12.accepts_at_key_ranges

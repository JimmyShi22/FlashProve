-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanTests.lean: each of the nine proximity tests of a proof file, a key file and an
entry file AS ONE OBJECT (`TestAt`, Johnson/Bridge/TestsAtWritten.lean) THAT IS A FUNCTION OF THE
PLANNER's RECORDS AND OF A RULE FOR THE RADII; and one test on the records whose yes gives, at every
one of the nine, that every fold, every code switch and the base case are taken off and every error
count is at most 2^-128 of its round's written verifier messages; and, of the fold alone, at the
groups of the proof file's links. No numeral of a plan is written here.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions with code, and statements that follow from Johnson/Bridge/TestsAtWritten.lean and
Johnson/Bridge/BrOf.lean.

Main names:
  `TestAt.of folds last work`: a test of stages with radii; the brackets by `brOf`.
  `testB`, `testB_paid`: `TestAt.ok` of it; a yes gives `TestAt.Paid`.
  `Rad`: a rule for the radii: of a setting, a group and its number of draws. `Rad.planner`: the
    function `radiusOf`. `Rad.ofStage r`: any function r of the stage alone.
  `stagesBy ρ σ st`: a planner's list of stages, each with its one radius by the rule.
  `testBy ρ σ st work`: the test of a planner's list of stages: each stage has ONE radius, in its
    fold, in the code switch that leaves it and in the one that enters it.
  `nineTests Z`: the nine lists of stages with their settings, in the order of the rounds «BASE»:
    the proof file's last test behind the links, folded row, Omega, own test; the key file's proof
    of the ranges, folded row, Omega, own test; the entry file's test.
  `planTestsBy ρ M`: the nine tests, each with the bits of work of the round «BASE» of its number.
  `linkFoldsBy ρ z`: the groups of the proof file's links as they are closed, at the rule's radii.
  `planTestsB ρ M`: THE TEST: `wholeB` (Johnson/Bridge/PlanStages.lean); nine tests are made;
    `TestAt.ok` at each; `foldsB` at the links' groups.
  `planTestsB_nine`, `planTestsB_tests`, `planTestsB_links`: what its yes gives: the tests made
    are nine; each is paid; each link's group is paid. No hypothesis on codes.
  `linkFoldsBy_planner`: at the planner's radii the links' groups are `linkFolds`.

Limits: THE RADII ARE WHATEVER THE RULE SAYS: no statement here ties a rule to a protocol. A test's
code switches are given the bits of work of its round «BASE»: that the plan's rounds of the code
switches have that work is not asked here. Of the 128 bits of the second round of a code switch and
of a base case, the bits of work are proof of work (the limits of Johnson/Bridge/CsPriced.lean and
Johnson/Bridge/BasePriced.lean). WHICH ROUND «BASE» BELONGS TO WHICH TEST IS BY ORDER ALONE. That
the records are those of a file's public files is asked where they are made. That the rounds of a
plan are the rounds of these stages, and that a verifier's description runs these stages, is not
said here. `stageOf` does not read a group's number of slots. The batching in front of a test, every
round «SEND seed» outside a test's code switches (those in front of the links' rounds «LOC» among
them), the rounds that draw positions alone («LOC») and the entry file's round «LINK» are not here.
The test has been EVALUATED at stored sets of public files, in a file not in this repository; no
theorem says that it says yes at any plan. No sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.PlanStages
import Johnson.Bridge.TestsAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Plan Johnson.Top.H

/-- A test of stages with radii, and the bits of work of its last round; the brackets by `brOf`. -/
def TestAt.of (folds : List (Sg × ℕ)) (last : Sg × ℕ) (work : ℕ) : TestAt :=
  ⟨folds.map fun p => FoldedPlace.of p.1 p.2, LastPlace.of last.1 last.2 work⟩

/-- All tests of all places of such a test. -/
def testB (folds : List (Sg × ℕ)) (last : Sg × ℕ) (work : ℕ) : Bool :=
  (TestAt.of folds last work).ok

/-- **A yes: every block of the test is taken off and every count is paid.** -/
theorem testB_paid {folds : List (Sg × ℕ)} {last : Sg × ℕ} {work : ℕ}
    (h : testB folds last work = true) : (TestAt.of folds last work).Paid := TestAt.paid h

/-- A rule for the radii: of a setting, a group and its number of draws. -/
abbrev Rad : Type := Setting → GroupSize → ℕ → ℕ

/-- The planner's radius. -/
def Rad.planner : Rad := fun σ g _ => radiusOf σ g

/-- A function of the stage alone. -/
def Rad.ofStage (r : Sg → ℕ) : Rad := fun _ g t => r (stageOf g t)

/-- A planner's stages, each with its one radius. -/
def stagesBy (ρ : Rad) (σ : Setting) (st : List StageSize) : List (Sg × ℕ) :=
  st.map fun y => (stageOf y.g y.t, ρ σ y.g y.t)

/-- The test of a planner's list of stages; none where the list is empty. -/
def testBy (ρ : Rad) (σ : Setting) (st : List StageSize) (work : ℕ) : List TestAt :=
  (stagesBy ρ σ st).getLast?.toList.map fun l => TestAt.of (stagesBy ρ σ st).dropLast l work

/-- The nine lists of stages, with their settings, in the order of the rounds «BASE». -/
def nineTests (Z : Params.Sized) : List (Setting × List StageSize) :=
  (proofTests Z).map (fun st => (Z.proof.set, st)) ++
    (keyTests Z).map (fun st => (Z.key.set, st)) ++ [(Z.set, Z.link.linked.stages)]

/-- **The nine tests**, each with the bits of work of the round «BASE» of its number. -/
def planTestsBy (ρ : Rad) (M : Configured) : List TestAt :=
  ((nineTests M.sized).zipWith (fun x w => testBy ρ x.1 x.2 w) (baseWorks M)).flatten

/-- The groups of a proof file's links, as they are closed, at the rule's radii. -/
def linkFoldsBy (ρ : Rad) (z : ProofSized) : List (Sg × ℕ) :=
  ((framesFrom z 0 (reqGroups z.request).toList z.request.link [] z.link.group).filter
    fun n => n.link.isSome).map fun n => (stageOf n.closed z.link.t, ρ z.set n.closed z.link.t)

/-- **The test on the planner's records, at a rule for the radii.** -/
def planTestsB (ρ : Rad) (M : Configured) : Bool :=
  wholeB M && Nat.beq (planTestsBy ρ M).length (nineTests M.sized).length &&
    ((planTestsBy ρ M).all fun T => T.ok) && foldsB (linkFoldsBy ρ M.sized.proof)

/-- The list of the nine has nine members. -/
theorem nineTests_length (Z : Params.Sized) : (nineTests Z).length = 9 := rfl

/-- **A yes of the test: the tests made are nine.** -/
theorem planTestsB_nine {ρ : Rad} {M : Configured} (h : planTestsB ρ M = true) :
    (planTestsBy ρ M).length = 9 :=
  (Nat.eq_of_beq_eq_true (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1
    (Bool.and_eq_true_iff.1 h).1).1).2).trans (nineTests_length M.sized)

/-- **A yes of the test: each of the nine tests is paid**: every fold, every code switch, the base
case; each stage at one radius. No hypothesis on codes. -/
theorem planTestsB_tests {ρ : Rad} {M : Configured} (h : planTestsB ρ M = true) :
    ∀ T ∈ planTestsBy ρ M, T.Paid := fun T hT =>
  TestAt.paid (List.all_eq_true.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).2 T hT)

/-- **A yes of the test: every link's group is paid.** No hypothesis on codes. -/
theorem planTestsB_links {ρ : Rad} {M : Configured} (h : planTestsB ρ M = true) :
    ∀ p ∈ linkFoldsBy ρ M.sized.proof, (FoldedPlace.of p.1 p.2).Paid :=
  foldsB_paid (Bool.and_eq_true_iff.1 h).2

/-- At the planner's radii the links' groups are those of Johnson/Bridge/PlanStages.lean. -/
theorem linkFoldsBy_planner (z : ProofSized) : linkFoldsBy Rad.planner z = linkFolds z := rfl

end Johnson.Bridge

#print axioms Johnson.Bridge.testB_paid
#print axioms Johnson.Bridge.planTestsB_nine
#print axioms Johnson.Bridge.planTestsB_tests
#print axioms Johnson.Bridge.planTestsB_links
